//! Integrity protection for SEP-2322 `requestState`.
//!
//! In the multi round-trip request (MRTR) flow, a server places an opaque
//! `requestState` string in an [`InputRequiredResult`](super::InputRequiredResult)
//! and the client echoes it back verbatim on retry. From the server's point of
//! view the echoed value is **untrusted, attacker-controlled input**: a client
//! can send back anything it likes. Per SEP-2322, a server that lets
//! `requestState` influence authorization, resource access, or business logic
//! MUST protect its integrity and reject values that fail verification.
//!
//! [`RequestStateCodec`] provides an opt-in way to do this. It seals a payload
//! into an opaque string with an HMAC-SHA256 tag and opens it again, rejecting
//! any value that was forged or tampered with.
//!
//! To follow the spec's replay-prevention guidance without hand-rolling the
//! checks, the codec supports two bindings via [`SealOptions`]:
//!
//! * **Associated data** — arbitrary context (e.g. the authenticated principal
//!   plus a digest of the originating request) that is mixed into the tag but
//!   not stored in the token. [`open_with`](RequestStateCodec::open_with) only
//!   succeeds when the caller supplies the same context, so a value cannot be
//!   replayed by a different principal or against a different request. This is
//!   *fail-closed*: forgetting to pass the context makes verification fail.
//! * **TTL** — a relative expiry stamped into the token; opening a value past
//!   its expiry fails with [`RequestStateError::Expired`].
//!
//! Single-use/nonce enforcement (for one-time redemptions) still has to be done
//! server-side, as the spec notes.
//!
//! This helper is only about *integrity*, not *confidentiality*: the sealed
//! payload is signed, not encrypted, so it is base64url-readable by anyone. Do
//! not put secrets in it.
//!
//! Using the codec is entirely optional. A server that keeps its state
//! server-side, or that does not trust `requestState` for anything security
//! sensitive, can keep building the string by hand via
//! [`InputRequiredResult::from_request_state`](super::InputRequiredResult::from_request_state).
//!
//! # Examples
//!
//! ```
//! use rmcp::model::{RequestStateCodec, SealOptions};
//! # fn main() -> Result<(), rmcp::model::RequestStateError> {
//!
//! // Derive the key from a per-process secret; keep it out of client reach.
//! let codec = RequestStateCodec::try_new(b"a-32-byte-or-longer-secret-key!!!")?;
//!
//! // Bind the state to the caller and the originating request.
//! let context = b"user:alice|tools/call:weather";
//! let sealed = codec.seal_with(
//!     b"step=2",
//!     &SealOptions::new().associated_data(context),
//! );
//!
//! // On retry the client echoes `sealed` back untouched; the server re-derives
//! // the same context and opens it.
//! let opened = codec.open_with(&sealed, context)?;
//! assert_eq!(opened, b"step=2");
//!
//! // A different principal (different context) is rejected.
//! assert!(codec.open_with(&sealed, b"user:bob|tools/call:weather").is_err());
//! # Ok(())
//! # }
//! ```

use std::{
    collections::{HashMap, hash_map::Entry},
    time::Duration,
};

use serde::{Serialize, de::DeserializeOwned};
use thiserror::Error;
use zeroize::Zeroizing;

use super::request_state_wire::{self as wire, prim};

/// [`wire::VERSION_V1`] as a `&str`, for building the token string.
const VERSION_V1: &str = "rs1";

/// [`wire::VERSION_V2`] as a `&str`, for building the token string.
const VERSION_V2: &str = "rs2";

/// Maximum unpadded base64url length for [`wire::MAX_KID_LEN`] bytes.
const MAX_ENCODED_KID_LEN: usize = wire::MAX_ENCODED_KID_LEN;

const KID_EMPTY_MSG: &str = "key id must not be empty";

const KID_TOO_LONG_MSG: &str = "key id exceeds 255 UTF-8 bytes";

/// Errors returned when constructing or configuring a
/// [`RequestStateCodec`], or when processing a sealed value.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum RequestStateError {
    /// The signing key is shorter than [`RequestStateCodec::MIN_KEY_LENGTH`].
    #[error(
        "request state signing key is too short: expected at least {minimum} bytes, got {actual}"
    )]
    KeyTooShort { minimum: usize, actual: usize },

    /// The value is not a well-formed sealed request state (wrong prefix or
    /// missing sections).
    #[error("request state is malformed or uses an unsupported format")]
    MalformedFormat,

    /// A section of the value was not valid base64url.
    #[error("request state is not valid base64url")]
    InvalidEncoding,

    /// The HMAC tag did not match; the value was forged, tampered with, or
    /// opened with the wrong associated data.
    #[error("request state failed integrity verification")]
    IntegrityCheckFailed,

    /// The value carried a TTL that has already elapsed.
    #[error("request state has expired")]
    Expired,

    /// The token names (or, for rs1, requires) a key this codec does not hold.
    #[error("request state was sealed with an unknown key")]
    UnknownKeyId,

    /// The decoded rs2 key id was empty, too long, or not valid UTF-8.
    #[error("request state contains an invalid key identifier")]
    InvalidKeyId,

    /// An invalid keyring configuration; the message is diagnostic only.
    #[error("invalid keyring configuration: {0}")]
    InvalidKeyring(&'static str),

    /// The sealed payload could not be serialized to JSON.
    #[error("failed to serialize request state payload: {0}")]
    Serialization(#[source] serde_json::Error),

    /// The opened payload could not be deserialized from JSON.
    #[error("failed to deserialize request state payload: {0}")]
    Deserialization(#[source] serde_json::Error),
}

/// Options controlling how a value is sealed by [`RequestStateCodec`].
///
/// Defaults to no associated data and no expiry, which is equivalent to the
/// bare [`seal`](RequestStateCodec::seal) / [`open`](RequestStateCodec::open)
/// methods.
#[derive(Clone, Copy, Debug, Default)]
pub struct SealOptions<'a> {
    associated_data: &'a [u8],
    ttl: Option<Duration>,
}

impl<'a> SealOptions<'a> {
    /// Creates empty options (no associated data, no expiry).
    pub fn new() -> Self {
        Self::default()
    }

    /// Binds the sealed value to `associated_data`. The same bytes must be
    /// supplied to [`open_with`](RequestStateCodec::open_with); the data is
    /// authenticated but not stored in the token.
    ///
    /// Use this to bind the state to the authenticated principal and/or the
    /// originating request (e.g. method name plus a digest of its parameters).
    pub fn associated_data(mut self, associated_data: &'a [u8]) -> Self {
        self.associated_data = associated_data;
        self
    }

    /// Sets a relative time-to-live after which opening the value fails with
    /// [`RequestStateError::Expired`].
    pub fn ttl(mut self, ttl: Duration) -> Self {
        self.ttl = Some(ttl);
        self
    }
}

/// A keyed codec for integrity-protected SEP-2322 `requestState` values.
///
/// [`new`](Self::new) preserves `rs1`; [`new_with_keyring`](Self::new_with_keyring)
/// emits `rs2`.
/// Use [`with_rs1_signing`](Self::with_rs1_signing) and
/// [`with_rs1_fallback`](Self::with_rs1_fallback) for rolling migrations.
///
/// Use [`try_new`](Self::try_new) and
/// [`new_with_keyring`](Self::new_with_keyring) to require at least
/// [`MIN_KEY_LENGTH`](Self::MIN_KEY_LENGTH) bytes of high-entropy key material.
/// Configure the same keys on every replica. Stored key material is zeroized
/// when the codec is dropped.
///
/// Values are authenticated, not encrypted; key ids and payloads remain
/// readable. Retain old keys until every value they signed has expired.
///
/// # Key rotation
///
/// Rotate in stages so every replica can open states emitted by its peers:
///
/// ```
/// # use rmcp::model::{RequestStateCodec, RequestStateError};
/// # fn main() -> Result<(), RequestStateError> {
/// let old_key = b"old-request-state-key-at-least-32b".as_slice();
/// let new_key = b"new-request-state-key-at-least-32b".as_slice();
/// let keys = [("old", old_key), ("new", new_key)];
///
/// // 1. Deploy both keys, but continue emitting rs1 with the old key.
/// let transitional = RequestStateCodec::new_with_keyring("new", keys)?
///     .with_rs1_signing("old")?;
///
/// // 2. Emit rs2 with the new key, while accepting in-flight rs1 values.
/// let promoted = RequestStateCodec::new_with_keyring("new", keys)?
///     .with_rs1_fallback("old")?;
///
/// let old_state = transitional.seal(b"old state");
/// assert_eq!(promoted.open(&old_state)?, b"old state");
/// let new_state = promoted.seal(b"new state");
/// assert_eq!(transitional.open(&new_state)?, b"new state");
///
/// // 3. After old values expire, remove the old key.
/// let retired = RequestStateCodec::new_with_keyring("new", [("new", new_key)])?;
/// assert_eq!(retired.open(&new_state)?, b"new state");
/// # Ok(())
/// # }
/// ```
#[derive(Clone)]
pub struct RequestStateCodec {
    keys: Keys,
}

#[derive(Clone)]
enum Keys {
    Single(Zeroizing<Vec<u8>>),
    Ring {
        keys: HashMap<String, Zeroizing<Vec<u8>>>,
        seal_mode: SealMode,
        rs1_fallbacks: Vec<String>,
    },
}

#[derive(Clone, Debug)]
enum SealMode {
    Rs1 { key_id: String },
    Rs2 { key_id: String },
}

impl std::fmt::Debug for RequestStateCodec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Never leak signing or verification keys through Debug output.
        match &self.keys {
            Keys::Single(_) => f
                .debug_struct("RequestStateCodec")
                .field("mode", &"single")
                .field("key", &"<redacted>")
                .finish(),
            Keys::Ring {
                keys,
                seal_mode,
                rs1_fallbacks,
            } => f
                .debug_struct("RequestStateCodec")
                .field("mode", &"ring")
                .field("key_count", &keys.len())
                .field("keys", &"<redacted>")
                .field("seal_mode", seal_mode)
                .field("rs1_fallbacks", rs1_fallbacks)
                .finish(),
        }
    }
}

impl RequestStateCodec {
    /// Minimum accepted signing-key length in bytes.
    pub const MIN_KEY_LENGTH: usize = wire::MIN_KEY_LENGTH;

    /// Creates a legacy single-key codec that seals and opens `rs1` values
    /// without validating the signing-key length.
    #[deprecated(
        since = "3.1.4",
        note = "use RequestStateCodec::try_new to enforce the minimum signing-key length"
    )]
    pub fn new(key: impl Into<Vec<u8>>) -> Self {
        Self::new_unchecked(key)
    }

    /// Creates a codec without validating the signing-key length.
    ///
    /// Prefer [`try_new`](Self::try_new) unless the key length has already been
    /// validated.
    pub fn new_unchecked(key: impl Into<Vec<u8>>) -> Self {
        Self {
            keys: Keys::Single(Zeroizing::new(key.into())),
        }
    }

    /// Creates a legacy single-key codec after validating its signing-key length.
    ///
    /// # Errors
    ///
    /// Returns [`RequestStateError::KeyTooShort`] when `key` contains fewer
    /// than [`MIN_KEY_LENGTH`](Self::MIN_KEY_LENGTH) bytes.
    pub fn try_new(key: impl Into<Vec<u8>>) -> Result<Self, RequestStateError> {
        let key = Zeroizing::new(key.into());
        Self::validate_key_length(&key)?;
        Ok(Self {
            keys: Keys::Single(key),
        })
    }

    /// Creates a keyring codec that seals `rs2` with `active_kid`.
    ///
    /// All configured keys can open matching `rs2` values. Legacy `rs1` values
    /// require [`with_rs1_fallback`](Self::with_rs1_fallback) or
    /// [`with_rs1_signing`](Self::with_rs1_signing).
    /// Key ids are case-sensitive UTF-8 strings of 1 to 255 bytes.
    ///
    /// # Errors
    ///
    /// Returns [`RequestStateError::KeyTooShort`] if a configured key contains
    /// fewer than [`MIN_KEY_LENGTH`](Self::MIN_KEY_LENGTH) bytes. Returns
    /// [`RequestStateError::InvalidKeyring`] if the keyring is empty, contains
    /// duplicate or invalid key ids, or does not contain `active_kid`.
    pub fn new_with_keyring<K, V>(
        active_kid: impl Into<String>,
        keys: impl IntoIterator<Item = (K, V)>,
    ) -> Result<Self, RequestStateError>
    where
        K: Into<String>,
        V: Into<Vec<u8>>,
    {
        let mut ring = HashMap::new();
        for (kid, key) in keys {
            let kid = kid.into();
            let key = Zeroizing::new(key.into());
            Self::validate_config_kid(&kid)?;
            Self::validate_key_length(&key)?;
            match ring.entry(kid) {
                Entry::Vacant(entry) => {
                    entry.insert(key);
                }
                Entry::Occupied(_) => {
                    return Err(RequestStateError::InvalidKeyring("duplicate key id"));
                }
            }
        }

        if ring.is_empty() {
            return Err(RequestStateError::InvalidKeyring(
                "keyring must contain at least one key",
            ));
        }

        let active_kid = active_kid.into();
        Self::validate_config_kid(&active_kid)?;
        if !ring.contains_key(&active_kid) {
            return Err(RequestStateError::InvalidKeyring(
                "active key id is not present in the keyring",
            ));
        }

        Ok(Self {
            keys: Keys::Ring {
                keys: ring,
                seal_mode: SealMode::Rs2 { key_id: active_kid },
                rs1_fallbacks: Vec::new(),
            },
        })
    }

    /// Uses `kid` to sign legacy `rs1` values during a rolling migration.
    /// The codec accepts its own `rs1` output and configured `rs2` values.
    ///
    /// # Errors
    ///
    /// Returns [`RequestStateError::InvalidKeyring`] when called on a single-key
    /// codec, or if the keyring does not contain `kid`.
    pub fn with_rs1_signing(mut self, kid: impl AsRef<str>) -> Result<Self, RequestStateError> {
        let kid = kid.as_ref();
        match &mut self.keys {
            Keys::Single(_) => Err(RequestStateError::InvalidKeyring(
                "rs1 transitional signing requires a keyring",
            )),
            Keys::Ring {
                keys,
                seal_mode,
                rs1_fallbacks,
            } => {
                if !keys.contains_key(kid) {
                    return Err(RequestStateError::InvalidKeyring(
                        "rs1 signing key id is not present in the keyring",
                    ));
                }

                let kid = kid.to_owned();
                *seal_mode = SealMode::Rs1 {
                    key_id: kid.clone(),
                };
                if !rs1_fallbacks.iter().any(|existing| existing == &kid) {
                    rs1_fallbacks.push(kid);
                }
                Ok(self)
            }
        }
    }

    /// Accepts legacy `rs1` values signed with `kid`.
    /// Adding the same id more than once has no effect; remove fallbacks after
    /// old values have drained.
    ///
    /// # Errors
    ///
    /// Returns [`RequestStateError::InvalidKeyring`] when called on a single-key
    /// codec, or if the keyring does not contain `kid`.
    pub fn with_rs1_fallback(mut self, kid: impl AsRef<str>) -> Result<Self, RequestStateError> {
        let kid = kid.as_ref();
        match &mut self.keys {
            Keys::Single(_) => Err(RequestStateError::InvalidKeyring(
                "rs1 fallbacks require a keyring",
            )),
            Keys::Ring {
                keys,
                rs1_fallbacks,
                ..
            } => {
                if !keys.contains_key(kid) {
                    return Err(RequestStateError::InvalidKeyring(
                        "rs1 fallback key id is not present in the keyring",
                    ));
                }
                if !rs1_fallbacks.iter().any(|existing| existing == kid) {
                    rs1_fallbacks.push(kid.to_owned());
                }
                Ok(self)
            }
        }
    }

    /// Seals raw bytes into an opaque, integrity-protected string suitable for
    /// use as `requestState`.
    pub fn seal(&self, payload: &[u8]) -> String {
        self.seal_with(payload, &SealOptions::default())
    }

    /// Seals raw bytes with [`SealOptions`] (associated data and/or TTL).
    pub fn seal_with(&self, payload: &[u8], options: &SealOptions<'_>) -> String {
        self.seal_at(payload, options, Self::now_ms())
    }

    /// Seals a serializable value by encoding it as JSON before sealing.
    ///
    /// # Errors
    ///
    /// Returns [`RequestStateError::Serialization`] if `value` cannot be encoded
    /// as JSON.
    pub fn seal_json<T: Serialize>(&self, value: &T) -> Result<String, RequestStateError> {
        self.seal_json_with(value, &SealOptions::default())
    }

    /// Seals a serializable value with [`SealOptions`].
    ///
    /// # Errors
    ///
    /// Returns [`RequestStateError::Serialization`] if `value` cannot be encoded
    /// as JSON.
    pub fn seal_json_with<T: Serialize>(
        &self,
        value: &T,
        options: &SealOptions<'_>,
    ) -> Result<String, RequestStateError> {
        let payload = serde_json::to_vec(value).map_err(RequestStateError::Serialization)?;
        Ok(self.seal_with(&payload, options))
    }

    /// Opens a sealed value that was sealed without associated data, verifying
    /// its integrity and expiry and returning the original bytes.
    ///
    /// # Errors
    ///
    /// See [`open_with`](Self::open_with).
    pub fn open(&self, sealed: &str) -> Result<Vec<u8>, RequestStateError> {
        self.open_with(sealed, &[])
    }

    /// Opens a sealed value, verifying its integrity against `associated_data`
    /// and checking its expiry.
    ///
    /// `associated_data` must match the bytes passed to
    /// [`SealOptions::associated_data`] when the value was sealed (use `&[]` for
    /// values sealed without it).
    ///
    /// # Errors
    ///
    /// Returns a [`RequestStateError`] if the value is malformed, cannot be
    /// verified, names an unavailable key, or has expired.
    ///
    /// Applications MUST map all token-opening failures to a single
    /// client-facing error and reserve the detailed variants for internal
    /// diagnostics.
    pub fn open_with(
        &self,
        sealed: &str,
        associated_data: &[u8],
    ) -> Result<Vec<u8>, RequestStateError> {
        self.open_at(sealed, associated_data, Self::now_ms())
    }

    /// Opens a sealed value (no associated data) and deserializes its JSON
    /// payload.
    ///
    /// # Errors
    ///
    /// See [`open_json_with`](Self::open_json_with).
    pub fn open_json<T: DeserializeOwned>(&self, sealed: &str) -> Result<T, RequestStateError> {
        self.open_json_with(sealed, &[])
    }

    /// Opens a sealed value against `associated_data` and deserializes its JSON
    /// payload.
    ///
    /// # Errors
    ///
    /// Returns the same integrity, expiry, and format errors as
    /// [`open_with`](Self::open_with), plus [`RequestStateError::Deserialization`]
    /// if the payload is not valid JSON for `T`.
    pub fn open_json_with<T: DeserializeOwned>(
        &self,
        sealed: &str,
        associated_data: &[u8],
    ) -> Result<T, RequestStateError> {
        let payload = self.open_with(sealed, associated_data)?;
        serde_json::from_slice(&payload).map_err(RequestStateError::Deserialization)
    }

    fn seal_at(&self, payload: &[u8], options: &SealOptions<'_>, now_ms: i64) -> String {
        let expiry = match options.ttl {
            Some(ttl) => now_ms.saturating_add(ttl.as_millis().min(i64::MAX as u128) as i64),
            None => 0,
        };

        // body = big-endian expiry (0 = none) followed by the caller payload.
        let body = wire::frame(expiry, payload);

        match &self.keys {
            Keys::Single(key) => Self::seal_rs1(key, options.associated_data, &body),
            Keys::Ring {
                keys, seal_mode, ..
            } => match seal_mode {
                SealMode::Rs1 { key_id } => Self::seal_rs1(
                    keys.get(key_id).expect("validated rs1 signing key"),
                    options.associated_data,
                    &body,
                ),
                SealMode::Rs2 { key_id } => Self::seal_rs2(
                    key_id,
                    keys.get(key_id).expect("validated rs2 signing key"),
                    options.associated_data,
                    &body,
                ),
            },
        }
    }

    fn open_at(
        &self,
        sealed: &str,
        associated_data: &[u8],
        now_ms: i64,
    ) -> Result<Vec<u8>, RequestStateError> {
        match wire::version_of(sealed.as_bytes()) {
            Some(wire::Version::V1) => self.open_rs1_at(sealed, associated_data, now_ms),
            Some(wire::Version::V2) => self.open_rs2_at(sealed, associated_data, now_ms),
            None => Err(RequestStateError::MalformedFormat),
        }
    }

    fn seal_rs1(key: &[u8], associated_data: &[u8], body: &[u8]) -> String {
        let tag = prim::hmac_sha256(key, &wire::transcript_v1(associated_data, body));
        let mut out = String::with_capacity(
            VERSION_V1.len() + 2 + Self::b64_len(body.len()) + Self::b64_len(tag.len()),
        );
        out.push_str(VERSION_V1);
        out.push('.');
        prim::b64_encode_into(body, &mut out);
        out.push('.');
        prim::b64_encode_into(&tag, &mut out);
        out
    }

    fn seal_rs2(kid: &str, key: &[u8], associated_data: &[u8], body: &[u8]) -> String {
        let tag = prim::hmac_sha256(
            key,
            &wire::transcript_v2(kid.as_bytes(), associated_data, body),
        );
        let mut out = String::with_capacity(
            VERSION_V2.len()
                + 3
                + Self::b64_len(kid.len())
                + Self::b64_len(body.len())
                + Self::b64_len(tag.len()),
        );
        out.push_str(VERSION_V2);
        out.push('.');
        prim::b64_encode_into(kid.as_bytes(), &mut out);
        out.push('.');
        prim::b64_encode_into(body, &mut out);
        out.push('.');
        prim::b64_encode_into(&tag, &mut out);
        out
    }

    fn open_rs1_at(
        &self,
        sealed: &str,
        associated_data: &[u8],
        now_ms: i64,
    ) -> Result<Vec<u8>, RequestStateError> {
        let Some(parts) = wire::parse_rs1(sealed.as_bytes()) else {
            return Err(RequestStateError::MalformedFormat);
        };

        if let Keys::Ring { rs1_fallbacks, .. } = &self.keys
            && rs1_fallbacks.is_empty()
        {
            return Err(RequestStateError::UnknownKeyId);
        }

        let body = prim::b64_decode(parts.body).ok_or(RequestStateError::InvalidEncoding)?;
        let tag = prim::b64_decode(parts.tag).ok_or(RequestStateError::InvalidEncoding)?;

        // Authentication must not short-circuit based on tag bytes.
        let transcript = wire::transcript_v1(associated_data, &body);
        let verified = match &self.keys {
            Keys::Single(key) => prim::hmac_sha256_verify(key, &transcript, &tag),
            Keys::Ring {
                keys,
                rs1_fallbacks,
                ..
            } => Self::rs1_fallbacks_verify(keys, rs1_fallbacks, &transcript, &tag),
        };
        if !verified {
            return Err(RequestStateError::IntegrityCheckFailed);
        }

        Self::open_authenticated_body(body, now_ms)
    }

    /// Tries every fallback so timing does not identify the matching key.
    fn rs1_fallbacks_verify(
        keys: &HashMap<String, Zeroizing<Vec<u8>>>,
        rs1_fallbacks: &[String],
        transcript: &[u8],
        tag: &[u8],
    ) -> bool {
        let mut verified = false;
        for kid in rs1_fallbacks {
            let key = keys.get(kid).expect("validated rs1 fallback key");
            let is_match = prim::hmac_sha256_verify(key, transcript, tag);
            verified |= is_match;
        }
        verified
    }

    fn open_rs2_at(
        &self,
        sealed: &str,
        associated_data: &[u8],
        now_ms: i64,
    ) -> Result<Vec<u8>, RequestStateError> {
        let Some(parts) = wire::parse_rs2(sealed.as_bytes()) else {
            return Err(RequestStateError::MalformedFormat);
        };

        if parts.kid.len() > MAX_ENCODED_KID_LEN {
            return Err(RequestStateError::InvalidKeyId);
        }
        let kid = prim::b64_decode(parts.kid).ok_or(RequestStateError::InvalidEncoding)?;
        if wire::check_kid_len(kid.len()).is_err() {
            return Err(RequestStateError::InvalidKeyId);
        }
        let kid = String::from_utf8(kid).map_err(|_| RequestStateError::InvalidKeyId)?;

        let key = match &self.keys {
            Keys::Single(_) => return Err(RequestStateError::UnknownKeyId),
            Keys::Ring { keys, .. } => keys.get(&kid).ok_or(RequestStateError::UnknownKeyId)?,
        };

        let body = prim::b64_decode(parts.body).ok_or(RequestStateError::InvalidEncoding)?;
        let tag = prim::b64_decode(parts.tag).ok_or(RequestStateError::InvalidEncoding)?;

        // Authentication must not short-circuit based on tag bytes.
        let transcript = wire::transcript_v2(kid.as_bytes(), associated_data, &body);
        if !prim::hmac_sha256_verify(key, &transcript, &tag) {
            return Err(RequestStateError::IntegrityCheckFailed);
        }

        Self::open_authenticated_body(body, now_ms)
    }

    fn open_authenticated_body(body: Vec<u8>, now_ms: i64) -> Result<Vec<u8>, RequestStateError> {
        // The body is now authenticated, so its framing can be trusted.
        match wire::open_frame(&body, now_ms) {
            Ok(payload) => Ok(payload.to_vec()),
            Err(wire::FrameError::TooShort) => Err(RequestStateError::MalformedFormat),
            Err(wire::FrameError::Expired) => Err(RequestStateError::Expired),
        }
    }

    fn validate_key_length(key: &[u8]) -> Result<(), RequestStateError> {
        if !wire::key_length_ok(key.len()) {
            return Err(RequestStateError::KeyTooShort {
                minimum: Self::MIN_KEY_LENGTH,
                actual: key.len(),
            });
        }
        Ok(())
    }

    fn validate_config_kid(kid: &str) -> Result<(), RequestStateError> {
        match wire::check_kid_len(kid.len()) {
            Ok(()) => Ok(()),
            Err(wire::KidError::Empty) => Err(RequestStateError::InvalidKeyring(KID_EMPTY_MSG)),
            Err(wire::KidError::TooLong) => {
                Err(RequestStateError::InvalidKeyring(KID_TOO_LONG_MSG))
            }
        }
    }

    // Base64url without padding encodes at most three bytes as four characters.
    fn b64_len(len: usize) -> usize {
        wire::b64_len(len)
    }

    fn now_ms() -> i64 {
        chrono::Utc::now().timestamp_millis()
    }
}

#[cfg(test)]
mod tests {
    use base64::{Engine, engine::general_purpose::URL_SAFE_NO_PAD};
    use hmac::{Hmac, KeyInit, Mac};
    use sha2::Sha256;

    use super::{
        wire::{DOMAIN_V1, DOMAIN_V2, MAX_KID_LEN},
        *,
    };

    type HmacSha256 = Hmac<Sha256>;

    #[test]
    fn codec_constants_agree_with_wire() {
        // The codec keeps a few copies of wire values (const `&str` tags, a
        // const message); they must agree exactly with the single definition
        // in `request_state_wire`, and with the base-commit literals.
        assert_eq!(VERSION_V1.as_bytes(), wire::VERSION_V1);
        assert_eq!(VERSION_V2.as_bytes(), wire::VERSION_V2);
        assert_eq!(VERSION_V1, "rs1");
        assert_eq!(VERSION_V2, "rs2");
        assert_eq!(MAX_ENCODED_KID_LEN, wire::MAX_ENCODED_KID_LEN);
        assert_eq!(MAX_ENCODED_KID_LEN, wire::b64_len(MAX_KID_LEN));
        assert_eq!(MAX_ENCODED_KID_LEN, 340);
        assert_eq!(MAX_KID_LEN, 255);
        assert_eq!(
            KID_TOO_LONG_MSG,
            format!("key id exceeds {MAX_KID_LEN} UTF-8 bytes")
        );
        assert_eq!(KID_TOO_LONG_MSG, "key id exceeds 255 UTF-8 bytes");
        assert_eq!(KID_EMPTY_MSG, "key id must not be empty");
        assert_eq!(RequestStateCodec::MIN_KEY_LENGTH, wire::MIN_KEY_LENGTH);

        // `prim::hmac_sha256` returns `[u8; 32]`; that 32 is `wire::TAG_LEN`,
        // and sealed tokens carry tags of exactly that length.
        let tag: [u8; 32] = prim::hmac_sha256(b"key", b"msg");
        assert_eq!(tag.len(), wire::TAG_LEN);
        let single = RequestStateCodec::try_new([7_u8; 32]).unwrap();
        let ring = RequestStateCodec::new_with_keyring("k", [("k", [7_u8; 32])]).unwrap();
        for (token, tag_index) in [(single.seal(b"p"), 2), (ring.seal(b"p"), 3)] {
            let tag_b64 = token.split('.').nth(tag_index).unwrap();
            let tag = URL_SAFE_NO_PAD.decode(tag_b64).unwrap();
            assert_eq!(tag.len(), wire::TAG_LEN, "{token}");
        }
    }

    #[test]
    fn try_new_accepts_key_at_minimum_length() {
        let result = RequestStateCodec::try_new(vec![0; RequestStateCodec::MIN_KEY_LENGTH]);

        assert!(result.is_ok(), "unexpected result: {result:?}");
    }

    #[test]
    fn try_new_rejects_key_below_minimum_length() {
        let actual = RequestStateCodec::MIN_KEY_LENGTH - 1;
        let error = RequestStateCodec::try_new(vec![0; actual]).unwrap_err();

        assert!(
            matches!(
                &error,
                RequestStateError::KeyTooShort {
                    minimum: RequestStateCodec::MIN_KEY_LENGTH,
                    actual: error_actual,
                } if *error_actual == actual
            ),
            "unexpected error: {error}"
        );
    }

    #[test]
    #[allow(deprecated)]
    fn new_accepts_short_key_for_backward_compatibility() {
        let codec = RequestStateCodec::new(b"key".to_vec());

        assert_eq!(codec.open(&codec.seal(b"state")).unwrap(), b"state");
    }

    #[test]
    fn seal_open_roundtrips_bytes() {
        let codec =
            RequestStateCodec::try_new(b"test-key-test-key-test-key-32byte".to_vec()).unwrap();
        let sealed = codec.seal(b"hello world");
        assert!(sealed.starts_with("rs1."));
        assert_eq!(codec.open(&sealed).unwrap(), b"hello world");
    }

    #[test]
    fn seal_open_roundtrips_json() {
        #[derive(serde::Serialize, serde::Deserialize, PartialEq, Debug)]
        struct State {
            tool: String,
            round: u32,
        }
        let codec =
            RequestStateCodec::try_new(b"another-strong-signing-key-here!!".to_vec()).unwrap();
        let state = State {
            tool: "weather".into(),
            round: 3,
        };
        let sealed = codec.seal_json(&state).unwrap();
        let opened: State = codec.open_json(&sealed).unwrap();
        assert_eq!(opened, state);
    }

    #[test]
    fn empty_payload_roundtrips() {
        let codec =
            RequestStateCodec::try_new(b"empty-payload-test-signing-key!!".to_vec()).unwrap();
        let sealed = codec.seal(b"");
        assert_eq!(codec.open(&sealed).unwrap(), b"");
    }

    #[test]
    fn tampered_payload_is_rejected() {
        let codec =
            RequestStateCodec::try_new(b"signing-key-signing-key-signing!!".to_vec()).unwrap();
        let sealed = codec.seal(b"amount=100");

        // Replace the body section but keep the original tag.
        let mut parts: Vec<&str> = sealed.split('.').collect();
        let forged_body = URL_SAFE_NO_PAD.encode(b"amount=999");
        parts[1] = &forged_body;
        let forged = parts.join(".");

        assert!(matches!(
            codec.open(&forged),
            Err(RequestStateError::IntegrityCheckFailed)
        ));
    }

    #[test]
    fn different_key_is_rejected() {
        let signer =
            RequestStateCodec::try_new(b"the-real-signing-key-value-here!!".to_vec()).unwrap();
        let attacker =
            RequestStateCodec::try_new(b"a-totally-different-forged-key!!!".to_vec()).unwrap();
        let sealed = signer.seal(b"trusted");
        assert!(matches!(
            attacker.open(&sealed),
            Err(RequestStateError::IntegrityCheckFailed)
        ));
    }

    #[test]
    fn appended_bytes_are_rejected() {
        let codec =
            RequestStateCodec::try_new(b"key-key-key-key-key-key-key-key!!".to_vec()).unwrap();
        let mut sealed = codec.seal(b"state");
        sealed.push('x');
        assert!(codec.open(&sealed).is_err());
    }

    #[test]
    fn unsupported_version_is_malformed() {
        let codec =
            RequestStateCodec::try_new(b"wrong-version-test-signing-key!!".to_vec()).unwrap();
        let sealed = codec.seal(b"state");
        let bumped = sealed.replacen("rs1.", "rs3.", 1);
        assert!(matches!(
            codec.open(&bumped),
            Err(RequestStateError::MalformedFormat)
        ));
    }

    #[test]
    fn missing_sections_are_malformed() {
        let codec =
            RequestStateCodec::try_new(b"missing-sections-test-signing-key".to_vec()).unwrap();
        assert!(matches!(
            codec.open("rs1"),
            Err(RequestStateError::MalformedFormat)
        ));
        assert!(matches!(
            codec.open("rs1.onlybody"),
            Err(RequestStateError::MalformedFormat)
        ));
        assert!(matches!(
            codec.open("rs1.a.b.c"),
            Err(RequestStateError::MalformedFormat)
        ));
    }

    #[test]
    fn non_base64_sections_are_invalid_encoding() {
        let codec =
            RequestStateCodec::try_new(b"invalid-base64-test-signing-key!!".to_vec()).unwrap();
        assert!(matches!(
            codec.open("rs1.!!!!.!!!!"),
            Err(RequestStateError::InvalidEncoding)
        ));
    }

    #[test]
    fn debug_does_not_leak_key() {
        let codec =
            RequestStateCodec::try_new(b"super-secret-key-super-secret-key!!".to_vec()).unwrap();
        let rendered = format!("{codec:?}");
        assert!(!rendered.contains("super-secret-key"));
        assert!(rendered.contains("redacted"));
    }

    mod associated_data {
        use super::*;

        #[test]
        fn matching_context_opens() {
            let codec =
                RequestStateCodec::try_new(b"key-key-key-key-key-key-key-key!!".to_vec()).unwrap();
            let ctx = b"user:alice|tools/call:weather";
            let sealed = codec.seal_with(b"state", &SealOptions::new().associated_data(ctx));
            assert_eq!(codec.open_with(&sealed, ctx).unwrap(), b"state");
        }

        #[test]
        fn different_context_is_rejected() {
            let codec =
                RequestStateCodec::try_new(b"key-key-key-key-key-key-key-key!!".to_vec()).unwrap();
            let sealed =
                codec.seal_with(b"state", &SealOptions::new().associated_data(b"user:alice"));
            assert!(matches!(
                codec.open_with(&sealed, b"user:bob"),
                Err(RequestStateError::IntegrityCheckFailed)
            ));
        }

        #[test]
        fn missing_context_is_rejected() {
            let codec =
                RequestStateCodec::try_new(b"key-key-key-key-key-key-key-key!!".to_vec()).unwrap();
            let sealed =
                codec.seal_with(b"state", &SealOptions::new().associated_data(b"user:alice"));
            // Opening without the associated data must fail closed.
            assert!(matches!(
                codec.open(&sealed),
                Err(RequestStateError::IntegrityCheckFailed)
            ));
        }
    }

    mod ttl {
        use super::*;

        const KEY: &[u8] = b"ttl-signing-key-ttl-signing-key!!";

        #[test]
        fn within_ttl_opens() {
            let codec = RequestStateCodec::try_new(KEY.to_vec()).unwrap();
            let sealed = codec.seal_at(
                b"state",
                &SealOptions::new().ttl(Duration::from_secs(60)),
                1_000,
            );
            // 30s later, still valid.
            assert_eq!(codec.open_at(&sealed, &[], 31_000).unwrap(), b"state");
        }

        #[test]
        fn past_ttl_is_expired() {
            let codec = RequestStateCodec::try_new(KEY.to_vec()).unwrap();
            let sealed = codec.seal_at(
                b"state",
                &SealOptions::new().ttl(Duration::from_secs(60)),
                1_000,
            );
            // 61s later, expired.
            assert!(matches!(
                codec.open_at(&sealed, &[], 62_000),
                Err(RequestStateError::Expired)
            ));
        }

        #[test]
        fn no_ttl_never_expires() {
            let codec = RequestStateCodec::try_new(KEY.to_vec()).unwrap();
            let sealed = codec.seal_at(b"state", &SealOptions::new(), 1_000);
            assert_eq!(codec.open_at(&sealed, &[], i64::MAX).unwrap(), b"state");
        }

        #[test]
        fn ttl_and_associated_data_combine() {
            let codec = RequestStateCodec::try_new(KEY.to_vec()).unwrap();
            let ctx = b"user:alice";
            let sealed = codec.seal_at(
                b"state",
                &SealOptions::new()
                    .associated_data(ctx)
                    .ttl(Duration::from_secs(60)),
                1_000,
            );
            assert_eq!(codec.open_at(&sealed, ctx, 10_000).unwrap(), b"state");
            assert!(matches!(
                codec.open_at(&sealed, b"user:bob", 10_000),
                Err(RequestStateError::IntegrityCheckFailed)
            ));
            assert!(matches!(
                codec.open_at(&sealed, ctx, 99_000),
                Err(RequestStateError::Expired)
            ));
        }
    }

    mod key_rotation {
        use super::*;

        const KEY_A: &[u8] = b"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        const KEY_B: &[u8] = b"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
        const KEY_C: &[u8] = b"cccccccccccccccccccccccccccccccc";
        const KAT_KEY: &[u8] = b"0123456789abcdef0123456789abcdef";
        const KAT_KID: &str = "rotation-key-2026-08";
        const KAT_AD: &[u8] = b"user:alice|request:weather";
        const KAT_NOW_MS: i64 = 1_700_000_000_000;

        fn two_key_ring(active: &str) -> RequestStateCodec {
            RequestStateCodec::new_with_keyring(active, [("a", KEY_A), ("b", KEY_B)]).unwrap()
        }

        fn body(expiry: i64, payload: &[u8]) -> Vec<u8> {
            let mut body = expiry.to_be_bytes().to_vec();
            body.extend_from_slice(payload);
            body
        }

        fn replace_segment(token: &str, index: usize, replacement: &str) -> String {
            let mut parts: Vec<String> = token.split('.').map(str::to_owned).collect();
            parts[index] = replacement.to_owned();
            parts.join(".")
        }

        fn test_mac(
            key: &[u8],
            domain: &[u8],
            kid: Option<&[u8]>,
            associated_data: &[u8],
            body: &[u8],
        ) -> Vec<u8> {
            let mut mac = HmacSha256::new_from_slice(key).expect("HMAC accepts keys of any length");
            mac.update(domain);
            if let Some(kid) = kid {
                mac.update(&(kid.len() as u64).to_be_bytes());
                mac.update(kid);
            }
            mac.update(&(associated_data.len() as u64).to_be_bytes());
            mac.update(associated_data);
            mac.update(body);
            mac.finalize().into_bytes().to_vec()
        }

        fn raw_rs1(body: &[u8], tag: &[u8]) -> String {
            format!(
                "rs1.{}.{}",
                URL_SAFE_NO_PAD.encode(body),
                URL_SAFE_NO_PAD.encode(tag)
            )
        }

        fn raw_rs2(kid: &[u8], body: &[u8], tag: &[u8]) -> String {
            format!(
                "rs2.{}.{}.{}",
                URL_SAFE_NO_PAD.encode(kid),
                URL_SAFE_NO_PAD.encode(body),
                URL_SAFE_NO_PAD.encode(tag)
            )
        }

        #[test]
        fn rs1_known_answer_is_unchanged() {
            // Independently checked with Python stdlib HMAC and Ruby OpenSSL.
            let codec = RequestStateCodec::try_new(KAT_KEY).unwrap();
            let sealed = codec.seal_at(
                b"step=2",
                &SealOptions::new()
                    .associated_data(KAT_AD)
                    .ttl(Duration::from_secs(90)),
                KAT_NOW_MS,
            );
            assert_eq!(
                sealed,
                "rs1.AAABi8_mx5BzdGVwPTI.GQgS0X7mtSz8ZOy_kld2Zjuc4gAMGpBL74EghWI36IQ"
            );
        }

        #[test]
        fn rs2_known_answer_matches_wire_specification() {
            // Independently checked with Python stdlib HMAC and Ruby OpenSSL.
            let codec = RequestStateCodec::new_with_keyring(KAT_KID, [(KAT_KID, KAT_KEY)]).unwrap();
            let sealed = codec.seal_at(
                b"step=2",
                &SealOptions::new()
                    .associated_data(KAT_AD)
                    .ttl(Duration::from_secs(90)),
                KAT_NOW_MS,
            );
            assert_eq!(
                sealed,
                "rs2.cm90YXRpb24ta2V5LTIwMjYtMDg.AAABi8_mx5BzdGVwPTI.twv2acu7lKXqebyrmit-JrHHZm-BkKlBQEMMtL3lHk8"
            );
        }

        #[test]
        fn rs2_roundtrips_with_associated_data_and_ttl() {
            let codec = two_key_ring("a");
            let options = SealOptions::new()
                .associated_data(b"user:alice")
                .ttl(Duration::from_secs(60));

            let sealed = codec.seal_at(b"state", &options, 1_000);
            assert!(sealed.starts_with("rs2.YQ."));
            assert_eq!(
                codec.open_at(&sealed, b"user:alice", 30_000).unwrap(),
                b"state"
            );
            assert!(matches!(
                codec.open_at(&sealed, b"user:bob", 30_000),
                Err(RequestStateError::IntegrityCheckFailed)
            ));
            assert!(matches!(
                codec.open_at(&sealed, b"user:alice", 70_000),
                Err(RequestStateError::Expired)
            ));
        }

        #[test]
        fn rotation_keeps_previous_rs2_key_verifiable() {
            let signer_a = two_key_ring("a");
            let token_a = signer_a.seal(b"state-a");

            let signer_b = two_key_ring("b");
            assert_eq!(signer_b.open(&token_a).unwrap(), b"state-a");
            let token_b = signer_b.seal(b"state-b");
            assert!(token_b.starts_with("rs2.Yg."));
            assert_eq!(signer_b.open(&token_b).unwrap(), b"state-b");

            let without_a = RequestStateCodec::new_with_keyring("b", [("b", KEY_B)]).unwrap();
            assert!(matches!(
                without_a.open(&token_a),
                Err(RequestStateError::UnknownKeyId)
            ));
        }

        #[test]
        fn rolling_migration_is_bidirectionally_compatible() {
            let old = RequestStateCodec::try_new(KEY_A).unwrap();
            let transitional =
                RequestStateCodec::new_with_keyring("new", [("old", KEY_A), ("new", KEY_B)])
                    .unwrap()
                    .with_rs1_signing("old")
                    .unwrap();
            let promoted =
                RequestStateCodec::new_with_keyring("new", [("old", KEY_A), ("new", KEY_B)])
                    .unwrap()
                    .with_rs1_fallback("old")
                    .unwrap();
            let retired = RequestStateCodec::new_with_keyring("new", [("new", KEY_B)]).unwrap();

            let old_token = old.seal(b"old");
            assert_eq!(transitional.open(&old_token).unwrap(), b"old");

            let transitional_token = transitional.seal(b"transition");
            assert!(transitional_token.starts_with("rs1."));
            assert_eq!(old.open(&transitional_token).unwrap(), b"transition");
            assert_eq!(promoted.open(&transitional_token).unwrap(), b"transition");

            let promoted_token = promoted.seal(b"promoted");
            assert!(promoted_token.starts_with("rs2."));
            assert_eq!(transitional.open(&promoted_token).unwrap(), b"promoted");
            assert_eq!(retired.open(&promoted_token).unwrap(), b"promoted");
            assert!(matches!(
                retired.open(&old_token),
                Err(RequestStateError::UnknownKeyId)
            ));
        }

        #[test]
        fn multiple_legacy_fallbacks_are_supported() {
            let legacy_a = RequestStateCodec::try_new(KEY_A).unwrap().seal(b"a");
            let legacy_b = RequestStateCodec::try_new(KEY_B).unwrap().seal(b"b");
            let legacy_c = RequestStateCodec::try_new(KEY_C).unwrap().seal(b"c");
            let ring = RequestStateCodec::new_with_keyring(
                "new",
                [("a", KEY_A), ("b", KEY_B), ("new", KEY_C)],
            )
            .unwrap()
            .with_rs1_fallback("a")
            .unwrap()
            .with_rs1_fallback("b")
            .unwrap();

            assert_eq!(ring.open(&legacy_a).unwrap(), b"a");
            assert_eq!(ring.open(&legacy_b).unwrap(), b"b");
            assert!(matches!(
                ring.open(&legacy_c),
                Err(RequestStateError::IntegrityCheckFailed)
            ));
        }

        #[test]
        fn kid_is_authenticated_even_when_ids_share_key_bytes() {
            let codec =
                RequestStateCodec::new_with_keyring("a", [("a", KEY_A), ("b", KEY_A)]).unwrap();
            let sealed = codec.seal(b"state");
            let swapped = replace_segment(&sealed, 1, &URL_SAFE_NO_PAD.encode(b"b"));
            assert!(matches!(
                codec.open(&swapped),
                Err(RequestStateError::IntegrityCheckFailed)
            ));
        }

        #[test]
        fn independent_rs2_segment_tampering_is_rejected() {
            let codec = two_key_ring("a");
            let sealed = codec.seal(b"state");

            let swapped_kid = replace_segment(&sealed, 1, &URL_SAFE_NO_PAD.encode(b"b"));
            let tampered_body = replace_segment(&sealed, 2, &URL_SAFE_NO_PAD.encode(b"changed"));
            let tampered_tag = replace_segment(&sealed, 3, &URL_SAFE_NO_PAD.encode([0_u8; 32]));

            for tampered in [swapped_kid, tampered_body, tampered_tag] {
                assert!(matches!(
                    codec.open(&tampered),
                    Err(RequestStateError::IntegrityCheckFailed)
                ));
            }
        }

        #[test]
        fn version_domains_are_cryptographically_separate() {
            let token_body = body(0, b"state");

            let wrong_v2_tag = test_mac(KEY_A, DOMAIN_V1, Some(b"a"), b"", &token_body);
            let wrong_v2 = raw_rs2(b"a", &token_body, &wrong_v2_tag);
            assert!(matches!(
                two_key_ring("a").open(&wrong_v2),
                Err(RequestStateError::IntegrityCheckFailed)
            ));

            let wrong_v1_tag = test_mac(KEY_A, DOMAIN_V2, None, b"", &token_body);
            let wrong_v1 = raw_rs1(&token_body, &wrong_v1_tag);
            assert!(matches!(
                RequestStateCodec::try_new(KEY_A).unwrap().open(&wrong_v1),
                Err(RequestStateError::IntegrityCheckFailed)
            ));
        }

        #[test]
        fn constructor_invariants_are_enforced() {
            let empty =
                RequestStateCodec::new_with_keyring("a", std::iter::empty::<(&str, &[u8])>());
            assert!(matches!(empty, Err(RequestStateError::InvalidKeyring(_))));

            let duplicate = RequestStateCodec::new_with_keyring("a", [("a", KEY_A), ("a", KEY_B)]);
            assert!(matches!(
                duplicate,
                Err(RequestStateError::InvalidKeyring(_))
            ));

            let empty_kid = RequestStateCodec::new_with_keyring("", [("", KEY_A)]);
            assert!(matches!(
                empty_kid,
                Err(RequestStateError::InvalidKeyring(_))
            ));

            let oversized = "x".repeat(MAX_KID_LEN + 1);
            let oversized_kid =
                RequestStateCodec::new_with_keyring(oversized.clone(), [(oversized, KEY_A)]);
            assert!(matches!(
                oversized_kid,
                Err(RequestStateError::InvalidKeyring(_))
            ));

            let absent_active = RequestStateCodec::new_with_keyring("missing", [("a", KEY_A)]);
            assert!(matches!(
                absent_active,
                Err(RequestStateError::InvalidKeyring(_))
            ));

            let short_key = RequestStateCodec::new_with_keyring(
                "a",
                [("a", vec![0; RequestStateCodec::MIN_KEY_LENGTH - 1])],
            );
            assert!(matches!(
                short_key,
                Err(RequestStateError::KeyTooShort { .. })
            ));

            assert!(matches!(
                RequestStateCodec::try_new(KEY_A)
                    .unwrap()
                    .with_rs1_signing("a"),
                Err(RequestStateError::InvalidKeyring(_))
            ));
            assert!(matches!(
                two_key_ring("a").with_rs1_signing("missing"),
                Err(RequestStateError::InvalidKeyring(_))
            ));
            assert!(matches!(
                RequestStateCodec::try_new(KEY_A)
                    .unwrap()
                    .with_rs1_fallback("a"),
                Err(RequestStateError::InvalidKeyring(_))
            ));
            assert!(matches!(
                two_key_ring("a").with_rs1_fallback("missing"),
                Err(RequestStateError::InvalidKeyring(_))
            ));
        }

        #[test]
        fn maximum_length_kid_roundtrips_and_oversized_wire_kid_is_rejected() {
            let max_kid = "x".repeat(MAX_KID_LEN);
            let codec =
                RequestStateCodec::new_with_keyring(max_kid.clone(), [(max_kid, KEY_A)]).unwrap();
            let token = codec.seal(b"state");
            assert_eq!(codec.open(&token).unwrap(), b"state");

            let encoded_oversized = URL_SAFE_NO_PAD.encode("x".repeat(MAX_KID_LEN + 1));
            assert!(encoded_oversized.len() > MAX_ENCODED_KID_LEN);
            let oversized = format!("rs2.{encoded_oversized}.!!!!.!!!!");
            assert!(matches!(
                codec.open(&oversized),
                Err(RequestStateError::InvalidKeyId)
            ));

            let overlong_invalid_base64 =
                format!("rs2.{}.!!!!.!!!!", "!".repeat(MAX_ENCODED_KID_LEN + 1));
            assert!(matches!(
                codec.open(&overlong_invalid_base64),
                Err(RequestStateError::InvalidKeyId)
            ));
        }

        #[test]
        fn parser_rejects_invalid_tokens_and_unavailable_keys() {
            let codec = two_key_ring("a");
            for malformed in [
                "rs2",
                "rs2.YQ",
                "rs2.YQ.body",
                "rs2.YQ.body.tag.extra",
                "rs3.YQ.body.tag",
            ] {
                assert!(matches!(
                    codec.open(malformed),
                    Err(RequestStateError::MalformedFormat)
                ));
            }

            let valid_rs2 = codec.seal(b"state");
            assert!(matches!(
                codec.open(&replace_segment(&valid_rs2, 1, "!!!!")),
                Err(RequestStateError::InvalidEncoding)
            ));
            assert!(matches!(
                codec.open(&replace_segment(&valid_rs2, 1, "")),
                Err(RequestStateError::InvalidKeyId)
            ));
            let non_utf8 = URL_SAFE_NO_PAD.encode([0xff]);
            assert!(matches!(
                codec.open(&replace_segment(&valid_rs2, 1, &non_utf8)),
                Err(RequestStateError::InvalidKeyId)
            ));

            assert!(matches!(
                RequestStateCodec::try_new(KEY_A).unwrap().open(&valid_rs2),
                Err(RequestStateError::UnknownKeyId)
            ));

            let valid_rs1 = RequestStateCodec::try_new(KEY_A).unwrap().seal(b"state");
            assert!(matches!(
                codec.open(&valid_rs1),
                Err(RequestStateError::UnknownKeyId)
            ));
        }

        #[test]
        fn authenticated_short_body_is_malformed() {
            let short_body = b"short";
            let tag = prim::hmac_sha256(KEY_A, &wire::transcript_v2(b"a", b"", short_body));
            let token = raw_rs2(b"a", short_body, tag.as_slice());
            assert!(matches!(
                two_key_ring("a").open(&token),
                Err(RequestStateError::MalformedFormat)
            ));
        }

        #[test]
        fn serde_is_reached_only_after_integrity_verification() {
            let codec = two_key_ring("a");
            let invalid_json = codec.seal(b"{not-json");
            let opened: Result<serde_json::Value, _> = codec.open_json(&invalid_json);
            assert!(matches!(opened, Err(RequestStateError::Deserialization(_))));

            let valid_json = codec.seal(b"{}");
            let tampered_body = body(0, b"{not-json");
            let tampered = replace_segment(&valid_json, 2, &URL_SAFE_NO_PAD.encode(tampered_body));
            let opened: Result<serde_json::Value, _> = codec.open_json(&tampered);
            assert!(matches!(
                opened,
                Err(RequestStateError::IntegrityCheckFailed)
            ));
        }

        #[test]
        fn ring_debug_redacts_all_key_material() {
            let codec = two_key_ring("b").with_rs1_fallback("a").unwrap();
            let rendered = format!("{codec:?}");
            assert!(!rendered.contains(std::str::from_utf8(KEY_A).unwrap()));
            assert!(!rendered.contains(std::str::from_utf8(KEY_B).unwrap()));
            assert!(rendered.contains("redacted"));
        }

        #[test]
        fn mutated_tokens_do_not_panic() {
            let codec = two_key_ring("a").with_rs1_fallback("a").unwrap();
            let valid = [
                RequestStateCodec::try_new(KEY_A).unwrap().seal(b"state"),
                codec.seal(b"state"),
            ];
            let mut corpus = vec![
                String::new(),
                ".".to_owned(),
                "...".to_owned(),
                "rs1".to_owned(),
                "rs2".to_owned(),
                "💥".to_owned(),
                "rs2.💥...".to_owned(),
            ];

            for token in valid {
                for end in 0..=token.len() {
                    corpus.push(token[..end].to_owned());
                }
                for index in 0..token.len() {
                    let mut bytes = token.as_bytes().to_vec();
                    bytes[index] = b'!';
                    corpus.push(String::from_utf8(bytes).expect("token is ASCII"));
                }
            }

            for candidate in corpus {
                let _ = codec.open(&candidate);
                let _ = codec.open_with(&candidate, b"context");
            }
        }
    }

    /// Byte-identity regression for the `request_state_wire` refactor (plan
    /// step S04a). Every expected line below was produced by the codec as it
    /// was before the refactor (commit `b9cfcfe`, which still had `mac_v1`,
    /// `mac_v2` and `str::split`), with the same keys, inputs and clock, so the
    /// tests pin both the sealed tokens and the `open` outcomes byte for byte.
    mod byte_identity {
        use super::*;

        const NOW_MS: i64 = 1_700_000_000_000;
        const TTL_MS: i64 = 90_000;
        const K1: [u8; 32] = [7; 32];
        const K2: [u8; 40] = [9; 40];

        fn codecs() -> [(&'static str, RequestStateCodec); 3] {
            let single = RequestStateCodec::try_new(K1).unwrap();
            let ring_rs2 = RequestStateCodec::new_with_keyring(
                "kid-é",
                [("kid-é", K1.to_vec()), ("b", K2.to_vec())],
            )
            .unwrap();
            let ring_rs1 =
                RequestStateCodec::new_with_keyring("b", [("a", K1.to_vec()), ("b", K2.to_vec())])
                    .unwrap()
                    .with_rs1_signing("b")
                    .unwrap()
                    .with_rs1_fallback("a")
                    .unwrap();
            [
                ("single", single),
                ("ring_rs2", ring_rs2),
                ("ring_rs1", ring_rs1),
            ]
        }

        fn outcome(result: Result<Vec<u8>, RequestStateError>) -> String {
            match result {
                Ok(payload) => {
                    let hex: String = payload.iter().map(|b| format!("{b:02x}")).collect();
                    format!("Ok:{hex}")
                }
                Err(e) => format!("{e:?}"),
            }
        }

        fn segment(token: &str, index: usize, replacement: &str) -> String {
            let mut parts: Vec<&str> = token.split('.').collect();
            parts[index] = replacement;
            parts.join(".")
        }

        /// Run-3 token harness (pilot `zz_pilot_tokens.rs`) at a fixed clock:
        /// 9 tokens (no expiry), each followed by its 18 `open` outcomes.
        fn run3_matrix() -> Vec<String> {
            let codecs = codecs();
            let inputs: [(&[u8], &[u8]); 3] =
                [(b"", b""), (b"payload", b"ad"), (&[0, 255, 46], b"x.y")];
            let mut out = Vec::new();
            for (name, codec) in &codecs {
                for (payload, ad) in inputs {
                    let t = codec.seal_at(payload, &SealOptions::new().associated_data(ad), NOW_MS);
                    out.push(format!("{name} {payload:?} {ad:?} -> {t}"));
                    let candidates = [
                        t.clone(),
                        t.replacen('.', ".A", 1),
                        format!("{t}.x"),
                        t.replace("rs", "rx"),
                        String::new(),
                        "rs2.AAAA.AA.AA".to_owned(),
                    ];
                    let mut codes = Vec::new();
                    for cand in &candidates {
                        for (_, opener) in &codecs {
                            codes.push(outcome(opener.open_at(cand, ad, NOW_MS)));
                        }
                    }
                    out.push(codes.join(" "));
                }
            }
            out
        }

        /// One rs1 and one rs2 token with a TTL, and `open` outcomes covering
        /// every error variant the opening path can return.
        fn pinned_cases() -> Vec<String> {
            let [(_, single), (_, ring_rs2), (_, ring_rs1)] = codecs();
            let opts = SealOptions::new()
                .associated_data(b"ad")
                .ttl(Duration::from_millis(TTL_MS as u64));
            let rs1 = single.seal_at(b"payload", &opts, NOW_MS);
            let rs2 = ring_rs2.seal_at(b"payload", &opts, NOW_MS);
            let expiry = NOW_MS + TTL_MS;
            let kid_256 = URL_SAFE_NO_PAD.encode([b'k'; 256]);
            let kid_255 = URL_SAFE_NO_PAD.encode([b'k'; 255]);
            let kid_bad_utf8 = URL_SAFE_NO_PAD.encode([0xff_u8]);
            let kid_unknown = URL_SAFE_NO_PAD.encode("kid-x");
            let cases: Vec<(&str, &RequestStateCodec, String, &[u8], i64)> = vec![
                ("rs1 ok", &single, rs1.clone(), b"ad", NOW_MS),
                ("rs1 ok at expiry", &single, rs1.clone(), b"ad", expiry),
                ("rs1 expired", &single, rs1.clone(), b"ad", expiry + 1),
                ("rs1 wrong ad", &single, rs1.clone(), b"other", NOW_MS),
                (
                    "rs1 ring no fallbacks",
                    &ring_rs2,
                    rs1.clone(),
                    b"ad",
                    NOW_MS,
                ),
                (
                    "rs1 ring last fallback",
                    &ring_rs1,
                    rs1.clone(),
                    b"ad",
                    NOW_MS,
                ),
                (
                    "rs1 ring expired",
                    &ring_rs1,
                    rs1.clone(),
                    b"ad",
                    expiry + 1,
                ),
                (
                    "rs1 bad body",
                    &single,
                    segment(&rs1, 1, "!"),
                    b"ad",
                    NOW_MS,
                ),
                (
                    "rs1 padded tag",
                    &single,
                    segment(&rs1, 2, "AA=="),
                    b"ad",
                    NOW_MS,
                ),
                ("rs1 4 parts", &single, format!("{rs1}.x"), b"ad", NOW_MS),
                ("rs1 2 parts", &single, "rs1.x".to_owned(), b"ad", NOW_MS),
                ("rs3", &single, "rs3.AA.AA".to_owned(), b"ad", NOW_MS),
                ("rs2 ok", &ring_rs2, rs2.clone(), b"ad", NOW_MS),
                ("rs2 ok at expiry", &ring_rs2, rs2.clone(), b"ad", expiry),
                ("rs2 expired", &ring_rs2, rs2.clone(), b"ad", expiry + 1),
                ("rs2 wrong ad", &ring_rs2, rs2.clone(), b"other", NOW_MS),
                ("rs2 single codec", &single, rs2.clone(), b"ad", NOW_MS),
                (
                    "rs2 unknown kid",
                    &ring_rs2,
                    segment(&rs2, 1, &kid_unknown),
                    b"ad",
                    NOW_MS,
                ),
                (
                    "rs2 encoded kid 340",
                    &ring_rs2,
                    segment(&rs2, 1, &"A".repeat(340)),
                    b"ad",
                    NOW_MS,
                ),
                (
                    "rs2 encoded kid 341",
                    &ring_rs2,
                    segment(&rs2, 1, &"A".repeat(341)),
                    b"ad",
                    NOW_MS,
                ),
                (
                    "rs2 kid 255 bytes",
                    &ring_rs2,
                    segment(&rs2, 1, &kid_255),
                    b"ad",
                    NOW_MS,
                ),
                (
                    "rs2 kid 256 bytes, encoded 342",
                    &ring_rs2,
                    segment(&rs2, 1, &kid_256),
                    b"ad",
                    NOW_MS,
                ),
                (
                    "rs2 empty kid",
                    &ring_rs2,
                    segment(&rs2, 1, ""),
                    b"ad",
                    NOW_MS,
                ),
                (
                    "rs2 kid not utf8",
                    &ring_rs2,
                    segment(&rs2, 1, &kid_bad_utf8),
                    b"ad",
                    NOW_MS,
                ),
                (
                    "rs2 bad kid b64",
                    &ring_rs2,
                    segment(&rs2, 1, "!!"),
                    b"ad",
                    NOW_MS,
                ),
                (
                    "rs2 bad body",
                    &ring_rs2,
                    segment(&rs2, 2, "!"),
                    b"ad",
                    NOW_MS,
                ),
                (
                    "rs2 bad tag",
                    &ring_rs2,
                    segment(&rs2, 3, "A"),
                    b"ad",
                    NOW_MS,
                ),
                ("rs2 5 parts", &ring_rs2, format!("{rs2}.x"), b"ad", NOW_MS),
                (
                    "rs2 3 parts",
                    &ring_rs2,
                    "rs2.AA.AA".to_owned(),
                    b"ad",
                    NOW_MS,
                ),
                // Check order: the MAC is verified before the expiry.
                (
                    "rs1 wrong ad + expired",
                    &single,
                    rs1.clone(),
                    b"other",
                    expiry + 1,
                ),
                (
                    "rs2 wrong ad + expired",
                    &ring_rs2,
                    rs2.clone(),
                    b"other",
                    expiry + 1,
                ),
                // Check order: the key is looked up before body and tag are decoded.
                (
                    "rs2 unknown kid + bad body",
                    &ring_rs2,
                    segment(&segment(&rs2, 1, &kid_unknown), 2, "!"),
                    b"ad",
                    NOW_MS,
                ),
                (
                    "rs2 single codec + bad body",
                    &single,
                    segment(&rs2, 2, "!"),
                    b"ad",
                    NOW_MS,
                ),
                // A body shorter than the 8-byte expiry prefix reaches the MAC
                // check (not a format error) when the tag is wrong.
                (
                    "rs1 short body + bad tag",
                    &single,
                    "rs1.AA.AA".to_owned(),
                    b"ad",
                    NOW_MS,
                ),
                (
                    "rs1 ring short body + bad tag",
                    &ring_rs1,
                    "rs1.AA.AA".to_owned(),
                    b"ad",
                    NOW_MS,
                ),
            ];
            let mut out = vec![format!("rs1 -> {rs1}"), format!("rs2 -> {rs2}")];
            for (label, codec, token, ad, now) in cases {
                out.push(format!(
                    "{label}: {}",
                    outcome(codec.open_at(&token, ad, now))
                ));
            }
            out
        }

        /// Expected `run3_matrix()` output (base commit `b9cfcfe`).
        const RUN3_MATRIX: [&str; 18] = [
            "single [] [] -> rs1.AAAAAAAAAAA.eMWx7ePXgVKczL4rS9wflryUEoCOnyBKp0mh_Gp0tNg",
            "Ok: UnknownKeyId Ok: IntegrityCheckFailed UnknownKeyId IntegrityCheckFailed MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat UnknownKeyId UnknownKeyId UnknownKeyId",
            "single [112, 97, 121, 108, 111, 97, 100] [97, 100] -> rs1.AAAAAAAAAABwYXlsb2Fk.geY2me0g1i4if57HkfTrA2A-nqHwMQ2Pe5UzO3-GAEU",
            "Ok:7061796c6f6164 UnknownKeyId Ok:7061796c6f6164 InvalidEncoding UnknownKeyId InvalidEncoding MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat UnknownKeyId UnknownKeyId UnknownKeyId",
            "single [0, 255, 46] [120, 46, 121] -> rs1.AAAAAAAAAAAA_y4.pnTaZMSAp-F1CdiTr4PtlgKyonSpWUmh5R-IHHe33RQ",
            "Ok:00ff2e UnknownKeyId Ok:00ff2e IntegrityCheckFailed UnknownKeyId IntegrityCheckFailed MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat UnknownKeyId UnknownKeyId UnknownKeyId",
            "ring_rs2 [] [] -> rs2.a2lkLcOp.AAAAAAAAAAA.vY9-9F-Gk2HB-6_HKFvS_mnzadpK_86pp8gGg9_8Jr8",
            "UnknownKeyId Ok: UnknownKeyId InvalidEncoding InvalidEncoding InvalidEncoding MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat UnknownKeyId UnknownKeyId UnknownKeyId",
            "ring_rs2 [112, 97, 121, 108, 111, 97, 100] [97, 100] -> rs2.a2lkLcOp.AAAAAAAAAABwYXlsb2Fk.v42DLILOYKVcrv8wEYqfGtqNtGd_GcxSi1DjByyXULY",
            "UnknownKeyId Ok:7061796c6f6164 UnknownKeyId InvalidEncoding InvalidEncoding InvalidEncoding MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat UnknownKeyId UnknownKeyId UnknownKeyId",
            "ring_rs2 [0, 255, 46] [120, 46, 121] -> rs2.a2lkLcOp.AAAAAAAAAAAA_y4.b05X4kMTx7-YpH1jWpu6zytcY11Fa26PJoXQz3uAvcc",
            "UnknownKeyId Ok:00ff2e UnknownKeyId InvalidEncoding InvalidEncoding InvalidEncoding MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat UnknownKeyId UnknownKeyId UnknownKeyId",
            "ring_rs1 [] [] -> rs1.AAAAAAAAAAA.lIeVK0gPUHWby2L5VU5yI35sSx1eaU0_kiyJbXSCYnA",
            "IntegrityCheckFailed UnknownKeyId Ok: IntegrityCheckFailed UnknownKeyId IntegrityCheckFailed MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat UnknownKeyId UnknownKeyId UnknownKeyId",
            "ring_rs1 [112, 97, 121, 108, 111, 97, 100] [97, 100] -> rs1.AAAAAAAAAABwYXlsb2Fk.iYew3xE8Zs0UpeasQ0-4gfu6t8GG4RyHofJ-V5MhyOk",
            "IntegrityCheckFailed UnknownKeyId Ok:7061796c6f6164 InvalidEncoding UnknownKeyId InvalidEncoding MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat UnknownKeyId UnknownKeyId UnknownKeyId",
            "ring_rs1 [0, 255, 46] [120, 46, 121] -> rs1.AAAAAAAAAAAA_y4.OsCMt6mFwjXUd4qi_Cy9Zqh4IJi4OS1Z4XIvtO4Lkwg",
            "IntegrityCheckFailed UnknownKeyId Ok:00ff2e IntegrityCheckFailed UnknownKeyId IntegrityCheckFailed MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat MalformedFormat UnknownKeyId UnknownKeyId UnknownKeyId",
        ];

        /// Expected `pinned_cases()` output (base commit `b9cfcfe`).
        const PINNED: [&str; 37] = [
            "rs1 -> rs1.AAABi8_mx5BwYXlsb2Fk.J-xkb-MpJwN5xolMTbSGGfKKloNYr-8DElzVIpqyYB4",
            "rs2 -> rs2.a2lkLcOp.AAABi8_mx5BwYXlsb2Fk._TRPmvVwYHfjD-gH5glNLhlG1sE_4eGgUIYxR6p8Wl8",
            "rs1 ok: Ok:7061796c6f6164",
            "rs1 ok at expiry: Ok:7061796c6f6164",
            "rs1 expired: Expired",
            "rs1 wrong ad: IntegrityCheckFailed",
            "rs1 ring no fallbacks: UnknownKeyId",
            "rs1 ring last fallback: Ok:7061796c6f6164",
            "rs1 ring expired: Expired",
            "rs1 bad body: InvalidEncoding",
            "rs1 padded tag: InvalidEncoding",
            "rs1 4 parts: MalformedFormat",
            "rs1 2 parts: MalformedFormat",
            "rs3: MalformedFormat",
            "rs2 ok: Ok:7061796c6f6164",
            "rs2 ok at expiry: Ok:7061796c6f6164",
            "rs2 expired: Expired",
            "rs2 wrong ad: IntegrityCheckFailed",
            "rs2 single codec: UnknownKeyId",
            "rs2 unknown kid: UnknownKeyId",
            "rs2 encoded kid 340: UnknownKeyId",
            "rs2 encoded kid 341: InvalidKeyId",
            "rs2 kid 255 bytes: UnknownKeyId",
            "rs2 kid 256 bytes, encoded 342: InvalidKeyId",
            "rs2 empty kid: InvalidKeyId",
            "rs2 kid not utf8: InvalidKeyId",
            "rs2 bad kid b64: InvalidEncoding",
            "rs2 bad body: InvalidEncoding",
            "rs2 bad tag: InvalidEncoding",
            "rs2 5 parts: MalformedFormat",
            "rs2 3 parts: MalformedFormat",
            "rs1 wrong ad + expired: IntegrityCheckFailed",
            "rs2 wrong ad + expired: IntegrityCheckFailed",
            "rs2 unknown kid + bad body: UnknownKeyId",
            "rs2 single codec + bad body: UnknownKeyId",
            "rs1 short body + bad tag: IntegrityCheckFailed",
            "rs1 ring short body + bad tag: IntegrityCheckFailed",
        ];

        fn assert_lines(actual: Vec<String>, expected: &[&str]) {
            for (i, (a, e)) in actual.iter().zip(expected).enumerate() {
                assert_eq!(a, e, "line {i}");
            }
            assert_eq!(actual.len(), expected.len());
        }

        #[test]
        fn run3_token_matrix_is_unchanged() {
            assert_lines(run3_matrix(), &RUN3_MATRIX);
        }

        #[test]
        fn pinned_tokens_and_open_results_are_unchanged() {
            assert_lines(pinned_cases(), &PINNED);
        }
    }

    // ---- Plan step S16: Section 7 boundary cases (E targets) ----
    //
    // The E07, E08, E09, E10 and round-trip tests build their expected tokens and tags from
    // `URL_SAFE_NO_PAD` and `HmacSha256` directly (not from the code under test). The E09a
    // test builds its tag with `wire::transcript_v1` and `prim::hmac_sha256`; the E11 loop is
    // an agreement check against E09/E10, and the E11 named cases are its oracle. Every
    // opening uses an explicit `now_ms`.

    const S16_K1: [u8; 32] = [0x11; 32];
    const S16_K2: [u8; 33] = [0x22; 33];
    const S16_K3: [u8; 40] = [0x33; 40];
    const S16_KN: [u8; 32] = [0x44; 32];

    /// One opening case: label, codec, token, associated data, `now_ms`, expected result.
    type S16Case<'a> = (
        &'a str,
        &'a RequestStateCodec,
        String,
        &'a [u8],
        i64,
        String,
    );

    /// A 255-byte UTF-8 key id made of 127 two-byte characters and one ASCII byte.
    fn s16_kid_255() -> String {
        let kid = format!("{}x", "é".repeat(127));
        assert_eq!(kid.len(), MAX_KID_LEN);
        kid
    }

    /// `Ok:<hex>` or the error's `Debug` text, so results can be compared as strings.
    fn s16_code(result: Result<Vec<u8>, RequestStateError>) -> String {
        match result {
            Ok(payload) => {
                let hex: String = payload.iter().map(|b| format!("{b:02x}")).collect();
                format!("Ok:{hex}")
            }
            Err(e) => format!("{e:?}"),
        }
    }

    fn s16_ok(payload: &[u8]) -> String {
        s16_code(Ok(payload.to_vec()))
    }

    /// Body = 8-byte big-endian expiry followed by the payload (independent of `wire::frame`).
    fn s16_body(expiry: i64, payload: &[u8]) -> Vec<u8> {
        let mut body = expiry.to_be_bytes().to_vec();
        body.extend_from_slice(payload);
        body
    }

    fn s16_tag_v1(key: &[u8], ad: &[u8], body: &[u8]) -> Vec<u8> {
        let mut mac = HmacSha256::new_from_slice(key).unwrap();
        mac.update(DOMAIN_V1);
        mac.update(&(ad.len() as u64).to_be_bytes());
        mac.update(ad);
        mac.update(body);
        mac.finalize().into_bytes().to_vec()
    }

    fn s16_tag_v2(key: &[u8], kid: &[u8], ad: &[u8], body: &[u8]) -> Vec<u8> {
        let mut mac = HmacSha256::new_from_slice(key).unwrap();
        mac.update(DOMAIN_V2);
        mac.update(&(kid.len() as u64).to_be_bytes());
        mac.update(kid);
        mac.update(&(ad.len() as u64).to_be_bytes());
        mac.update(ad);
        mac.update(body);
        mac.finalize().into_bytes().to_vec()
    }

    fn s16_rs1(key: &[u8], ad: &[u8], body: &[u8]) -> String {
        format!(
            "rs1.{}.{}",
            URL_SAFE_NO_PAD.encode(body),
            URL_SAFE_NO_PAD.encode(s16_tag_v1(key, ad, body))
        )
    }

    fn s16_rs2(kid: &[u8], key: &[u8], ad: &[u8], body: &[u8]) -> String {
        format!(
            "rs2.{}.{}.{}",
            URL_SAFE_NO_PAD.encode(kid),
            URL_SAFE_NO_PAD.encode(body),
            URL_SAFE_NO_PAD.encode(s16_tag_v2(key, kid, ad, body))
        )
    }

    fn s16_single() -> RequestStateCodec {
        RequestStateCodec::try_new(S16_K1).unwrap()
    }

    /// Ring with no rs1 fallbacks.
    fn s16_ring_no_fallbacks() -> RequestStateCodec {
        RequestStateCodec::new_with_keyring("n", [("n", S16_KN.to_vec())]).unwrap()
    }

    /// Ring with rs1 fallbacks `a`, `b`, `c` in this order (`c` is the last one) and a
    /// fourth key `n` that is not a fallback.
    fn s16_ring_three_fallbacks() -> RequestStateCodec {
        RequestStateCodec::new_with_keyring(
            "n",
            [
                ("a", S16_K1.to_vec()),
                ("b", S16_K2.to_vec()),
                ("c", S16_K3.to_vec()),
                ("n", S16_KN.to_vec()),
            ],
        )
        .unwrap()
        .with_rs1_fallback("a")
        .unwrap()
        .with_rs1_fallback("b")
        .unwrap()
        .with_rs1_fallback("c")
        .unwrap()
    }

    /// rs2 ring holding a multibyte kid and a 255-byte multibyte kid.
    fn s16_ring_rs2() -> RequestStateCodec {
        RequestStateCodec::new_with_keyring(
            "kid-é",
            [
                ("kid-é".to_owned(), S16_K1.to_vec()),
                (s16_kid_255(), S16_K2.to_vec()),
            ],
        )
        .unwrap()
    }

    // Plan §7 W01/E02: E02 equals W01, including n mod 3 in {0,1,2}, n = 0 and the largest n.
    #[test]
    fn s16_e02_b64_len_agrees_with_w01() {
        let largest = usize::MAX / 4 * 3;
        let mut inputs: Vec<usize> = (0..300).collect();
        inputs.extend((largest - 5)..=largest);
        for n in inputs {
            assert_eq!(RequestStateCodec::b64_len(n), wire::b64_len(n), "n = {n}");
            assert_eq!(RequestStateCodec::b64_len(n), n.div_ceil(3) * 4, "n = {n}");
        }
    }

    // Plan §7 W02/E03: 31, 32, 33 and E03's `actual` field value.
    #[test]
    fn s16_e03_validate_key_length_31_32_33_and_actual() {
        for len in [0, 1, 31] {
            let result = RequestStateCodec::validate_key_length(&vec![0; len]);
            assert!(
                matches!(
                    result,
                    Err(RequestStateError::KeyTooShort {
                        minimum: 32,
                        actual
                    }) if actual == len
                ),
                "len = {len}: {result:?}"
            );
        }
        for len in [32, 33, 1024] {
            let result = RequestStateCodec::validate_key_length(&vec![0; len]);
            assert!(result.is_ok(), "len = {len}: {result:?}");
        }
    }

    // Plan §7 W03/E04: 0, 1, 255, 256 bytes; multibyte UTF-8 crossing 255; the two messages.
    #[test]
    fn s16_e04_validate_config_kid_boundaries_and_messages() {
        let empty = RequestStateCodec::validate_config_kid("");
        assert!(
            matches!(empty, Err(RequestStateError::InvalidKeyring(m)) if m == KID_EMPTY_MSG),
            "{empty:?}"
        );
        let accepted = [
            "k".to_owned(),
            "é".to_owned(),
            "k".repeat(255),
            s16_kid_255(),
            "é".repeat(127),
        ];
        for kid in accepted {
            let result = RequestStateCodec::validate_config_kid(&kid);
            assert!(result.is_ok(), "len = {}: {result:?}", kid.len());
        }
        // 256 bytes: ASCII, and 128 two-byte characters (128 characters, 256 bytes).
        for kid in [
            "k".repeat(256),
            "é".repeat(128),
            format!("{}xy", "é".repeat(127)),
        ] {
            assert_eq!(kid.len(), 256);
            let result = RequestStateCodec::validate_config_kid(&kid);
            let too_long = KID_TOO_LONG_MSG;
            assert!(
                matches!(result, Err(RequestStateError::InvalidKeyring(m)) if m == too_long),
                "{result:?}"
            );
        }
        assert_ne!(KID_EMPTY_MSG, KID_TOO_LONG_MSG);
    }

    // Plan §7 W12-W15/E01: 0-7 bytes, exactly 8, expiry 0, now before/equal/after, negative.
    #[test]
    fn s16_e01_open_authenticated_body_cases() {
        let open = |body: Vec<u8>, now: i64| {
            s16_code(RequestStateCodec::open_authenticated_body(body, now))
        };
        for len in 0..8 {
            assert_eq!(open(vec![0; len], 0), "MalformedFormat", "len = {len}");
            assert_eq!(
                open(vec![0xff; len], i64::MAX),
                "MalformedFormat",
                "len = {len}"
            );
        }
        assert_eq!(open(vec![0; 8], i64::MAX), s16_ok(b""));
        assert_eq!(open(vec![0; 8], i64::MIN), s16_ok(b""));
        assert_eq!(open(s16_body(0, b"p"), i64::MAX), s16_ok(b"p"));
        assert_eq!(open(s16_body(1_000, b"p"), 999), s16_ok(b"p"));
        assert_eq!(open(s16_body(1_000, b"p"), 1_000), s16_ok(b"p"));
        assert_eq!(open(s16_body(1_000, b"p"), 1_001), "Expired");
        assert_eq!(open(s16_body(-5, b"p"), -6), s16_ok(b"p"));
        assert_eq!(open(s16_body(-5, b"p"), -5), s16_ok(b"p"));
        assert_eq!(open(s16_body(-5, b"p"), -4), "Expired");
        assert_eq!(open(s16_body(1, b""), 2), "Expired");
        assert_eq!(open(s16_body(i64::MIN, b""), i64::MIN + 1), "Expired");
        assert_eq!(open(s16_body(0, &[0, 255, 46]), 0), s16_ok(&[0, 255, 46]));
    }

    // Plan §7 E07: empty and nonempty body; delimiters; tag encoding (43 symbols, 32 bytes).
    #[test]
    fn s16_e07_seal_rs1_layout() {
        let bodies: [Vec<u8>; 6] = [
            Vec::new(),
            vec![0x2e],
            vec![0, 0xff],
            vec![0xfb, 0xff, 0xbf],
            s16_body(0, b""),
            s16_body(1_000, b"payload"),
        ];
        for body in &bodies {
            for ad in [&b""[..], b"user:alice|x.y"] {
                let token = RequestStateCodec::seal_rs1(&S16_K1, ad, body);
                assert_eq!(token, s16_rs1(&S16_K1, ad, body), "{body:?}");
                assert_eq!(token.matches('.').count(), 2, "{token}");
                assert!(!token.contains('='), "{token}");
                let parts: Vec<&str> = token.split('.').collect();
                assert_eq!(parts[0], "rs1");
                assert_eq!(URL_SAFE_NO_PAD.decode(parts[1]).unwrap(), *body);
                assert_eq!(parts[2].len(), 43, "{token}");
                assert_eq!(
                    URL_SAFE_NO_PAD.decode(parts[2]).unwrap(),
                    s16_tag_v1(&S16_K1, ad, body)
                );
            }
        }
        // Empty body: "rs1." followed directly by the "." before the tag.
        assert!(RequestStateCodec::seal_rs1(&S16_K1, b"", b"").starts_with("rs1.."));
    }

    // Plan §7 E08: empty and nonempty body; delimiters; tag encoding; multibyte kid.
    #[test]
    fn s16_e08_seal_rs2_layout() {
        let kids = ["k".to_owned(), "kid-é".to_owned(), s16_kid_255()];
        let bodies: [Vec<u8>; 3] = [Vec::new(), s16_body(0, b""), s16_body(-1, b"p.q")];
        for kid in &kids {
            for body in &bodies {
                let ad = b"ad";
                let token = RequestStateCodec::seal_rs2(kid, &S16_K2, ad, body);
                assert_eq!(token, s16_rs2(kid.as_bytes(), &S16_K2, ad, body));
                assert_eq!(token.matches('.').count(), 3, "{token}");
                assert!(!token.contains('='), "{token}");
                let parts: Vec<&str> = token.split('.').collect();
                assert_eq!(parts[0], "rs2");
                assert_eq!(URL_SAFE_NO_PAD.decode(parts[1]).unwrap(), kid.as_bytes());
                assert_eq!(URL_SAFE_NO_PAD.decode(parts[2]).unwrap(), *body);
                assert_eq!(parts[3].len(), 43, "{token}");
                assert_eq!(
                    URL_SAFE_NO_PAD.decode(parts[3]).unwrap(),
                    s16_tag_v2(&S16_K2, kid.as_bytes(), ad, body)
                );
            }
        }
        // The 255-byte kid encodes to exactly `MAX_ENCODED_KID_LEN` symbols.
        let token = RequestStateCodec::seal_rs2(&s16_kid_255(), &S16_K2, b"", b"");
        assert_eq!(token.split('.').nth(1).unwrap().len(), MAX_ENCODED_KID_LEN);
    }

    // Plan §7 E09 and §3 "E09 - error order": malformed (also on a ring with no fallbacks:
    // parsing first); ring with no fallbacks (before any decoding); bad Base64 body/tag; MAC
    // fails; match on the last fallback; expiry; E01.
    #[test]
    fn s16_e09_open_rs1_at_error_order() {
        let single = s16_single();
        let none = s16_ring_no_fallbacks();
        let ring = s16_ring_three_fallbacks();
        let body = s16_body(1_000, b"payload");
        let ok = s16_rs1(&S16_K1, b"ad", &body);
        let ok_parts: Vec<&str> = ok.split('.').collect();
        let cases: Vec<S16Case<'_>> = vec![
            (
                "2 parts",
                &single,
                "rs1.a".into(),
                b"ad",
                0,
                "MalformedFormat".into(),
            ),
            (
                "4 parts",
                &single,
                format!("{ok}.x"),
                b"ad",
                0,
                "MalformedFormat".into(),
            ),
            (
                "no dot",
                &single,
                "rs1".into(),
                b"ad",
                0,
                "MalformedFormat".into(),
            ),
            (
                "ring, no fallbacks, 2 parts",
                &none,
                "rs1.a".into(),
                b"ad",
                0,
                "MalformedFormat".into(),
            ),
            (
                "ring, no fallbacks, 4 parts",
                &none,
                format!("{ok}.x"),
                b"ad",
                0,
                "MalformedFormat".into(),
            ),
            (
                "ring, no fallbacks, no dot",
                &none,
                "rs1".into(),
                b"ad",
                0,
                "MalformedFormat".into(),
            ),
            (
                "ring, no fallbacks, bad b64",
                &none,
                "rs1.!!!!.!!!!".into(),
                b"ad",
                0,
                "UnknownKeyId".into(),
            ),
            (
                "ring, no fallbacks, ring key",
                &none,
                s16_rs1(&S16_KN, b"ad", &body),
                b"ad",
                0,
                "UnknownKeyId".into(),
            ),
            (
                "bad body",
                &single,
                format!("rs1.!.{}", ok_parts[2]),
                b"ad",
                0,
                "InvalidEncoding".into(),
            ),
            (
                "bad tag",
                &single,
                format!("rs1.{}.!!!!", ok_parts[1]),
                b"ad",
                0,
                "InvalidEncoding".into(),
            ),
            (
                "padded tag",
                &single,
                format!("{ok}="),
                b"ad",
                0,
                "InvalidEncoding".into(),
            ),
            (
                "bad body and tag",
                &single,
                "rs1.!.!".into(),
                b"ad",
                0,
                "InvalidEncoding".into(),
            ),
            (
                "ring bad body",
                &ring,
                format!("rs1.!.{}", ok_parts[2]),
                b"ad",
                0,
                "InvalidEncoding".into(),
            ),
            (
                "empty tag",
                &single,
                format!("rs1.{}.", ok_parts[1]),
                b"ad",
                0,
                "IntegrityCheckFailed".into(),
            ),
            (
                "empty body and tag",
                &single,
                "rs1..".into(),
                b"ad",
                0,
                "IntegrityCheckFailed".into(),
            ),
            (
                "wrong key",
                &single,
                s16_rs1(&S16_K2, b"ad", &body),
                b"ad",
                0,
                "IntegrityCheckFailed".into(),
            ),
            (
                "wrong ad",
                &single,
                ok.clone(),
                b"other",
                0,
                "IntegrityCheckFailed".into(),
            ),
            (
                "ring, non-fallback key",
                &ring,
                s16_rs1(&S16_KN, b"ad", &body),
                b"ad",
                0,
                "IntegrityCheckFailed".into(),
            ),
            (
                "ring, first fallback",
                &ring,
                s16_rs1(&S16_K1, b"ad", &body),
                b"ad",
                0,
                s16_ok(b"payload"),
            ),
            (
                "ring, middle fallback",
                &ring,
                s16_rs1(&S16_K2, b"ad", &body),
                b"ad",
                0,
                s16_ok(b"payload"),
            ),
            (
                "ring, last fallback",
                &ring,
                s16_rs1(&S16_K3, b"ad", &body),
                b"ad",
                0,
                s16_ok(b"payload"),
            ),
            (
                "now = expiry",
                &single,
                ok.clone(),
                b"ad",
                1_000,
                s16_ok(b"payload"),
            ),
            (
                "now = expiry + 1",
                &single,
                ok.clone(),
                b"ad",
                1_001,
                "Expired".into(),
            ),
            (
                "now = i64::MIN",
                &single,
                ok.clone(),
                b"ad",
                i64::MIN,
                s16_ok(b"payload"),
            ),
            (
                "ring, last fallback, now = expiry",
                &ring,
                s16_rs1(&S16_K3, b"ad", &body),
                b"ad",
                1_000,
                s16_ok(b"payload"),
            ),
            (
                "ring, last fallback, expired",
                &ring,
                s16_rs1(&S16_K3, b"ad", &body),
                b"ad",
                1_001,
                "Expired".into(),
            ),
            (
                "wrong ad and expired",
                &single,
                ok.clone(),
                b"other",
                1_001,
                "IntegrityCheckFailed".into(),
            ),
            (
                "authenticated 7-byte body",
                &single,
                s16_rs1(&S16_K1, b"ad", &[0; 7]),
                b"ad",
                0,
                "MalformedFormat".into(),
            ),
            (
                "ring, last fallback, 7-byte body",
                &ring,
                s16_rs1(&S16_K3, b"ad", &[0; 7]),
                b"ad",
                0,
                "MalformedFormat".into(),
            ),
            (
                "authenticated 8-byte body",
                &single,
                s16_rs1(&S16_K1, b"ad", &[0; 8]),
                b"ad",
                i64::MAX,
                s16_ok(b""),
            ),
        ];
        for (label, codec, token, ad, now, expected) in cases {
            assert_eq!(
                s16_code(codec.open_rs1_at(&token, ad, now)),
                expected,
                "{label}"
            );
        }
    }

    // Plan §7 E09a: no fallbacks; match on the first, a middle and the last fallback; no match;
    // duplicate ids; wrong-length tags.
    #[test]
    fn s16_e09a_rs1_fallbacks_verify_cases() {
        let mut keys: HashMap<String, Zeroizing<Vec<u8>>> = HashMap::new();
        keys.insert("a".into(), Zeroizing::new(S16_K1.to_vec()));
        keys.insert("b".into(), Zeroizing::new(S16_K2.to_vec()));
        keys.insert("c".into(), Zeroizing::new(S16_K3.to_vec()));
        let transcript = wire::transcript_v1(b"ad", &s16_body(0, b"p"));
        let tag_c = prim::hmac_sha256(&S16_K3, &transcript);
        let verify = |fallbacks: &[&str], tag: &[u8]| {
            let fallbacks: Vec<String> = fallbacks.iter().map(|s| s.to_string()).collect();
            RequestStateCodec::rs1_fallbacks_verify(&keys, &fallbacks, &transcript, tag)
        };
        assert!(!verify(&[], &tag_c));
        assert!(!verify(&["a"], &tag_c));
        assert!(!verify(&["a", "b"], &tag_c));
        assert!(verify(&["c"], &tag_c));
        assert!(verify(&["a", "b", "c"], &tag_c));
        assert!(verify(&["c", "a", "b"], &tag_c));
        assert!(verify(&["a", "c", "b"], &tag_c));
        assert!(verify(&["c", "c"], &tag_c));
        assert!(!verify(&["a", "a"], &tag_c));
        assert!(!verify(&["a", "b", "c"], &tag_c[..31]));
        assert!(!verify(&["a", "b", "c"], &[]));
        let mut flipped = tag_c;
        flipped[31] ^= 1;
        assert!(!verify(&["a", "b", "c"], &flipped));
    }

    // Plan §7 E10 and §3 "E10 - error order": encoded kid 340/341; decoded kid 0/255; invalid
    // UTF-8; single-key codec; unknown kid; bad body/tag; MAC fails (including a tag made for
    // another kid with the same key: W11 binds the kid); expiry; E01.
    #[test]
    fn s16_e10_open_rs2_at_error_order() {
        let single = s16_single();
        let ring = s16_ring_rs2();
        // Two kids with the same key: only the kid in the transcript differs.
        let shared = RequestStateCodec::new_with_keyring(
            "kid-a",
            [("kid-a", S16_K1.to_vec()), ("kid-b", S16_K1.to_vec())],
        )
        .unwrap();
        let kid = "kid-é".as_bytes();
        let kid_255 = s16_kid_255();
        let body = s16_body(1_000, b"payload");
        let ok = s16_rs2(kid, &S16_K1, b"ad", &body);
        let ok_255 = s16_rs2(kid_255.as_bytes(), &S16_K2, b"ad", &body);
        let p: Vec<&str> = ok.split('.').collect();
        let with_kid = |encoded_kid: &str| format!("rs2.{encoded_kid}.{}.{}", p[2], p[3]);
        let a340 = "A".repeat(340);
        let a341 = "A".repeat(341);
        let unknown = with_kid(&URL_SAFE_NO_PAD.encode("kid-x"));
        let token_a = s16_rs2(b"kid-a", &S16_K1, b"ad", &body);
        let parts_a: Vec<&str> = token_a.split('.').collect();
        let kid_b_with_tag_a = format!(
            "rs2.{}.{}.{}",
            URL_SAFE_NO_PAD.encode("kid-b"),
            parts_a[2],
            parts_a[3]
        );
        let cases: Vec<S16Case<'_>> = vec![
            (
                "3 parts",
                &ring,
                "rs2.a.b".into(),
                b"ad",
                0,
                "MalformedFormat".into(),
            ),
            (
                "5 parts",
                &ring,
                format!("{ok}.x"),
                b"ad",
                0,
                "MalformedFormat".into(),
            ),
            (
                "no dot",
                &ring,
                "rs2".into(),
                b"ad",
                0,
                "MalformedFormat".into(),
            ),
            (
                "encoded kid 341",
                &ring,
                with_kid(&a341),
                b"ad",
                0,
                "InvalidKeyId".into(),
            ),
            (
                "encoded kid 341, bad body",
                &ring,
                format!("rs2.{a341}.!.!"),
                b"ad",
                0,
                "InvalidKeyId".into(),
            ),
            (
                "encoded kid 341, single codec",
                &single,
                with_kid(&a341),
                b"ad",
                0,
                "InvalidKeyId".into(),
            ),
            (
                "encoded kid 340, 255 NUL bytes, unknown",
                &ring,
                with_kid(&a340),
                b"ad",
                0,
                "UnknownKeyId".into(),
            ),
            (
                "encoded kid 340, known 255-byte kid",
                &ring,
                ok_255.clone(),
                b"ad",
                0,
                s16_ok(b"payload"),
            ),
            (
                "bad kid b64",
                &ring,
                with_kid("!!"),
                b"ad",
                0,
                "InvalidEncoding".into(),
            ),
            (
                "padded kid",
                &ring,
                with_kid("YQ=="),
                b"ad",
                0,
                "InvalidEncoding".into(),
            ),
            (
                "kid length 1 mod 4",
                &ring,
                with_kid("AAAAA"),
                b"ad",
                0,
                "InvalidEncoding".into(),
            ),
            (
                "decoded kid 0 bytes",
                &ring,
                with_kid(""),
                b"ad",
                0,
                "InvalidKeyId".into(),
            ),
            (
                "decoded kid 0 bytes, single codec",
                &single,
                with_kid(""),
                b"ad",
                0,
                "InvalidKeyId".into(),
            ),
            (
                "kid 0xff",
                &ring,
                with_kid(&URL_SAFE_NO_PAD.encode([0xff])),
                b"ad",
                0,
                "InvalidKeyId".into(),
            ),
            (
                "kid truncated multibyte",
                &ring,
                with_kid(&URL_SAFE_NO_PAD.encode([b'k', 0xc3])),
                b"ad",
                0,
                "InvalidKeyId".into(),
            ),
            (
                "kid 255 x 0xff",
                &ring,
                with_kid(&URL_SAFE_NO_PAD.encode([0xff; 255])),
                b"ad",
                0,
                "InvalidKeyId".into(),
            ),
            (
                "kid not utf8, single codec",
                &single,
                with_kid(&URL_SAFE_NO_PAD.encode([0xff])),
                b"ad",
                0,
                "InvalidKeyId".into(),
            ),
            (
                "single codec",
                &single,
                ok.clone(),
                b"ad",
                0,
                "UnknownKeyId".into(),
            ),
            (
                "single codec, bad body",
                &single,
                format!("rs2.{}.!.!", p[1]),
                b"ad",
                0,
                "UnknownKeyId".into(),
            ),
            (
                "unknown kid",
                &ring,
                unknown.clone(),
                b"ad",
                0,
                "UnknownKeyId".into(),
            ),
            (
                "unknown kid, bad body",
                &ring,
                format!("rs2.{}.!.!", URL_SAFE_NO_PAD.encode("kid-x")),
                b"ad",
                0,
                "UnknownKeyId".into(),
            ),
            (
                "bad body",
                &ring,
                format!("rs2.{}.!.{}", p[1], p[3]),
                b"ad",
                0,
                "InvalidEncoding".into(),
            ),
            (
                "bad tag",
                &ring,
                format!("rs2.{}.{}.!!!!", p[1], p[2]),
                b"ad",
                0,
                "InvalidEncoding".into(),
            ),
            (
                "padded tag",
                &ring,
                format!("{ok}="),
                b"ad",
                0,
                "InvalidEncoding".into(),
            ),
            (
                "empty tag",
                &ring,
                format!("rs2.{}.{}.", p[1], p[2]),
                b"ad",
                0,
                "IntegrityCheckFailed".into(),
            ),
            (
                "wrong key",
                &ring,
                s16_rs2(kid, &S16_K2, b"ad", &body),
                b"ad",
                0,
                "IntegrityCheckFailed".into(),
            ),
            (
                "wrong ad",
                &ring,
                ok.clone(),
                b"other",
                0,
                "IntegrityCheckFailed".into(),
            ),
            (
                "same key, tag made for kid-a, presented with kid-b",
                &shared,
                kid_b_with_tag_a,
                b"ad",
                0,
                "IntegrityCheckFailed".into(),
            ),
            (
                "same key, kid-a token",
                &shared,
                s16_rs2(b"kid-a", &S16_K1, b"ad", &body),
                b"ad",
                0,
                s16_ok(b"payload"),
            ),
            (
                "same key, kid-b token",
                &shared,
                s16_rs2(b"kid-b", &S16_K1, b"ad", &body),
                b"ad",
                0,
                s16_ok(b"payload"),
            ),
            (
                "tag for another kid and another key",
                &ring,
                with_kid(&URL_SAFE_NO_PAD.encode(&kid_255)),
                b"ad",
                0,
                "IntegrityCheckFailed".into(),
            ),
            (
                "now = expiry",
                &ring,
                ok.clone(),
                b"ad",
                1_000,
                s16_ok(b"payload"),
            ),
            (
                "now = expiry + 1",
                &ring,
                ok.clone(),
                b"ad",
                1_001,
                "Expired".into(),
            ),
            (
                "255-byte kid, now = expiry",
                &ring,
                ok_255.clone(),
                b"ad",
                1_000,
                s16_ok(b"payload"),
            ),
            (
                "255-byte kid, expired",
                &ring,
                ok_255.clone(),
                b"ad",
                1_001,
                "Expired".into(),
            ),
            (
                "wrong ad and expired",
                &ring,
                ok.clone(),
                b"other",
                1_001,
                "IntegrityCheckFailed".into(),
            ),
            (
                "authenticated 7-byte body",
                &ring,
                s16_rs2(kid, &S16_K1, b"ad", &[0; 7]),
                b"ad",
                0,
                "MalformedFormat".into(),
            ),
            (
                "authenticated 8-byte body",
                &ring,
                s16_rs2(kid, &S16_K1, b"ad", &[0; 8]),
                b"ad",
                i64::MIN,
                s16_ok(b""),
            ),
        ];
        for (label, codec, token, ad, now, expected) in cases {
            assert_eq!(
                s16_code(codec.open_rs2_at(&token, ad, now)),
                expected,
                "{label}"
            );
        }
        // 340 encoded symbols decode to 255 bytes; 341 cannot be a valid encoding at all.
        assert_eq!(URL_SAFE_NO_PAD.decode(&a340).unwrap().len(), MAX_KID_LEN);
        assert!(URL_SAFE_NO_PAD.decode(&a341).is_err());
        assert_eq!(ok_255.split('.').nth(1).unwrap().len(), MAX_ENCODED_KID_LEN);
    }

    // Plan §7 W07/E11: `rs1` -> E09, `rs2` -> E10 with the result unchanged; `rs3`, `rs1x`,
    // empty string and no `.` -> `MalformedFormat`. The loop checks agreement with E09/E10
    // (computed by the code under test); the named cases after it are the oracle.
    #[test]
    fn s16_e11_open_at_dispatch() {
        let codecs = [
            s16_single(),
            s16_ring_no_fallbacks(),
            s16_ring_three_fallbacks(),
            s16_ring_rs2(),
        ];
        let body = s16_body(1_000, b"payload");
        let rs1 = s16_rs1(&S16_K1, b"ad", &body);
        let rs2 = s16_rs2("kid-é".as_bytes(), &S16_K1, b"ad", &body);
        let corpus = [
            rs1.clone(),
            rs2.clone(),
            format!("{rs1}.x"),
            format!("{rs2}.x"),
            "rs1".to_owned(),
            "rs2".to_owned(),
            "rs1.!.!".to_owned(),
            "rs2.!!.!.!".to_owned(),
            "rs2..AA.AA".to_owned(),
            rs1.replacen("rs1", "rs3", 1),
            rs1.replacen("rs1", "rs1x", 1),
            rs2.replacen("rs2", "rs2x", 1),
            String::new(),
            "abc".to_owned(),
            ".rs1.a.b".to_owned(),
            "RS1.a.b".to_owned(),
        ];
        for codec in &codecs {
            for token in &corpus {
                for now in [0, 1_000, 1_001] {
                    let expected = match wire::version_of(token.as_bytes()) {
                        Some(wire::Version::V1) => s16_code(codec.open_rs1_at(token, b"ad", now)),
                        Some(wire::Version::V2) => s16_code(codec.open_rs2_at(token, b"ad", now)),
                        None => "MalformedFormat".to_owned(),
                    };
                    let actual = s16_code(codec.open_at(token, b"ad", now));
                    assert_eq!(actual, expected, "{token:?} at {now}");
                }
            }
        }
        // The plan's named cases, explicitly.
        let single = s16_single();
        let ring = s16_ring_rs2();
        for token in ["rs3.a.b", "rs1x.a.b", "rs1x", "", "abc"] {
            assert_eq!(s16_code(single.open_at(token, b"", 0)), "MalformedFormat");
            assert_eq!(s16_code(ring.open_at(token, b"", 0)), "MalformedFormat");
        }
        assert_eq!(s16_code(single.open_at(&rs1, b"ad", 0)), s16_ok(b"payload"));
        assert_eq!(s16_code(ring.open_at(&rs2, b"ad", 0)), s16_ok(b"payload"));
        assert_eq!(s16_code(single.open_at(&rs2, b"ad", 0)), "UnknownKeyId");
        assert_eq!(s16_code(ring.open_at(&rs1, b"ad", 0)), "UnknownKeyId");
        // `rs1`/`rs2` with no `.` reach E09/E10 and are rejected there.
        assert_eq!(s16_code(single.open_at("rs1", b"", 0)), "MalformedFormat");
        assert_eq!(s16_code(ring.open_at("rs2", b"", 0)), "MalformedFormat");
    }

    /// (body, a time at which it is not expired) pairs: body lengths 8 and up, expiry 0,
    /// positive (now before and equal), negative and extreme.
    fn s16_roundtrip_bodies() -> Vec<(Vec<u8>, i64)> {
        vec![
            (vec![0; 8], i64::MAX),
            (s16_body(0, b"p"), i64::MIN),
            (s16_body(1_000, b"payload"), 999),
            (s16_body(1_000, b"payload"), 1_000),
            (s16_body(-5, &[0, 255, 46]), -5),
            (s16_body(i64::MIN, b"x"), i64::MIN),
            (s16_body(i64::MAX, &[0x2e; 100]), i64::MAX),
        ]
    }

    // Plan §3 "Round-trip" (S15 `rs1_roundtrip`, `open_at_roundtrip_rs1`): single key.
    #[test]
    fn s16_roundtrip_rs1_single_key() {
        let codec = s16_single();
        for (body, now) in s16_roundtrip_bodies() {
            for ad in [&b""[..], b"ad"] {
                let token = RequestStateCodec::seal_rs1(&S16_K1, ad, &body);
                let expected = s16_ok(&body[8..]);
                assert_eq!(s16_code(codec.open_rs1_at(&token, ad, now)), expected);
                assert_eq!(s16_code(codec.open_at(&token, ad, now)), expected);
            }
        }
    }

    // Plan §3 "Round-trip": rs1 opened by a ring whose fallbacks include the signing key
    // (first, middle and last fallback).
    #[test]
    fn s16_roundtrip_rs1_ring() {
        let codec = s16_ring_three_fallbacks();
        let keys: [&[u8]; 3] = [&S16_K1, &S16_K2, &S16_K3];
        for key in keys {
            for (body, now) in s16_roundtrip_bodies() {
                let token = RequestStateCodec::seal_rs1(key, b"ad", &body);
                let expected = s16_ok(&body[8..]);
                assert_eq!(s16_code(codec.open_rs1_at(&token, b"ad", now)), expected);
                assert_eq!(s16_code(codec.open_at(&token, b"ad", now)), expected);
            }
        }
    }

    // Plan §3 "Round-trip" (S15 `rs2_roundtrip`, `open_at_roundtrip_rs2`): valid UTF-8 kid of
    // 1-255 bytes mapped by the ring to the signing key.
    #[test]
    fn s16_roundtrip_rs2() {
        let ring = s16_ring_rs2();
        let one_byte = RequestStateCodec::new_with_keyring("k", [("k", S16_K3.to_vec())]).unwrap();
        let cases = [
            (&ring, "kid-é".to_owned(), &S16_K1[..]),
            (&ring, s16_kid_255(), &S16_K2[..]),
            (&one_byte, "k".to_owned(), &S16_K3[..]),
        ];
        for (codec, kid, key) in cases {
            for (body, now) in s16_roundtrip_bodies() {
                for ad in [&b""[..], b"ad"] {
                    let token = RequestStateCodec::seal_rs2(&kid, key, ad, &body);
                    let expected = s16_ok(&body[8..]);
                    assert_eq!(s16_code(codec.open_rs2_at(&token, ad, now)), expected);
                    assert_eq!(s16_code(codec.open_at(&token, ad, now)), expected);
                }
            }
        }
    }
}
