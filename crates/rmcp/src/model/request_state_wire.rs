//! Request-state wire format: public, pure building blocks.
//!
//! Every function here works on bytes, integers and `Vec<u8>`, uses no
//! `str` patterns, no HMAC types and no string literals in results, so that
//! Aeneas translates each one without an adapter. HMAC-SHA256 and Base64url
//! live in [`prim`], the only opaque boundary.

/// Version tag of the single-key format.
pub const VERSION_V1: &[u8] = b"rs1";
/// Version tag of the key-id format.
pub const VERSION_V2: &[u8] = b"rs2";
/// MAC domain separator for `rs1`.
pub const DOMAIN_V1: &[u8] = b"rmcp/mrtr/request-state/v1";
/// MAC domain separator for `rs2`.
pub const DOMAIN_V2: &[u8] = b"rmcp/mrtr/request-state/v2";
/// Length of the big-endian expiry prefix of a body.
pub const EXPIRY_LEN: usize = 8;
/// Minimum key length in bytes.
pub const MIN_KEY_LENGTH: usize = 32;
/// Maximum key-id length in bytes.
pub const MAX_KID_LEN: usize = 255;
/// Maximum Base64url length of an encoded key id.
pub const MAX_ENCODED_KID_LEN: usize = 340;
/// Length of an HMAC-SHA256 tag.
pub const TAG_LEN: usize = 32;

/// Upper bound on the unpadded Base64url length of `len` bytes.
/// Equal to `len.div_ceil(3) * 4`; overflows exactly when that does.
#[allow(
    clippy::manual_is_multiple_of,
    reason = "`is_multiple_of` has no Aeneas model"
)]
pub fn b64_len(len: usize) -> usize {
    let full = len / 3 * 4;
    if len % 3 == 0 { full } else { full + 4 }
}

/// `true` iff a key of `len` bytes is long enough.
pub fn key_length_ok(len: usize) -> bool {
    len >= MIN_KEY_LENGTH
}

/// Why a configured key id is rejected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum KidError {
    /// The key id is empty.
    Empty,
    /// The key id is longer than [`MAX_KID_LEN`] bytes.
    TooLong,
}

/// Checks the byte length of a key id (any bytes; UTF-8 is the caller's type).
pub fn check_kid_len(len: usize) -> Result<(), KidError> {
    if len == 0 {
        return Err(KidError::Empty);
    }
    if len > MAX_KID_LEN {
        return Err(KidError::TooLong);
    }
    Ok(())
}

/// Byte-slice equality.
pub fn bytes_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// Index of the first `.` at or after `start`, or `s.len()` if there is none.
pub fn next_dot(s: &[u8], start: usize) -> usize {
    let mut i = start;
    while i < s.len() {
        if s[i] == b'.' {
            return i;
        }
        i += 1;
    }
    s.len()
}

/// Number of `.`-separated components (`split('.').count()`; at least 1).
pub fn component_count(s: &[u8]) -> usize {
    let mut n = 1;
    let mut i = 0;
    while i < s.len() {
        if s[i] == b'.' {
            n += 1;
        }
        i += 1;
    }
    n
}

/// Token version, from the first `.`-component.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Version {
    /// `rs1`
    V1,
    /// `rs2`
    V2,
}

/// The version named by the first `.`-component, if it is `rs1` or `rs2`.
pub fn version_of(s: &[u8]) -> Option<Version> {
    let first = &s[..next_dot(s, 0)];
    if bytes_eq(first, VERSION_V1) {
        Some(Version::V1)
    } else if bytes_eq(first, VERSION_V2) {
        Some(Version::V2)
    } else {
        None
    }
}

/// Parsed `rs1.<body>.<tag>` token (components still Base64url).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct Rs1Parts<'a> {
    /// Encoded body.
    pub body: &'a [u8],
    /// Encoded tag.
    pub tag: &'a [u8],
}

/// Splits an `rs1` token: exactly three components, the first `rs1`.
pub fn parse_rs1(s: &[u8]) -> Option<Rs1Parts<'_>> {
    if component_count(s) != 3 {
        return None;
    }
    let d1 = next_dot(s, 0);
    let d2 = next_dot(s, d1 + 1);
    if !bytes_eq(&s[..d1], VERSION_V1) {
        return None;
    }
    Some(Rs1Parts {
        body: &s[d1 + 1..d2],
        tag: &s[d2 + 1..],
    })
}

/// Parsed `rs2.<kid>.<body>.<tag>` token (components still Base64url).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct Rs2Parts<'a> {
    /// Encoded key id.
    pub kid: &'a [u8],
    /// Encoded body.
    pub body: &'a [u8],
    /// Encoded tag.
    pub tag: &'a [u8],
}

/// Splits an `rs2` token: exactly four components, the first `rs2`.
pub fn parse_rs2(s: &[u8]) -> Option<Rs2Parts<'_>> {
    if component_count(s) != 4 {
        return None;
    }
    let d1 = next_dot(s, 0);
    let d2 = next_dot(s, d1 + 1);
    let d3 = next_dot(s, d2 + 1);
    if !bytes_eq(&s[..d1], VERSION_V2) {
        return None;
    }
    Some(Rs2Parts {
        kid: &s[d1 + 1..d2],
        body: &s[d2 + 1..d3],
        tag: &s[d3 + 1..],
    })
}

/// `DOMAIN_V1 ++ be64(len ad) ++ ad ++ body`: the bytes `rs1` authenticates.
pub fn transcript_v1(associated_data: &[u8], body: &[u8]) -> Vec<u8> {
    let mut t = Vec::new();
    t.extend_from_slice(DOMAIN_V1);
    t.extend_from_slice(&(associated_data.len() as u64).to_be_bytes());
    t.extend_from_slice(associated_data);
    t.extend_from_slice(body);
    t
}

/// `DOMAIN_V2 ++ be64(len kid) ++ kid ++ be64(len ad) ++ ad ++ body`.
pub fn transcript_v2(kid: &[u8], associated_data: &[u8], body: &[u8]) -> Vec<u8> {
    let mut t = Vec::new();
    t.extend_from_slice(DOMAIN_V2);
    t.extend_from_slice(&(kid.len() as u64).to_be_bytes());
    t.extend_from_slice(kid);
    t.extend_from_slice(&(associated_data.len() as u64).to_be_bytes());
    t.extend_from_slice(associated_data);
    t.extend_from_slice(body);
    t
}

/// Signed big-endian expiry from the first 8 body bytes.
pub fn decode_expiry(head: [u8; 8]) -> i64 {
    u64::from_be_bytes(head) as i64
}

/// `true` iff a token with this expiry is expired at `now_ms` (0 = never).
pub fn is_expired(expiry: i64, now_ms: i64) -> bool {
    expiry != 0 && now_ms > expiry
}

/// Why an authenticated body is rejected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum FrameError {
    /// Shorter than [`EXPIRY_LEN`].
    TooShort,
    /// Expiry passed.
    Expired,
}

/// Checks framing and expiry of an authenticated body; returns the payload.
pub fn open_frame(body: &[u8], now_ms: i64) -> Result<&[u8], FrameError> {
    if body.len() < EXPIRY_LEN {
        return Err(FrameError::TooShort);
    }
    let head = [
        body[0], body[1], body[2], body[3], body[4], body[5], body[6], body[7],
    ];
    if is_expired(decode_expiry(head), now_ms) {
        return Err(FrameError::Expired);
    }
    Ok(&body[EXPIRY_LEN..])
}

/// `expiry` as 8 big-endian bytes followed by `payload`.
pub fn frame(expiry: i64, payload: &[u8]) -> Vec<u8> {
    let mut body = Vec::new();
    body.extend_from_slice(&(expiry as u64).to_be_bytes());
    body.extend_from_slice(payload);
    body
}

/// Opaque primitives: the only code that is not extracted.
pub mod prim {
    use base64::{Engine, engine::general_purpose::URL_SAFE_NO_PAD};
    use hmac::{Hmac, KeyInit, Mac};
    use sha2::Sha256;

    /// HMAC-SHA256 of `msg` under `key`.
    pub fn hmac_sha256(key: &[u8], msg: &[u8]) -> [u8; 32] {
        let mut m = <Hmac<Sha256> as KeyInit>::new_from_slice(key)
            .expect("HMAC accepts keys of any length");
        m.update(msg);
        m.finalize().into_bytes().into()
    }

    /// Constant-time check that `tag` is the HMAC-SHA256 of `msg` under `key`.
    pub fn hmac_sha256_verify(key: &[u8], msg: &[u8], tag: &[u8]) -> bool {
        let mut m = <Hmac<Sha256> as KeyInit>::new_from_slice(key)
            .expect("HMAC accepts keys of any length");
        m.update(msg);
        m.verify_slice(tag).is_ok()
    }

    /// Appends the unpadded Base64url encoding of `input` to `out`.
    pub fn b64_encode_into(input: &[u8], out: &mut String) {
        URL_SAFE_NO_PAD.encode_string(input, out);
    }

    /// Strict unpadded Base64url decoding; `None` on any error.
    pub fn b64_decode(input: &[u8]) -> Option<Vec<u8>> {
        URL_SAFE_NO_PAD.decode(input).ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(s: &str) -> Vec<u8> {
        assert!(s.len().is_multiple_of(2), "odd-length hex literal");
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("hex literal"))
            .collect()
    }

    /// Reference splitter: the components of `str::split('.')`, as bytes.
    fn split_dots(s: &[u8]) -> Vec<&[u8]> {
        s.split(|b| *b == b'.').collect()
    }

    // W01 (and E02, which delegates to it).
    #[test]
    fn b64_len_boundaries() {
        assert_eq!(b64_len(0), 0);
        assert_eq!(b64_len(1), 4);
        assert_eq!(b64_len(2), 4);
        assert_eq!(b64_len(3), 4);
        assert_eq!(b64_len(4), 8);
        assert_eq!(b64_len(5), 8);
        assert_eq!(b64_len(6), 8);
        for n in 0..3000 {
            assert_eq!(b64_len(n), n.div_ceil(3) * 4, "n = {n}");
        }
    }

    #[test]
    fn b64_len_largest_input_without_overflow() {
        // Largest n with ceil(n / 3) * 4 <= usize::MAX.
        let largest = usize::MAX / 4 * 3;
        assert_eq!(b64_len(largest), largest.div_ceil(3) * 4);
        assert_eq!(b64_len(largest), usize::MAX / 4 * 4);
        assert!((largest + 1).div_ceil(3).checked_mul(4).is_none());
        for n in [largest - 2, largest - 1] {
            assert_eq!(b64_len(n), n.div_ceil(3) * 4, "n = {n}");
        }
    }

    #[test]
    fn b64_len_matches_encoder_output_length() {
        for n in 0..200 {
            let mut out = String::new();
            prim::b64_encode_into(&vec![0xa5; n], &mut out);
            // `b64_len` is an upper bound that is exact when `n` is a multiple of 3.
            assert!(out.len() <= b64_len(n), "n = {n}");
            assert!(b64_len(n) - out.len() < 3, "n = {n}");
            if n % 3 == 0 {
                assert_eq!(out.len(), b64_len(n), "n = {n}");
            }
        }
    }

    // W02.
    #[test]
    fn key_length_ok_boundaries() {
        assert!(!key_length_ok(0));
        assert!(!key_length_ok(31));
        assert!(key_length_ok(32));
        assert!(key_length_ok(33));
        assert!(key_length_ok(usize::MAX));
        assert_eq!(MIN_KEY_LENGTH, 32);
    }

    // W03.
    #[test]
    fn check_kid_len_boundaries() {
        assert_eq!(check_kid_len(0), Err(KidError::Empty));
        assert_eq!(check_kid_len(1), Ok(()));
        assert_eq!(check_kid_len(255), Ok(()));
        assert_eq!(check_kid_len(256), Err(KidError::TooLong));
        assert_eq!(check_kid_len(usize::MAX), Err(KidError::TooLong));
        assert_eq!(MAX_KID_LEN, 255);
    }

    #[test]
    fn check_kid_len_counts_utf8_bytes() {
        // "é" is two UTF-8 bytes: 127 of them plus one ASCII byte is 255 bytes.
        let at_limit = format!("{}x", "é".repeat(127));
        assert_eq!(at_limit.len(), 255);
        assert_eq!(check_kid_len(at_limit.len()), Ok(()));
        let over_limit = "é".repeat(128);
        assert_eq!(over_limit.chars().count(), 128);
        assert_eq!(over_limit.len(), 256);
        assert_eq!(check_kid_len(over_limit.len()), Err(KidError::TooLong));
    }

    #[test]
    fn max_encoded_kid_len_is_b64_len_of_max_kid_len() {
        assert_eq!(MAX_ENCODED_KID_LEN, 340);
        let mut out = String::new();
        prim::b64_encode_into(&[0; MAX_KID_LEN], &mut out);
        assert_eq!(out.len(), MAX_ENCODED_KID_LEN);
        let mut out = String::new();
        prim::b64_encode_into(&[0; MAX_KID_LEN + 1], &mut out);
        assert!(out.len() > MAX_ENCODED_KID_LEN);
    }

    // W04.
    #[test]
    fn bytes_eq_cases() {
        assert!(bytes_eq(b"", b""));
        assert!(bytes_eq(b"abc", b"abc"));
        assert!(!bytes_eq(b"abc", b"abcd"));
        assert!(!bytes_eq(b"abcd", b"abc"));
        assert!(!bytes_eq(b"", b"a"));
        assert!(!bytes_eq(b"abc", b"abd"));
        assert!(!bytes_eq(b"xbc", b"abc"));
        let corpus: [&[u8]; 6] = [b"", b"a", b"b", b"ab", b"rs1", b"rs2"];
        for a in corpus {
            for b in corpus {
                assert_eq!(bytes_eq(a, b), a == b, "{a:?} {b:?}");
            }
        }
    }

    // W05.
    #[test]
    fn next_dot_cases() {
        assert_eq!(next_dot(b"", 0), 0);
        assert_eq!(next_dot(b"abc", 0), 3);
        assert_eq!(next_dot(b".abc", 0), 0);
        assert_eq!(next_dot(b".abc", 1), 4);
        assert_eq!(next_dot(b"abc.", 0), 3);
        assert_eq!(next_dot(b"abc.", 3), 3);
        assert_eq!(next_dot(b"abc.", 4), 4);
        assert_eq!(next_dot(b"a..b", 0), 1);
        assert_eq!(next_dot(b"a..b", 2), 2);
        assert_eq!(next_dot(b"a..b", 3), 4);
        // `start > len` returns `len`.
        assert_eq!(next_dot(b"", 5), 0);
        assert_eq!(next_dot(b"a.b", 10), 3);
        assert_eq!(next_dot(b"a.b", usize::MAX), 3);
    }

    // W06.
    #[test]
    fn component_count_cases() {
        let corpus: [&[u8]; 10] = [
            b"",
            b"abc",
            b".abc",
            b"abc.",
            b"a..b",
            b"...",
            b".",
            b"rs1.a.b",
            b"rs2.k.b.t",
            "é.ü".as_bytes(),
        ];
        let expected = [1, 1, 2, 2, 3, 4, 2, 3, 4, 2];
        for (s, n) in corpus.iter().zip(expected) {
            assert_eq!(component_count(s), n, "{s:?}");
            assert_eq!(component_count(s), split_dots(s).len(), "{s:?}");
        }
    }

    // W07.
    #[test]
    fn version_of_cases() {
        assert_eq!(version_of(b"rs1"), Some(Version::V1));
        assert_eq!(version_of(b"rs1.body.tag"), Some(Version::V1));
        assert_eq!(version_of(b"rs1."), Some(Version::V1));
        assert_eq!(version_of(b"rs2"), Some(Version::V2));
        assert_eq!(version_of(b"rs2.kid.body.tag"), Some(Version::V2));
        assert_eq!(version_of(b"rs3.a.b"), None);
        assert_eq!(version_of(b"rs1x.a.b"), None);
        assert_eq!(version_of(b"rs1x"), None);
        assert_eq!(version_of(b"xrs1.a.b"), None);
        assert_eq!(version_of(b"rs"), None);
        assert_eq!(version_of(b""), None);
        assert_eq!(version_of(b".rs1"), None);
        assert_eq!(version_of(b"RS1.a.b"), None);
    }

    fn parse_corpus() -> Vec<&'static [u8]> {
        vec![
            b"",
            b".",
            b"..",
            b"...",
            b"....",
            b"rs1",
            b"rs1.a",
            b"rs1.a.b",
            b"rs1.a.b.c",
            b"rs1.a.b.c.d",
            b"rs1..",
            b"rs1...",
            b"rs2",
            b"rs2.k",
            b"rs2.k.b",
            b"rs2.k.b.t",
            b"rs2.k.b.t.x",
            b"rs2...",
            b"rs2....",
            b"rs3.a.b",
            b"rs3.k.b.t",
            b"rs1x.a.b",
            b"rs2x.k.b.t",
            b".rs1.a.b",
        ]
    }

    // W08.
    #[test]
    fn parse_rs1_cases() {
        assert_eq!(parse_rs1(b"rs1.a"), None);
        assert_eq!(
            parse_rs1(b"rs1.body.tag"),
            Some(Rs1Parts {
                body: b"body",
                tag: b"tag"
            })
        );
        assert_eq!(parse_rs1(b"rs1.a.b.c"), None);
        assert_eq!(parse_rs1(b"rs1.a.b.c.d"), None);
        assert_eq!(parse_rs1(b"rs2.a.b"), None);
        assert_eq!(
            parse_rs1(b"rs1.."),
            Some(Rs1Parts {
                body: b"",
                tag: b""
            })
        );
        assert_eq!(parse_rs1(b".."), None);
        for s in parse_corpus() {
            let parts = split_dots(s);
            let expected = (parts.len() == 3 && parts[0] == VERSION_V1).then(|| Rs1Parts {
                body: parts[1],
                tag: parts[2],
            });
            assert_eq!(parse_rs1(s), expected, "{s:?}");
        }
    }

    // W09.
    #[test]
    fn parse_rs2_cases() {
        assert_eq!(parse_rs2(b"rs2.k"), None);
        assert_eq!(parse_rs2(b"rs2.k.b"), None);
        assert_eq!(
            parse_rs2(b"rs2.kid.body.tag"),
            Some(Rs2Parts {
                kid: b"kid",
                body: b"body",
                tag: b"tag"
            })
        );
        assert_eq!(parse_rs2(b"rs2.k.b.t.x"), None);
        assert_eq!(parse_rs2(b"rs1.k.b.t"), None);
        assert_eq!(
            parse_rs2(b"rs2..."),
            Some(Rs2Parts {
                kid: b"",
                body: b"",
                tag: b""
            })
        );
        assert_eq!(parse_rs2(b"..."), None);
        for s in parse_corpus() {
            let parts = split_dots(s);
            let expected = (parts.len() == 4 && parts[0] == VERSION_V2).then(|| Rs2Parts {
                kid: parts[1],
                body: parts[2],
                tag: parts[3],
            });
            assert_eq!(parse_rs2(s), expected, "{s:?}");
        }
    }

    // W10.
    #[test]
    fn transcript_v1_layout() {
        let mut expected = DOMAIN_V1.to_vec();
        expected.extend_from_slice(&[0; 8]);
        assert_eq!(transcript_v1(b"", b""), expected);

        let mut expected = DOMAIN_V1.to_vec();
        expected.extend_from_slice(&[0, 0, 0, 0, 0, 0, 0, 2]);
        expected.extend_from_slice(b"ad");
        expected.extend_from_slice(b"body");
        assert_eq!(transcript_v1(b"ad", b"body"), expected);

        // The length prefix separates associated data from body.
        assert_ne!(transcript_v1(b"a", b"bc"), transcript_v1(b"ab", b"c"));
        assert_ne!(transcript_v1(b"ad", b"x"), transcript_v1(b"ad", b"y"));
        assert_ne!(transcript_v1(b"x", b"body"), transcript_v1(b"y", b"body"));
    }

    // W11.
    #[test]
    fn transcript_v2_layout() {
        let mut expected = DOMAIN_V2.to_vec();
        expected.extend_from_slice(&[0; 8]);
        expected.extend_from_slice(&[0; 8]);
        assert_eq!(transcript_v2(b"", b"", b""), expected);

        let mut expected = DOMAIN_V2.to_vec();
        expected.extend_from_slice(&[0, 0, 0, 0, 0, 0, 0, 3]);
        expected.extend_from_slice(b"kid");
        expected.extend_from_slice(&[0, 0, 0, 0, 0, 0, 0, 2]);
        expected.extend_from_slice(b"ad");
        expected.extend_from_slice(b"body");
        assert_eq!(transcript_v2(b"kid", b"ad", b"body"), expected);

        let base = transcript_v2(b"k", b"a", b"b");
        assert_ne!(base, transcript_v2(b"x", b"a", b"b"));
        assert_ne!(base, transcript_v2(b"k", b"x", b"b"));
        assert_ne!(base, transcript_v2(b"k", b"a", b"x"));
        assert_ne!(
            transcript_v2(b"ka", b"", b"b"),
            transcript_v2(b"k", b"a", b"b")
        );
        // Domain separation between the two versions: same length, different bytes.
        assert_eq!(DOMAIN_V1.len(), DOMAIN_V2.len());
        assert_ne!(DOMAIN_V1, DOMAIN_V2);
    }

    /// Section 3: HMAC over the transcript equals HMAC with incremental
    /// `update` calls over the same bytes (the removed `mac_v1`/`mac_v2`).
    #[test]
    fn transcripts_match_incremental_hmac() {
        use hmac::{Hmac, KeyInit, Mac};
        use sha2::Sha256;

        let key = b"0123456789abcdef0123456789abcdef";
        for (kid, ad, body) in [
            (&b""[..], &b""[..], &b""[..]),
            (b"kid-\xc3\xa9", b"ad", b"\0\0\0\0\0\0\0\0payload"),
            (b"k", b"x.y", b"\x00\xff\x2e"),
        ] {
            let mut mac = <Hmac<Sha256> as KeyInit>::new_from_slice(key).unwrap();
            mac.update(DOMAIN_V1);
            mac.update(&(ad.len() as u64).to_be_bytes());
            mac.update(ad);
            mac.update(body);
            let v1: [u8; 32] = mac.finalize().into_bytes().into();
            assert_eq!(prim::hmac_sha256(key, &transcript_v1(ad, body)), v1);

            let mut mac = <Hmac<Sha256> as KeyInit>::new_from_slice(key).unwrap();
            mac.update(DOMAIN_V2);
            mac.update(&(kid.len() as u64).to_be_bytes());
            mac.update(kid);
            mac.update(&(ad.len() as u64).to_be_bytes());
            mac.update(ad);
            mac.update(body);
            let v2: [u8; 32] = mac.finalize().into_bytes().into();
            assert_eq!(prim::hmac_sha256(key, &transcript_v2(kid, ad, body)), v2);
        }
    }

    // W12.
    #[test]
    fn decode_expiry_is_signed_big_endian() {
        assert_eq!(decode_expiry([0; 8]), 0);
        assert_eq!(decode_expiry([0, 0, 0, 0, 0, 0, 0, 1]), 1);
        assert_eq!(decode_expiry([0, 0, 0, 0, 0, 0, 1, 0]), 256);
        assert_eq!(decode_expiry([0xff; 8]), -1);
        assert_eq!(decode_expiry([0x80, 0, 0, 0, 0, 0, 0, 0]), i64::MIN);
        assert_eq!(
            decode_expiry([0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
            i64::MAX
        );
        for v in [
            0,
            1,
            -1,
            1_700_000_090_000,
            -1_700_000_090_000,
            i64::MIN,
            i64::MAX,
        ] {
            assert_eq!(decode_expiry(v.to_be_bytes()), v);
            assert_eq!(
                decode_expiry(v.to_be_bytes()),
                i64::from_be_bytes(v.to_be_bytes())
            );
        }
    }

    // W13.
    #[test]
    fn is_expired_cases() {
        // 0 never expires.
        assert!(!is_expired(0, i64::MIN));
        assert!(!is_expired(0, 0));
        assert!(!is_expired(0, i64::MAX));
        // `now` before, equal to, after expiry.
        assert!(!is_expired(1000, 999));
        assert!(!is_expired(1000, 1000));
        assert!(is_expired(1000, 1001));
        // Negative expiry compares as a signed value.
        assert!(!is_expired(-5, -6));
        assert!(!is_expired(-5, -5));
        assert!(is_expired(-5, -4));
        assert!(is_expired(-5, 0));
        assert!(!is_expired(i64::MAX, i64::MAX));
        assert!(is_expired(i64::MIN, i64::MIN + 1));
    }

    // W14.
    #[test]
    fn open_frame_short_bodies() {
        for len in 0..EXPIRY_LEN {
            assert_eq!(
                open_frame(&vec![0; len], 0),
                Err(FrameError::TooShort),
                "len = {len}"
            );
        }
        assert_eq!(open_frame(&[0; 8], i64::MAX), Ok(&[][..]));
    }

    #[test]
    fn open_frame_expiry() {
        let body = frame(1000, b"payload");
        assert_eq!(open_frame(&body, 999), Ok(&b"payload"[..]));
        assert_eq!(open_frame(&body, 1000), Ok(&b"payload"[..]));
        assert_eq!(open_frame(&body, 1001), Err(FrameError::Expired));

        let negative = frame(-5, b"p");
        assert_eq!(open_frame(&negative, -6), Ok(&b"p"[..]));
        assert_eq!(open_frame(&negative, -5), Ok(&b"p"[..]));
        assert_eq!(open_frame(&negative, -4), Err(FrameError::Expired));

        let never = frame(0, b"p");
        assert_eq!(open_frame(&never, i64::MAX), Ok(&b"p"[..]));
        // Exactly 8 bytes, expired.
        assert_eq!(open_frame(&frame(1, b""), 2), Err(FrameError::Expired));
    }

    // W15.
    #[test]
    fn frame_layout() {
        assert_eq!(frame(0, b""), vec![0; 8]);
        assert_eq!(frame(1, b"x"), b"\0\0\0\0\0\0\0\x01x".to_vec());
        let mut expected = vec![0xff; 8];
        expected.extend_from_slice(b"ab");
        assert_eq!(frame(-1, b"ab"), expected);
        for e in [0, 1, -1, i64::MIN, i64::MAX, 1_700_000_090_000] {
            let mut expected = e.to_be_bytes().to_vec();
            expected.extend_from_slice(b"payload");
            assert_eq!(frame(e, b"payload"), expected);
        }
    }

    /// `open_frame (frame e p) now = Ok p` when `¬ is_expired e now`, else `Expired`.
    #[test]
    fn frame_open_frame_roundtrip() {
        let payloads: [&[u8]; 3] = [b"", b"payload", &[0, 255, 46]];
        let times = [i64::MIN, -5, -1, 0, 1, 999, 1000, 1001, i64::MAX];
        for e in times {
            for now in times {
                for p in payloads {
                    let body = frame(e, p);
                    let expected = if is_expired(e, now) {
                        Err(FrameError::Expired)
                    } else {
                        Ok(p)
                    };
                    assert_eq!(open_frame(&body, now), expected, "e={e} now={now}");
                }
            }
        }
    }

    /// RFC 4231 HMAC-SHA256 test cases 1-7 through `prim`. Case 5 specifies a
    /// 128-bit truncated output: the full tag must start with it, and
    /// `hmac_sha256_verify` must reject the truncated tag (wrong length).
    #[test]
    fn rfc4231_hmac_sha256_vectors() {
        let long_key = vec![0xaa; 131];
        let cases: [(Vec<u8>, Vec<u8>, &str); 7] = [
            (
                vec![0x0b; 20],
                b"Hi There".to_vec(),
                "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7",
            ),
            (
                b"Jefe".to_vec(),
                b"what do ya want for nothing?".to_vec(),
                "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843",
            ),
            (
                vec![0xaa; 20],
                vec![0xdd; 50],
                "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe",
            ),
            (
                (1..=25).collect(),
                vec![0xcd; 50],
                "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b",
            ),
            (
                vec![0x0c; 20],
                b"Test With Truncation".to_vec(),
                "a3b6167473100ee06e0c796c2955552b",
            ),
            (
                long_key.clone(),
                b"Test Using Larger Than Block-Size Key - Hash Key First".to_vec(),
                "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54",
            ),
            (
                long_key,
                b"This is a test using a larger than block-size key and a larger than \
                  block-size data. The key needs to be hashed before being used by the \
                  HMAC algorithm."
                    .to_vec(),
                "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2",
            ),
        ];
        for (i, (key, data, expected)) in cases.iter().enumerate() {
            let expected = hex(expected);
            let tag = prim::hmac_sha256(key, data);
            if expected.len() == TAG_LEN {
                assert_eq!(tag.to_vec(), expected, "case {}", i + 1);
                assert!(
                    prim::hmac_sha256_verify(key, data, &expected),
                    "case {}",
                    i + 1
                );
                let mut flipped = expected.clone();
                flipped[TAG_LEN - 1] ^= 1;
                assert!(
                    !prim::hmac_sha256_verify(key, data, &flipped),
                    "case {}",
                    i + 1
                );
            } else {
                // Case 5: truncated output.
                assert_eq!(&tag[..expected.len()], &expected[..], "case {}", i + 1);
                assert!(
                    !prim::hmac_sha256_verify(key, data, &expected),
                    "case {}",
                    i + 1
                );
                assert!(prim::hmac_sha256_verify(key, data, &tag), "case {}", i + 1);
            }
        }
    }

    #[test]
    fn hmac_sha256_verify_rejects_wrong_length_tags() {
        let key = [7; 32];
        let tag = prim::hmac_sha256(&key, b"msg");
        assert!(prim::hmac_sha256_verify(&key, b"msg", &tag));
        assert!(!prim::hmac_sha256_verify(&key, b"msg", &[]));
        assert!(!prim::hmac_sha256_verify(&key, b"msg", &tag[..31]));
        let mut longer = tag.to_vec();
        longer.push(0);
        assert!(!prim::hmac_sha256_verify(&key, b"msg", &longer));
        // Any key length is accepted, including empty.
        assert!(prim::hmac_sha256_verify(
            b"",
            b"msg",
            &prim::hmac_sha256(b"", b"msg")
        ));
    }

    /// RFC 4648 Section 10 test vectors (the URL-safe alphabet agrees on them).
    #[test]
    fn rfc4648_base64url_vectors() {
        let vectors: [(&[u8], &str); 7] = [
            (b"", ""),
            (b"f", "Zg"),
            (b"fo", "Zm8"),
            (b"foo", "Zm9v"),
            (b"foob", "Zm9vYg"),
            (b"fooba", "Zm9vYmE"),
            (b"foobar", "Zm9vYmFy"),
        ];
        for (raw, encoded) in vectors {
            let mut out = String::new();
            prim::b64_encode_into(raw, &mut out);
            assert_eq!(out, encoded);
            assert_eq!(prim::b64_decode(encoded.as_bytes()), Some(raw.to_vec()));
        }
    }

    #[test]
    fn base64url_alphabet_and_append() {
        // URL-safe alphabet: 62 is '-' and 63 is '_' (not '+' and '/').
        let mut out = String::from("prefix.");
        prim::b64_encode_into(&[0xfb, 0xef, 0xbe], &mut out);
        prim::b64_encode_into(&[0xff, 0xff, 0xff], &mut out);
        prim::b64_encode_into(&[0xfb, 0xff], &mut out);
        assert_eq!(out, "prefix.----____-_8");
        assert_eq!(prim::b64_decode(b"----"), Some(vec![0xfb, 0xef, 0xbe]));
        assert_eq!(prim::b64_decode(b"____"), Some(vec![0xff, 0xff, 0xff]));
        assert_eq!(prim::b64_decode(b"++++"), None);
        assert_eq!(prim::b64_decode(b"////"), None);
    }

    #[test]
    fn base64url_decode_is_strict() {
        // Padding is rejected.
        assert_eq!(prim::b64_decode(b"Zg=="), None);
        assert_eq!(prim::b64_decode(b"Zm8="), None);
        assert_eq!(prim::b64_decode(b"Zm9vYg=="), None);
        // Non-canonical trailing bits are rejected.
        assert_eq!(prim::b64_decode(b"Zh"), None);
        assert_eq!(prim::b64_decode(b"Zm9"), None);
        assert_eq!(prim::b64_decode(b"_w"), Some(vec![0xff]));
        assert_eq!(prim::b64_decode(b"_x"), None);
        // Impossible length (1 mod 4) and invalid symbols.
        assert_eq!(prim::b64_decode(b"Z"), None);
        assert_eq!(prim::b64_decode(b"Zm9vY"), None);
        assert_eq!(prim::b64_decode(b"!!!!"), None);
        assert_eq!(prim::b64_decode(b"Zm 9v"), None);
        assert_eq!(prim::b64_decode(b"Zm9v\n"), None);
    }

    #[test]
    fn base64url_roundtrip() {
        let all: Vec<u8> = (0..=255).collect();
        for n in 0..all.len() {
            let mut out = String::new();
            prim::b64_encode_into(&all[..n], &mut out);
            assert!(
                out.bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
            );
            assert_eq!(prim::b64_decode(out.as_bytes()), Some(all[..n].to_vec()));
        }
    }
}
