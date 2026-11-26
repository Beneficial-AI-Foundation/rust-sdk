/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Aeneas
public import Rmcp.Types
public import Rmcp.FunsExternal
public import Defs.Wire
public import Defs.RequestState

@[expose] public section

/-!
# Codec state, keys and expected opening results (E07–E11)

The vocabulary of the seal and open statements E07–E11 and E09a (plan Section 2.2): key lookup
in a keyring, the codec-state predicate of plan Section 4 ("Codec state") and its fallback
clause, the rs1 fallback acceptance of E09a, and the expected results of opening an `rs1` token
(E09), an `rs2` token (E10) and a token of either version (E11). They are stated on byte lists
with the external models `ExtModel.b64Decode`, `ExtModel.strOfBytes?` and `ExtModel.hmacSha256`
(`trusted/Rmcp/FunsExternal.lean`) and the `Defs.Wire` vocabulary (`components`, `transcriptV1`,
`transcriptV2`, `bodyExpiry`, `Expired`). The style guide names this file for the codec-state
invariant ("Specification Definition Guidelines").
Signed off by the spec owner on 2026-11-23 with the E07–E11 statements (the S05 evidence (git history at 223ff12),
"E batch part 2").

Rust source: `crates/rmcp/src/model/request_state.rs` (and `request_state_wire.rs` where named)
in the patched copy (patch 01 on origin/main 7caec76, D2 fallback 2026-11-23); line numbers
below refer to it (its non-test lines are those of `9bd8144`) up to the end of `resultBytes`. The
R09–R15 sections from "`InvalidKeyring` messages of the keyring builders" on ("Sealing",
"Keyring configuration" and "Abbreviations used by the public statements") cite the patches
01–03 copy as "patched", origin/main `7caec76` as "upstream", and the patch-01 copy only where
they say "patch-01 copy".

The section "Abbreviations used by the public statements" at the end of this file was added by
the readability rewrite of 2026-11-25 of `Specs/Model/RequestState.lean`. That rewrite changes
the text of signed-off statements and was **signed off by the spec owner on 2026-11-25**; each
rewritten statement's type is definitionally equal to its text at commit `8debe97` (checked by
`rfl`; evidence in `formal/docs/STATUS.md`, "Readability rewrite of R01–R15"). No definition above that section changes.
-/

namespace Defs.CodecState

open Aeneas.Std

open rmcp.model.request_state (RequestStateCodec Keys SealMode RequestStateError)
open Defs.Wire
open Defs.RequestState (StrIs kidEmptyMsg kidTooLongMsg)
open Result (ok)

/-- The key table of a keyring codec: the translated `HashMap<String, Zeroizing<Vec<u8>>>` of
`Keys::Ring { keys, .. }` (request_state.rs, lines 228–235; plan Section 4, "Standard library":
an association list `entries`). -/
abbrev KeyTable : Type :=
  std.collections.hash.map.HashMap String (zeroize.Zeroizing (alloc.vec.Vec U8))
    std.hash.random.RandomState alloc.alloc.Global

/-- The key ids of a key table, in table order. -/
def keyIds (keys : KeyTable) : List String := keys.entries.map Prod.fst

/-- The key bytes stored under `kid`, or `none` if `kid` is not a key id: the value of the first
entry whose key equals `kid`. This is the model of `keys.get(kid)` (request_state.rs lines 652
and 680; `std.collections.hash.map.HashMap.get` in `trusted/Rmcp/FunsExternal.lean` and its law
`HashMap.get_string_spec`), with the `Zeroizing` wrapper removed (its `deref` is the identity,
plan Section 4). With pairwise distinct key ids (`CodecValid`) it is the key stored under
`kid`. -/
def lookupKey (keys : KeyTable) (kid : String) : Option (List U8) :=
  (keys.entries.find? (fun e => decide (e.1 = kid))).map (fun e => e.2.inner.val)

/-- The key id of a seal mode (`SealMode::Rs1 { key_id }`, `SealMode::Rs2 { key_id }`,
request_state.rs lines 238–241). -/
def sealModeKid : SealMode → String
  | .Rs1 kid => kid
  | .Rs2 kid => kid

/-- Every rs1 fallback id is a key id of the table. This is the first clause of the codec-state
predicate (plan Section 4, "Codec state"). It is sufficient for
`keys.get(kid).expect("validated rs1 fallback key")` (request_state.rs line 652) never to panic
while `rs1_fallbacks_verify` tries every fallback (the premise `h_known` of E09a,
`rmcp.model.request_state.RequestStateCodec.rs1_fallbacks_verify_spec`). It is also necessary, by an
argument from the code that is not proved: the loop (lines 651–655) has no early exit and looks
up every fallback, so the `expect` panics on the first id that is not a key. -/
def FallbacksKnown (keys : KeyTable) (rs1_fallbacks : List String) : Prop :=
  ∀ kid ∈ rs1_fallbacks, kid ∈ keyIds keys

/-- `FallbacksKnown` for the keyring of a codec; a single-key codec has no fallbacks and
satisfies it. This is the part of the codec-state predicate that `open_rs1_at` (E09) and
`open_at` (E11) need (request_state.rs lines 628–635 and 652). -/
def CodecFallbacksKnown (codec : RequestStateCodec) : Prop :=
  match codec.keys with
  | .Single _ => True
  | .Ring keys _ rs1_fallbacks => FallbacksKnown keys rs1_fallbacks.val

/-- **Codec-state predicate** (plan Section 4, "Codec state"; Section 2.3, consequences: it is
permanently a hypothesis, because the constructors that establish it are excluded). For a
keyring codec (`Keys::Ring`, request_state.rs lines 228–235):

* the key ids are pairwise distinct (a Rust `HashMap` has no two equal keys, and
  `new_with_keyring` rejects duplicates, lines 333–340; the translated `HashMap` does not carry
  this, `trusted/Rmcp/TypesExternal.lean`);
* every rs1 fallback id is a key id (`with_rs1_signing`, lines 384–396, and
  `with_rs1_fallback`, lines 421–428, push only ids that pass `keys.contains_key`);
* the seal-mode key id is a key id (`new_with_keyring`, lines 349–363; `with_rs1_signing`,
  lines 384–393);
* every key has at least `minKeyLength = 32` bytes and every key id passes E04 (UTF-8 byte
  length in `1..=255`) (`new_with_keyring` calls `validate_config_kid` and
  `validate_key_length` on every entry, lines 331–332, and `validate_config_kid` alone on the
  active id, line 350).

A single-key codec is unconstrained: `new_unchecked` (lines 286–290) and the deprecated `new`
(line 278) accept a key of any length, so "every key is at least 32 bytes" of plan Section 4
holds only for keyring codecs and for `try_new` (lines 298–304). Both the unconstrained
single-key case and the distinct-ids clause are spec-owner decisions (2026-11-23; plan Section 4,
"Codec state"). A keyring is also nonempty (lines 343–347), which follows from the
seal-mode clause.

The opening statements take only the clauses they need (spec-owner decision): E09 and E11
`CodecFallbacksKnown`, E09a `FallbacksKnown`, E10 none. `CodecValid codec` implies
`CodecFallbacksKnown codec` (its second clause), so the round trips can assume `CodecValid`. -/
def CodecValid (codec : RequestStateCodec) : Prop :=
  match codec.keys with
  | .Single _ => True
  | .Ring keys seal_mode rs1_fallbacks =>
    (keyIds keys).Nodup ∧
    FallbacksKnown keys rs1_fallbacks.val ∧
    sealModeKid seal_mode ∈ keyIds keys ∧
    ∀ e ∈ keys.entries,
      Defs.Wire.minKeyLength ≤ e.2.inner.val.length ∧
      1 ≤ e.1.utf8ByteSize ∧ e.1.utf8ByteSize ≤ Defs.Wire.maxKidLen

/-- `key` verifies `tag` over `msg`: the tag equals, as a byte list, the HMAC-SHA256 of `msg`
under `key` (plan Section 4, HMAC row: `hmac_sha256_verify k m t := ok (t = hmacSha256 k m)`;
a tag of a length other than 32 never verifies). -/
def TagVerifies (key msg tag : List U8) : Prop :=
  tag = (ExtModel.hmacSha256 key msg).val

instance (key msg tag : List U8) : Decidable (TagVerifies key msg tag) :=
  inferInstanceAs (Decidable (tag = (ExtModel.hmacSha256 key msg).val))

/-- **rs1 fallback acceptance** (plan Section 2.2, E09a): some rs1 fallback id names a key of
the table that verifies `tag` over `msg`. It does not say which fallback matched, and says
nothing about the order in which they are tried or about timing (request_state.rs line 643,
plan Section 3: trying every fallback is a timing measure the functional statement does not
cover). False when there is no fallback. -/
def Rs1Verifies (keys : KeyTable) (rs1_fallbacks : List String) (msg tag : List U8) : Prop :=
  ∃ kid ∈ rs1_fallbacks, ∃ key ∈ lookupKey keys kid, TagVerifies key msg tag

instance (keys : KeyTable) (rs1_fallbacks : List String) (msg tag : List U8) :
    Decidable (Rs1Verifies keys rs1_fallbacks msg tag) :=
  inferInstanceAs
    (Decidable (∃ kid ∈ rs1_fallbacks, ∃ key ∈ lookupKey keys kid, TagVerifies key msg tag))

/-- Which `rs1` tags a codec accepts over `msg` (request_state.rs lines 628–635): a single-key
codec accepts a tag that its key verifies; a keyring codec accepts a tag that some rs1 fallback
key verifies (`Rs1Verifies`). -/
def Rs1Accepts (codec : RequestStateCodec) (msg tag : List U8) : Prop :=
  match codec.keys with
  | .Single key => TagVerifies key.inner.val msg tag
  | .Ring keys _ rs1_fallbacks => Rs1Verifies keys rs1_fallbacks.val msg tag

instance (codec : RequestStateCodec) (msg tag : List U8) : Decidable (Rs1Accepts codec msg tag) :=
  match codec with
  | ⟨.Single key⟩ => inferInstanceAs (Decidable (TagVerifies key.inner.val msg tag))
  | ⟨.Ring keys _ rs1_fallbacks⟩ =>
    inferInstanceAs (Decidable (Rs1Verifies keys rs1_fallbacks.val msg tag))

/-- A keyring codec with no rs1 fallback, which rejects every `rs1` token with `UnknownKeyId`
before decoding (request_state.rs lines 617–621; plan Section 3, "E09 — error order",
step 2). -/
def noRs1Fallback (codec : RequestStateCodec) : Bool :=
  match codec.keys with
  | .Single _ => false
  | .Ring _ _ rs1_fallbacks => rs1_fallbacks.val.isEmpty

/-- The maximum length of the Base64 encoding of a key id, `MAX_ENCODED_KID_LEN = 340`
(request_state_wire.rs line 23; request_state.rs line 84 is an alias of it): the unpadded
encoding of `maxKidLen = 255` bytes. -/
def maxEncodedKidLen : Nat := 340

/-- **Expected result of E01** on an authenticated body, as an `Except` over byte lists (plan
Section 2.2, E01; the signed-off E01 statement): `MalformedFormat` below `expiryLen = 8` bytes,
otherwise `Expired` if the body's expiry has passed at `now`, otherwise the bytes after the
first 8. -/
def openBody (body : List U8) (now : Int) : Except RequestStateError (List U8) :=
  if body.length < expiryLen then .error .MalformedFormat
  else if Expired (bodyExpiry body) now then .error .Expired
  else .ok (body.drop expiryLen)

/-- **Expected result of E09** (`open_rs1_at`) for the token bytes `token`, associated data `ad`
and time `now`, in the error order of plan Section 3 ("E09 — error order"):

1. the token does not split on `.` into `["rs1", b, t]` → `MalformedFormat` (W08; lines
   613–615);
2. a keyring codec with no rs1 fallback → `UnknownKeyId`, before any decoding (lines 617–621);
3. `b` is not canonical unpadded Base64url → `InvalidEncoding`; then the same for `t` (lines
   623, 624);
4. the decoded tag is not accepted over `transcriptV1 ad body` (`Rs1Accepts`) →
   `IntegrityCheckFailed` (lines 627–638);
5. otherwise E01 on the decoded body (line 640). -/
def openRs1 (codec : RequestStateCodec) (token ad : List U8) (now : Int) :
    Except RequestStateError (List U8) :=
  match components token with
  | [v, bodyB64, tagB64] =>
    if v ≠ versionV1 then .error .MalformedFormat
    else if noRs1Fallback codec then .error .UnknownKeyId
    else
      match ExtModel.b64Decode bodyB64, ExtModel.b64Decode tagB64 with
      | none, _ => .error .InvalidEncoding
      | some _, none => .error .InvalidEncoding
      | some body, some tag =>
        if Rs1Accepts codec (transcriptV1 ad body) tag then openBody body now
        else .error .IntegrityCheckFailed
  | _ => .error .MalformedFormat

/-- **Expected result of E10** (`open_rs2_at`) for the token bytes `token`, associated data `ad`
and time `now`, in the error order of plan Section 3 ("E10 — error order"):

1. the token does not split on `.` into `["rs2", k, b, t]` → `MalformedFormat` (W09; lines
   665–667);
2. `k` is longer than `maxEncodedKidLen = 340` bytes → `InvalidKeyId` (lines 669–671);
3. `k` is not canonical unpadded Base64url → `InvalidEncoding` (line 672);
4. the decoded kid has 0 or more than `maxKidLen = 255` bytes → `InvalidKeyId` (W03; lines
   673–675); it is not UTF-8 → `InvalidKeyId` (line 676);
5. a single-key codec → `UnknownKeyId` (line 679); a keyring with no key under that kid →
   `UnknownKeyId` (line 680);
6. `b` is not canonical Base64url → `InvalidEncoding`; then the same for `t` (lines 683, 684);
7. the decoded tag does not verify over `transcriptV2 kid ad body` under the kid's key →
   `IntegrityCheckFailed` (lines 687–690); the transcript binds the decoded kid bytes, `ad`
   and the body;
8. otherwise E01 on the decoded body (line 692). -/
def openRs2 (codec : RequestStateCodec) (token ad : List U8) (now : Int) :
    Except RequestStateError (List U8) :=
  match components token with
  | [v, kidB64, bodyB64, tagB64] =>
    if v ≠ versionV2 then .error .MalformedFormat
    else if maxEncodedKidLen < kidB64.length then .error .InvalidKeyId
    else
      match ExtModel.b64Decode kidB64 with
      | none => .error .InvalidEncoding
      | some kid =>
        if kid.length = 0 ∨ maxKidLen < kid.length then .error .InvalidKeyId
        else
          match ExtModel.strOfBytes? kid with
          | none => .error .InvalidKeyId
          | some kidStr =>
            match codec.keys with
            | .Single _ => .error .UnknownKeyId
            | .Ring keys _ _ =>
              match lookupKey keys kidStr with
              | none => .error .UnknownKeyId
              | some key =>
                match ExtModel.b64Decode bodyB64, ExtModel.b64Decode tagB64 with
                | none, _ => .error .InvalidEncoding
                | some _, none => .error .InvalidEncoding
                | some body, some tag =>
                  if TagVerifies key (transcriptV2 kid ad body) tag then openBody body now
                  else .error .IntegrityCheckFailed
  | _ => .error .MalformedFormat

/-- **Expected result of E11** (`open_at`, request_state.rs lines 559–570): dispatch on the first
`.`-component of the token (W07, line 565): `"rs1"` → `openRs1` (line 566), `"rs2"` →
`openRs2` (line 567), anything else → `MalformedFormat` (line 568). The result of the chosen
opener is passed through unchanged. -/
def openAt (codec : RequestStateCodec) (token ad : List U8) (now : Int) :
    Except RequestStateError (List U8) :=
  if (components token).head? = some versionV1 then openRs1 codec token ad now
  else if (components token).head? = some versionV2 then openRs2 codec token ad now
  else .error .MalformedFormat

/-- The translated result of an opener as an `Except` over byte lists: `Ok v ↦ .ok v.val`,
`Err e ↦ .error e`. Used to compare `open_rs1_at`, `open_rs2_at` and `open_at` with `openRs1`,
`openRs2` and `openAt`.

**It loses no information** (spec-owner decision 2026-11-23): `resultBytes` is injective, so
`resultBytes result = x` pins down the whole `core.result.Result (alloc.vec.Vec U8)
RequestStateError` value `result`, as an equation on `result` itself would.

* `Err e ↦ .error e` keeps the error value itself, of the same type `RequestStateError`: every
  variant, with all of its fields (`KeyTooShort { minimum, actual }`, the `&'static str` of
  `InvalidKeyring`, the payloads of `Serialization`/`Deserialization`, request_state.rs lines
  94–138), is passed through unchanged, so two results with different errors (or different
  fields) have different images.
* `Ok v ↦ .ok v.val` keeps the success bytes: the Aeneas `alloc.vec.Vec U8` is the subtype
  `{ l : List U8 // l.length ≤ Usize.max }` (`Aeneas/Std/Vec.lean`), so `v.val` determines `v`
  (`Subtype.ext`).
* An `Ok` and an `Err` have images `.ok _` and `.error _`, which differ.

The only `Except` values that are not images are `.ok l` with `l.length > Usize.max`; the
expected results never produce one (their success value is a suffix of a decoded component of the
token, which is a slice), and an equation with such a value would be unprovable, not weaker. The
four-case injectivity proof is written out in the S05 evidence (git history at 223ff12) ("E batch part 2",
fix round 2); `Defs` holds no proofs. -/
def resultBytes (r : core.result.Result (alloc.vec.Vec U8) RequestStateError) :
    Except RequestStateError (List U8) :=
  match r with
  | .Ok v => .ok v.val
  | .Err e => .error e

/-! ### `InvalidKeyring` messages of the keyring builders -/

/-- The message of `InvalidKeyring` from `with_rs1_signing` on a single-key codec (patched line
377, upstream 387). -/
def rs1SigningNeedsKeyringMsg : String := "rs1 transitional signing requires a keyring"

/-- The message of `InvalidKeyring` from `with_rs1_signing` for an id that is not a key id
(patched line 386, upstream 396). -/
def rs1SigningKidMissingMsg : String := "rs1 signing key id is not present in the keyring"

/-- The message of `InvalidKeyring` from `with_rs1_fallback` on a single-key codec (patched line
414, upstream 424). -/
def rs1FallbackNeedsKeyringMsg : String := "rs1 fallbacks require a keyring"

/-- The message of `InvalidKeyring` from `with_rs1_fallback` for an id that is not a key id
(patched line 423, upstream 433). -/
def rs1FallbackKidMissingMsg : String := "rs1 fallback key id is not present in the keyring"

/-- The message of `InvalidKeyring` from `new_with_keyring` for a repeated key id (patched line
338, upstream 348). -/
def duplicateKidMsg : String := "duplicate key id"

/-- The message of `InvalidKeyring` from `new_with_keyring` for no keys (patched line 345,
upstream 355). -/
def emptyKeyringMsg : String := "keyring must contain at least one key"

/-- The message of `InvalidKeyring` from `new_with_keyring` when the active id is not a key id
(patched line 353, upstream 363). -/
def activeKidMissingMsg : String := "active key id is not present in the keyring"

/-! ### Sealing -/

/-- The whole milliseconds of a `Duration`, `Duration::as_millis` (`core/src/time.rs`, lines
601–604: `secs * 1000 + nanos / 1_000_000`). -/
def durationMillis (d : core.time.Duration) : Nat :=
  d.secs.val * 1000 + d.nanos.val / 1000000

/-- **Expiry of a sealed token** (patched lines 534–538, upstream 541–544): `0` without a
time-to-live; with a time-to-live `d`, `now_ms.saturating_add(d.as_millis().min(i64::MAX as u128)
as i64)`, i.e. `now + min(ms, i64::MAX)` clamped to the `i64` range. The cast `as i64` is exact
because its argument is at most `i64::MAX`. The bounds are the Aeneas constants `I64.max`
(`2^63 - 1`) and `I64.min` (`-2^63`) of `Aeneas/Std/Scalar/Core.lean`. -/
def sealExpiry (ttl : Option core.time.Duration) (now : Int) : Int :=
  match ttl with
  | none => 0
  | some d => max I64.min (min I64.max (now + min (durationMillis d : Int) I64.max))

/-- The `rs1` token of `body` under `key` and associated data `ad`, as UTF-8 bytes:
`"rs1." ++ b64(body) ++ "." ++ b64(tag)` with `tag = HMAC-SHA256(key, transcriptV1 ad body)`
(plan Section 2.2, E07; `seal_rs1`, patched lines 576–587). -/
def tokenV1 (key ad body : List U8) : List U8 :=
  versionV1 ++ [dot] ++ ExtModel.b64 body ++ [dot] ++
    ExtModel.b64 (ExtModel.hmacSha256 key (transcriptV1 ad body)).val

/-- The `rs2` token of `body` under key id bytes `kid`, `key` and `ad`, as UTF-8 bytes:
`"rs2." ++ b64(kid) ++ "." ++ b64(body) ++ "." ++ b64(tag)` with
`tag = HMAC-SHA256(key, transcriptV2 kid ad body)` (plan Section 2.2, E08; `seal_rs2`, patched
lines 589–609). -/
def tokenV2 (kid key ad body : List U8) : List U8 :=
  versionV2 ++ [dot] ++ ExtModel.b64 kid ++ [dot] ++ ExtModel.b64 body ++ [dot] ++
    ExtModel.b64 (ExtModel.hmacSha256 key (transcriptV2 kid ad body)).val

/-- **Expected result of sealing** (`seal_at`, patched lines 533–561, upstream 540–569) at time
`now`, as the UTF-8 bytes of the token: the body is `frameBytes (sealExpiry ttl now) payload`
(W15, line 541); a single-key codec seals `rs1` with its key (line 544); a keyring seals with its
seal-mode key id `kid`, `rs1` with the key stored under `kid` (lines 548–552) or `rs2` with the
UTF-8 bytes of `kid` and that key (lines 553–558). `none` if the keyring holds no key under
`kid` (the `expect` at line 549 or 555 panics). The key stored under `kid` is `lookupKey`, the
model of `HashMap::get`. -/
def sealAt (codec : RequestStateCodec) (payload ad : List U8) (ttl : Option core.time.Duration)
    (now : Int) : Option (List U8) :=
  let body := frameBytes (sealExpiry ttl now) payload
  match codec.keys with
  | .Single key => some (tokenV1 key.inner.val ad body)
  | .Ring keys (.Rs1 kid) _ => (lookupKey keys kid).map fun key => tokenV1 key ad body
  | .Ring keys (.Rs2 kid) _ =>
    (lookupKey keys kid).map fun key => tokenV2 (ExtModel.utf8 kid) key ad body

/-- The seal-mode key id of a keyring codec is a key id (the third clause of `CodecValid`); a
single-key codec satisfies it. It is the part of the codec-state predicate that sealing needs:
`keys.get(key_id).expect(..)` (patched lines 549 and 555) panics exactly when it fails. -/
def CodecSealKeyKnown (codec : RequestStateCodec) : Prop :=
  match codec.keys with
  | .Single _ => True
  | .Ring keys seal_mode _ => sealModeKid seal_mode ∈ keyIds keys

/-- **Lean-model domain of sealing** a payload of `payloadLen` bytes with associated data of
`adLen` bytes (plan Section 3, "W01 and the seal capacities" and "Lean-model domains"): the MAC
transcript fits in `usize::MAX` bytes (the bound of the Lean model of `Vec::extend_from_slice`;
`transcriptV1`/`transcriptV2` have `26 + 8 + adLen + expiryLen + payloadLen` and
`26 + 8 + |kid| + 8 + adLen + expiryLen + payloadLen` bytes, with `expiryLen = 8` the expiry
prefix of the body) and the capacity sum of `seal_rs1`
(patched lines 578–580) or `seal_rs2` (lines 594–600) is at most `isize::MAX`
(`ExtModel.maxStringBytes`; `String::with_capacity` panics above it). The `rs2` case is that of
a keyring sealing `rs2` with key id `kid`; every other codec seals `rs1`. -/
def SealFits (codec : RequestStateCodec) (payloadLen adLen : Nat) : Prop :=
  match codec.keys with
  | .Ring _ (.Rs2 kid) _ =>
    domainV2.length + 8 + kid.utf8ByteSize + 8 + adLen + expiryLen + payloadLen ≤ Usize.max ∧
    versionV2.length + 3 + b64Len kid.utf8ByteSize + b64Len (expiryLen + payloadLen) +
      b64Len 32 ≤ ExtModel.maxStringBytes
  | _ =>
    domainV1.length + 8 + adLen + expiryLen + payloadLen ≤ Usize.max ∧
    versionV1.length + 2 + b64Len (expiryLen + payloadLen) + b64Len 32 ≤ ExtModel.maxStringBytes

/-! ### Keyring configuration -/

/-- **Lean-model domain of the keyring builders** (`with_rs1_signing`, `with_rs1_fallback`): every
key id has at most `usize::MAX` UTF-8 bytes (the Lean model of `Borrow<str> for String`, used by
`contains_key` with a `&str` query, fails above it) and there are fewer than `usize::MAX` rs1
fallbacks (the Aeneas model of `Vec::push` fails at `usize::MAX` elements). Every Rust value
satisfies both: a `String` has at most `isize::MAX` bytes, and a `Vec<String>` at most
`isize::MAX / 24` elements. A single-key codec satisfies it. How a caller discharges it: it
holds for every value a Rust program can have; along the public constructor chain,
`new_with_keyring` (R15) yields key ids of 1 to 255 bytes (`CodecValid`) and no fallback, and
each `with_rs1_signing`/`with_rs1_fallback` (R11/R12) keeps the key table and adds at most one
fallback, so after `n` builder calls there are at most `n` fallbacks. -/
def KeyringFits (codec : RequestStateCodec) : Prop :=
  match codec.keys with
  | .Single _ => True
  | .Ring keys _ rs1_fallbacks =>
    (∀ kid ∈ keyIds keys, kid.utf8ByteSize ≤ Usize.max) ∧
      rs1_fallbacks.val.length < Usize.max

/-- The iterator `it` of the caller's `Iterator` instance (its `next`) yields the items `items` in
order and then `None`. Used for the `keys: impl IntoIterator` argument of `new_with_keyring`
(patched line 328: `for (kid, key) in keys`), whose iterator is caller code. It relies on the
Aeneas translation of the trait, where `next` is a pure function of the iterator state; stated
exception: a caller iterator with side effects outside its state (global or thread-local state,
input/output) is not described. A finite list of items is assumed (an infinite iterator has no
such list). Kept in `Defs.CodecState` because only the R15 statement uses it. -/
def IterYields {I T : Type} (next : I → Result (Option T × I)) : I → List T → Prop
  | it, [] => ∃ it', next it = ok (none, it')
  | it, x :: xs => ∃ it', next it = ok (some x, it') ∧ IterYields next it' xs

/-- Why `new_with_keyring` rejects its arguments. -/
inductive KeyringFailure where
  /-- A key id (configured or active) is empty (`InvalidKeyring(KID_EMPTY_MSG)`). -/
  | kidEmpty
  /-- A key id has more than 255 UTF-8 bytes (`InvalidKeyring(KID_TOO_LONG_MSG)`). -/
  | kidTooLong
  /-- A key has `actual < 32` bytes (`KeyTooShort { minimum: 32, actual }`). -/
  | keyTooShort (actual : Nat)
  /-- A key id occurs twice (`InvalidKeyring("duplicate key id")`). -/
  | duplicateKid
  /-- No key (`InvalidKeyring("keyring must contain at least one key")`). -/
  | emptyKeyring
  /-- The active id is not a key id (`InvalidKeyring("active key id is not present …")`). -/
  | activeKidMissing

/-- The error value that each failure of `new_with_keyring` returns: the `InvalidKeyring`
messages (texts of `Defs.RequestState` and `Defs.CodecState`, related to the `&'static str` by
`StrIs`) and `KeyTooShort { minimum: 32, actual }` (E03). -/
def KeyringFailure.Describes : KeyringFailure → RequestStateError → Prop
  | .kidEmpty, e => ∃ msg, e = .InvalidKeyring msg ∧ StrIs msg kidEmptyMsg
  | .kidTooLong, e => ∃ msg, e = .InvalidKeyring msg ∧ StrIs msg kidTooLongMsg
  | .keyTooShort n, e => ∃ minimum actual : Usize, e = .KeyTooShort minimum actual ∧
      minimum.val = minKeyLength ∧ actual.val = n
  | .duplicateKid, e => ∃ msg, e = .InvalidKeyring msg ∧ StrIs msg duplicateKidMsg
  | .emptyKeyring, e => ∃ msg, e = .InvalidKeyring msg ∧ StrIs msg emptyKeyringMsg
  | .activeKidMissing, e => ∃ msg, e = .InvalidKeyring msg ∧ StrIs msg activeKidMissingMsg

/-- The first rejected entry of a keyring configuration, scanned in order with the ids `seen`
already accepted (patched lines 328–341, upstream 338–351): for each `(kid, key)`, an empty id
(E04, line 331), then an id over 255 bytes (E04), then a key under 32 bytes (E03, line 332), then
an id already accepted (`Entry::Occupied`, lines 333–339); `none` if every entry is accepted. -/
def keyringScan : List String → List (String × List U8) → Option KeyringFailure
  | _, [] => none
  | seen, (kid, key) :: rest =>
    if kid.utf8ByteSize = 0 then some .kidEmpty
    else if maxKidLen < kid.utf8ByteSize then some .kidTooLong
    else if key.length < minKeyLength then some (.keyTooShort key.length)
    else if kid ∈ seen then some .duplicateKid
    else keyringScan (seen ++ [kid]) rest

/-- **Expected outcome of `new_with_keyring`** (patched lines 319–364, upstream 329–374) for the
active id `active` and the converted entries `entries`, in the Rust order of checks: the first
rejected entry (`keyringScan`); then no entry → `emptyKeyring` (lines 343–347); then the active
id empty or over 255 bytes (E04, line 350); then the active id not a key id →
`activeKidMissing` (lines 351–355); otherwise success (lines 357–363). -/
def keyringCheck (active : String) (entries : List (String × List U8)) :
    Except KeyringFailure Unit :=
  match keyringScan [] entries with
  | some f => .error f
  | none =>
    if entries = [] then .error .emptyKeyring
    else if active.utf8ByteSize = 0 then .error .kidEmpty
    else if maxKidLen < active.utf8ByteSize then .error .kidTooLong
    else if active ∈ entries.map Prod.fst then .ok ()
    else .error .activeKidMissing

/-! ### Abbreviations used by the public statements

Each definition below names a formula that the public `request_state.rs` statements
(`formal/specs/Specs/Model/RequestState.lean`, R06–R15) used to spell out in full. Its body is
exactly the replaced text, so each statement that uses it is definitionally equal (`rfl`) to its
signed-off form; none adds or drops a condition (readability rewrite of 2026-11-25, signed off
by the spec owner on 2026-11-25). Line numbers: "patched" is the patched copy of
`request_state.rs` (patches 01–03 on origin/main `7caec76`), which agrees with the patch-01 copy cited above up to
line 526; "upstream" is `7caec76`. -/

/-- The bytes of a Rust `&str`. Aeneas translates `&str` to `Str`, the slice of its UTF-8 bytes
(`def Str := Slice U8`, `Aeneas/Std/StringDef.lean`); this is that list of bytes. Used for the
`sealed: &str` token of `open`, `open_with`, `open_json` and `open_json_with` (patched lines 476,
495–498, 509 and 521–525; upstream 486, 505–508, 519 and 531–535) and for the `&str` that
`kid.as_ref()` returns in `with_rs1_signing` and `with_rs1_fallback` (patched lines 374 and 411,
upstream 384 and 421). -/
def strBytes (s : Str) : List U8 := (s : Slice U8).val

/-- **Premise (F) for one token**: if the first `.`-component of `token` is `rs1`, every rs1
fallback id of `codec` is a key id (`CodecFallbacksKnown`). The premise is sufficient, not
necessary, for Rust not to panic: `open_at` dispatches on the first component (patch-01 copy
lines 565–568), and the fallback loop, whose `keys.get(kid).expect("validated rs1 fallback key")`
(patch-01 copy line 652, patched 656, upstream 661) panics on the first fallback id that is not a
key id, is reached only by an `rs1` token that splits into three components, opened by a keyring
with a non-empty fallback list, whose body and tag both decode (patch-01 copy lines 613–624).
A single-key codec never reaches the loop (it checks the tag directly, patch-01 copy line 629);
any other `rs1` token opened by a keyring returns an error (`MalformedFormat`, `UnknownKeyId` or
`InvalidEncoding`) before the loop. -/
def FallbacksKnownForToken (codec : RequestStateCodec) (token : List U8) : Prop :=
  (components token).head? = some versionV1 → CodecFallbacksKnown codec

/-- **Premise (T), `rs1` tokens**: if `token` splits on `.` into `["rs1", b, t]` and `b` decodes
(`ExtModel.b64Decode`) to `body`, the MAC transcript `transcriptV1 ad body` has at most
`usize::MAX` bytes. This is the domain of the Lean model of `Vec::extend_from_slice` (an Aeneas
`Vec` holds at most `usize::MAX` elements), which builds the transcript of the tag check of
`open_rs1_at` (patch-01 copy lines 627–638; see `openRs1`). -/
def TranscriptV1Fits (token ad : List U8) : Prop :=
  ∀ b t body, components token = [versionV1, b, t] → ExtModel.b64Decode b = some body →
    (transcriptV1 ad body).length ≤ Usize.max

/-- **Premise (T), `rs2` tokens**: if `token` splits on `.` into `["rs2", k, b, t]`, `k` decodes
to `kid` and `b` to `body`, the MAC transcript `transcriptV2 kid ad body` has at most
`usize::MAX` bytes (as `TranscriptV1Fits`, for the tag check of `open_rs2_at`, patch-01 copy
lines 687–690; see `openRs2`). -/
def TranscriptV2Fits (token ad : List U8) : Prop :=
  ∀ k b t kid body, components token = [versionV2, k, b, t] →
    ExtModel.b64Decode k = some kid → ExtModel.b64Decode b = some body →
    (transcriptV2 kid ad body).length ≤ Usize.max

/-- The list `l` with `x` appended at the end, unless `x` already occurs in `l` (then `l`
unchanged): the rs1 fallback update of `with_rs1_signing`,
`if !rs1_fallbacks.iter().any(|existing| existing == &kid) { rs1_fallbacks.push(kid); }`
(patched lines 394–396, upstream 404–406, with `kid` the owned `String`), and of
`with_rs1_fallback`,
`if !rs1_fallbacks.iter().any(|existing| existing == kid) { rs1_fallbacks.push(kid.to_owned()); }`
(patched lines 426–428, upstream 436–438, with `kid` the `&str`). -/
def appendIfAbsent (l : List String) (x : String) : List String :=
  if x ∈ l then l else l ++ [x]

/-- `e` is `RequestStateError::InvalidKeyring(msg)` (patched line 129, upstream 139) whose
`&'static str` message `msg` holds exactly the UTF-8 bytes of `text` (`StrIs`). -/
def IsInvalidKeyring (e : RequestStateError) (text : String) : Prop :=
  ∃ msg, e = .InvalidKeyring msg ∧ StrIs msg text

/-- The converted keyring entries of `new_with_keyring`, each key given as its list of bytes:
`(kid, key) ↦ (kid, key.val)`. These are the pairs `(kid.into(), key.into())` of the loop
(patched lines 328–330, upstream 338–340), in the form `keyringCheck` takes. -/
def entryBytes (entries : List (String × alloc.vec.Vec U8)) : List (String × List U8) :=
  entries.map fun c => (c.1, c.2.val)

/-- How `open_json_with` turns the outcome of `serde_json::from_slice` into its result:
`Ok value ↦ Ok value`, `Err error ↦ Err(RequestStateError::Deserialization(error))` (patched
lines 527–530, patch 03; upstream `.map_err(RequestStateError::Deserialization)`, line 537). It
names no model: the statements apply it to `ExtModel.serdeJsonFromSlice …` at the call site. -/
def mapErrDeserialization {T : Type} (r : core.result.Result T serde_json.error.Error) :
    core.result.Result T RequestStateError :=
  match r with
  | .Ok value => .Ok value
  | .Err error => .Err (.Deserialization error)

/-- `e` is `RequestStateError::KeyTooShort { minimum, actual }` (patched line 99, upstream 109;
built by `validate_key_length`, patched lines 708–716, upstream 755–763) with `minimum = 32`
(`minKeyLength`; `Self::MIN_KEY_LENGTH`, patched line 270, upstream 280) and `actual = n`. Used
for the `Err` case of `try_new` (R06), where `n` is the length of the converted key. -/
def IsKeyTooShort (e : RequestStateError) (n : Nat) : Prop :=
  ∃ minimum actual : Usize, e = .KeyTooShort minimum actual ∧
    minimum.val = minKeyLength ∧ actual.val = n

/-- The caller's conversions turn the items `items` of the `keys` iterator of `new_with_keyring`
into the converted entries `entries`, position by position: for the item `(kid, key)` at a
position, `kid.into()` (with the caller's `Into<String>`, `kidInto`) returns the key id and
`key.into()` (with the caller's `Into<Vec<u8>>`, `keyInto`) returns the key of the entry at the
same position (patched lines 329–330, upstream 339–340). Both conversions are caller code,
translated as functions of their argument; as for `IterYields`, a conversion with side effects
outside its argument (global or thread-local state, input/output) is not described. -/
def ItemsConvert {K V : Type} (kidInto : core.convert.Into K String)
    (keyInto : core.convert.Into V (alloc.vec.Vec U8)) (items : List (K × V))
    (entries : List (String × alloc.vec.Vec U8)) : Prop :=
  List.Forall₂ (fun (p : K × V) (c : String × alloc.vec.Vec U8) =>
    kidInto.into p.1 = ok c.1 ∧ keyInto.into p.2 = ok c.2) items entries

end Defs.CodecState
