/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Aeneas
import Rmcp.Types
import Rmcp.FunsExternal
import Defs.Wire

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
Signed off by the spec owner on 2026-11-23 with the E07–E11 statements (the S05 evidence (git history at 0d75981),
"E batch part 2").

Rust source: `crates/rmcp/src/model/request_state.rs` (and `request_state_wire.rs` where named)
at `adce319`; both files are unchanged at `9e584e2`, and the line numbers below refer to them.
-/

namespace Defs.CodecState

open Aeneas.Std

open rmcp.model.request_state (RequestStateCodec Keys SealMode RequestStateError)
open Defs.Wire

/-- The key table of a keyring codec: the translated `HashMap<String, Zeroizing<Vec<u8>>>` of
`Keys::Ring { keys, .. }` (request_state.rs, lines 228–235; plan Section 4, "Standard library":
an association list `entries`). -/
abbrev KeyTable : Type :=
  std.collections.hash.map.HashMap String (zeroize.Zeroizing (alloc.vec.Vec U8))
    std.hash.random.RandomState Global

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
def NoRs1Fallback (codec : RequestStateCodec) : Bool :=
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
    else if NoRs1Fallback codec then .error .UnknownKeyId
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
four-case injectivity proof is written out in the S05 evidence (git history at 0d75981) ("E batch part 2",
fix round 2); `Defs` holds no proofs. -/
def resultBytes (r : core.result.Result (alloc.vec.Vec U8) RequestStateError) :
    Except RequestStateError (List U8) :=
  match r with
  | .Ok v => .ok v.val
  | .Err e => .error e

end Defs.CodecState
