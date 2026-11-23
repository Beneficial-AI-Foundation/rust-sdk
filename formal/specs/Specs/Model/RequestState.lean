/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Defs
import Proofs

/-!
# Spec file for crates/rmcp/src/model/request_state.rs

Statements of the codec functions of `RequestStateCodec` (plan Section 2.2), in Rust source
order, each restated as a theorem `Theorems.request_state.RequestStateCodec.<function>` proved by
the spec theorem in `Proofs/Model/RequestState/` and followed by
the assumptions its proof depends on, checked by `#print axioms` under `#guard_msgs`. The
statements were signed off by the spec owner on 2026-11-23 (the S05 evidence (git history at 223ff12)); their signed-off
text is in `specs/Drafts/RequestState.lean` at commit `9bd8144`.

Translated configuration (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
features `--no-default-features --features request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth`
(widened for Phase 2, plan Section 15; the translation of this file's targets is unchanged), with `overflow-checks=true` and
`debug-assertions=true` (plan Section 1), so arithmetic overflow panics, which Aeneas models as
failure. Aeneas `nightly-2026.08.20-5d08da4`; the translation base is the patched copy (patch 01
on origin/main 7caec76, `formal/trusted/patches/01-request-state-wire.patch`, D2 fallback
2026-11-23; translation committed at `9bd8144`). Line numbers refer to `request_state.rs` in the
patched copy.

Definitions used: `Defs.Wire` (`expiryLen`, `bodyExpiry`, `Expired`, `minKeyLength`, `maxKidLen`,
`b64Len`, `dot`, `components`, `versionV1`, `versionV2`, `transcriptV1`, `transcriptV2`),
`Defs.RequestState` (`StrIs`, `kidEmptyMsg`, `kidTooLongMsg`) and `Defs.CodecState` (`KeyTable`,
`FallbacksKnown`, `CodecFallbacksKnown`, `Rs1Verifies`, `openRs1`, `openRs2`, `openAt`,
`resultBytes`, `lookupKey`).

External models used (S08–S09, `trusted/Rmcp/FunsExternal.lean`): E04 uses the model of
`core.str.Str.len` (the byte length of the `Str`). E04 also depends on the native-code
assumptions `KID_EMPTY_MSG._native.decide.ax_1` and `KID_TOO_LONG_MSG._native.decide.ax_1`, which
the pinned Aeneas `toStr` declares for the two message literals of the translation (listed in
`trusted/native-axioms.lock`; any statement about `validate_config_kid` reaches them).

External models used by E07–E11 and E09a: `ExtModel.utf8`, `ExtModel.b64`, `ExtModel.b64Decode`,
`ExtModel.hmacSha256`, `ExtModel.maxStringBytes`, `ExtModel.strOfBytes?`. Stated exceptions (plan
Section 4, rows "HMAC" and "Standard library"): HMAC SHA-256 always succeeds in the model, while
its `u64` bit-length counter overflows (a panic under overflow-checks) for a message of at least
`2^61 - 64` bytes or a key of at least `2^61` bytes; allocation failure is not modelled, and the
transcript `Vec` is modelled up to `Usize.max` bytes where Rust panics above `isize::MAX`. For
such inputs a statement promises a result where the Rust code panics. The E07/E08 premises
`h_len`/`h_cap` are the no-overflow domains of the debug-build semantics. E07 and E08 reach the
locked native-code assumptions `VERSION_V1._native.decide.ax_1` and
`VERSION_V2._native.decide.ax_1`;
E09, E09a and E11 reach `RequestStateCodec.rs1_fallbacks_verify_loop.body._native.decide.ax_3`;
E10 reaches none (all in `trusted/native-axioms.lock`).

Statements here, in Rust source order: E11 (line 559), E07 (572), E08 (585), E09 (607),
E09a (644), E10 (659) (S11, S13, S14), then E01 (695), E03 (704), E04 (714), E02 (725) (S07).
The E07–E11 and E09a statements were signed off by the spec owner on 2026-11-23 after three
review rounds (the S05 evidence (git history at 223ff12), "E batch part 2"); their signed-off text was in
`specs/Drafts/RequestState.lean`, removed at incorporation.

Composition theorems last (S15, proofs in `Proofs/Model/RequestState/Roundtrip.lean`):
`rs1_roundtrip`, `rs2_roundtrip`, `open_at_roundtrip_rs1`, `open_at_roundtrip_rs2`. Each says that
sealing terminates, that some `Str` holds the token's bytes, and that opening any such `Str`
returns `Ok (body[8..])`, under the plan Section 3 round-trip conditions and the seal statements'
own size premises. Signed off by the spec owner on 2026-11-23 after two review rounds
(the S15 evidence (git history at 223ff12)). The rs1 ones reach `VERSION_V1._native.decide.ax_1` and
`RequestStateCodec.rs1_fallbacks_verify_loop.body._native.decide.ax_3`; `rs2_roundtrip` reaches
`VERSION_V2._native.decide.ax_1`; `open_at_roundtrip_rs2` reaches both `VERSION_V2…` and `…ax_3`.
-/

open Aeneas Aeneas.Std Result
open Defs.Wire
open rmcp.model.request_state  -- for `RequestStateError`; theorems named in full
open Defs.CodecState (KeyTable FallbacksKnown CodecFallbacksKnown Rs1Verifies openRs1 openRs2
  openAt resultBytes lookupKey)

open rmcp.model.request_state.RequestStateCodec (open_at) in
/-- E11 `open_at`: dispatches on the first `.`-component of the token, `"rs1"` to E09 and
`"rs2"` to E10, anything else to `MalformedFormat`; the result is exactly `openAt`. -/
theorem Theorems.request_state.RequestStateCodec.open_at
    (self : RequestStateCodec) (sealed : Str) (associated_data : Slice Std.U8)
    (now_ms : Std.I64)
    (h_len1 : ∀ b t body, components (sealed : Slice Std.U8).val = [versionV1, b, t] →
      ExtModel.b64Decode b = some body →
      (transcriptV1 associated_data.val body).length ≤ Usize.max)
    (h_len2 : ∀ k b t kid body, components (sealed : Slice Std.U8).val = [versionV2, k, b, t] →
      ExtModel.b64Decode k = some kid → ExtModel.b64Decode b = some body →
      (transcriptV2 kid associated_data.val body).length ≤ Usize.max)
    (h_fallbacks : (components (sealed : Slice Std.U8).val).head? = some versionV1 →
      CodecFallbacksKnown self) :
    open_at self sealed associated_data now_ms ⦃ (result :
        core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      -- lines 565–568; `openAt` (Defs.CodecState) dispatches on `(components _).head?`
      resultBytes result = openAt self (sealed : Slice Std.U8).val associated_data.val
        now_ms.val ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_at_spec self sealed associated_data now_ms
    h_len1 h_len2 h_fallbacks

/--
info: 'Theorems.request_state.RequestStateCodec.open_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RequestStateCodec.rs1_fallbacks_verify_loop.body._native.decide.ax_3]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open_at

/-- E07 `seal_rs1`: the token `"rs1." ++ b64 body ++ "." ++ b64 tag` as UTF-8 bytes, where `tag`
is the HMAC SHA-256 of `transcriptV1 associated_data body` under `key`. -/
theorem Theorems.request_state.RequestStateCodec.seal_rs1 (key : Slice Std.U8)
    (associated_data : Slice Std.U8)
    (body : Slice Std.U8)
    (h_len : (transcriptV1 associated_data.val body.val).length ≤ Usize.max)
    (h_cap : versionV1.length + 2 + b64Len body.val.length + b64Len 32 ≤
      ExtModel.maxStringBytes) :
    rmcp.model.request_state.RequestStateCodec.seal_rs1 key associated_data body ⦃
      (result : String) =>
      -- lines 577–582: "rs1", '.', b64(body), '.', b64(tag); tag from line 573
      ExtModel.utf8 result =
        versionV1 ++ [dot] ++ ExtModel.b64 body.val ++ [dot] ++
          ExtModel.b64 (ExtModel.hmacSha256 key.val
            (transcriptV1 associated_data.val body.val)).val ⦄ :=
  rmcp.model.request_state.RequestStateCodec.seal_rs1_spec key associated_data body h_len h_cap

/--
info: 'Theorems.request_state.RequestStateCodec.seal_rs1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 VERSION_V1._native.decide.ax_1]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.seal_rs1

/-- E08 `seal_rs2`: the token `"rs2." ++ b64 kid ++ "." ++ b64 body ++ "." ++ b64 tag` as UTF-8
bytes, where `tag` is the HMAC SHA-256 of `transcriptV2 kid associated_data body` under `key`;
any kid is accepted. -/
theorem Theorems.request_state.RequestStateCodec.seal_rs2 (kid : Str) (key : Slice Std.U8)
    (associated_data : Slice Std.U8)
    (body : Slice Std.U8)
    (h_len : (transcriptV2 (kid : Slice Std.U8).val associated_data.val body.val).length ≤
      Usize.max)
    (h_cap : versionV2.length + 3 + b64Len (kid : Slice Std.U8).val.length +
      b64Len body.val.length + b64Len 32 ≤ ExtModel.maxStringBytes) :
    rmcp.model.request_state.RequestStateCodec.seal_rs2 kid key associated_data body ⦃
      (result : String) =>
      -- lines 597–604: "rs2", '.', b64(kid), '.', b64(body), '.', b64(tag); tag from 586–589
      ExtModel.utf8 result =
        versionV2 ++ [dot] ++ ExtModel.b64 (kid : Slice Std.U8).val ++ [dot] ++
          ExtModel.b64 body.val ++ [dot] ++
          ExtModel.b64 (ExtModel.hmacSha256 key.val
            (transcriptV2 (kid : Slice Std.U8).val associated_data.val body.val)).val ⦄ :=
  rmcp.model.request_state.RequestStateCodec.seal_rs2_spec kid key associated_data body h_len
    h_cap

/--
info: 'Theorems.request_state.RequestStateCodec.seal_rs2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 VERSION_V2._native.decide.ax_1]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.seal_rs2

/-- E09 `open_rs1_at`: the result is exactly `openRs1` (the error order of plan Section 3, then
E01 on the authenticated body). -/
theorem Theorems.request_state.RequestStateCodec.open_rs1_at (self : RequestStateCodec)
    (sealed : Str) (associated_data : Slice Std.U8) (now_ms : Std.I64)
    (h_count : (sealed : Slice Std.U8).val.count dot < Usize.max)
    (h_len : ∀ b t body, components (sealed : Slice Std.U8).val = [versionV1, b, t] →
      ExtModel.b64Decode b = some body →
      (transcriptV1 associated_data.val body).length ≤ Usize.max)
    (h_fallbacks : CodecFallbacksKnown self) :
    rmcp.model.request_state.RequestStateCodec.open_rs1_at self sealed associated_data now_ms ⦃
        (result : core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      -- lines 613–640, in the order of plan Section 3 (see `Defs.CodecState.openRs1`)
      resultBytes result = openRs1 self (sealed : Slice Std.U8).val associated_data.val
        now_ms.val ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_rs1_at_spec self sealed associated_data now_ms
    h_count h_len h_fallbacks

/--
info: 'Theorems.request_state.RequestStateCodec.open_rs1_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RequestStateCodec.rs1_fallbacks_verify_loop.body._native.decide.ax_3]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open_rs1_at

/-- E09a `rs1_fallbacks_verify`: `true` iff some rs1 fallback key verifies the tag over the
transcript (`Rs1Verifies`). -/
theorem Theorems.request_state.RequestStateCodec.rs1_fallbacks_verify (keys : KeyTable)
    (rs1_fallbacks : Slice String) (transcript : Slice Std.U8) (tag : Slice Std.U8)
    (h_known : FallbacksKnown keys rs1_fallbacks.val) :
    rmcp.model.request_state.RequestStateCodec.rs1_fallbacks_verify keys rs1_fallbacks transcript
        tag ⦃ (result : Bool) =>
      -- lines 650–656: `verified |= hmac_sha256_verify(key, transcript, tag)` over all ids
      result = decide (Rs1Verifies keys rs1_fallbacks.val transcript.val tag.val) ⦄ :=
  rmcp.model.request_state.RequestStateCodec.rs1_fallbacks_verify_spec keys rs1_fallbacks
    transcript tag h_known

/--
info: 'Theorems.request_state.RequestStateCodec.rs1_fallbacks_verify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RequestStateCodec.rs1_fallbacks_verify_loop.body._native.decide.ax_3]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.rs1_fallbacks_verify

/-- E10 `open_rs2_at`: the result is exactly `openRs2` (the error order of plan Section 3, then
E01 on the decoded body), for every codec. -/
theorem Theorems.request_state.RequestStateCodec.open_rs2_at (self : RequestStateCodec)
    (sealed : Str)
    (associated_data : Slice Std.U8) (now_ms : Std.I64)
    (h_count : (sealed : Slice Std.U8).val.count dot < Usize.max)
    (h_len : ∀ k b t kid body, components (sealed : Slice Std.U8).val = [versionV2, k, b, t] →
      ExtModel.b64Decode k = some kid → ExtModel.b64Decode b = some body →
      (transcriptV2 kid associated_data.val body).length ≤ Usize.max) :
    rmcp.model.request_state.RequestStateCodec.open_rs2_at self sealed associated_data
        now_ms ⦃ (result :
        core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      -- lines 665–692, in the order of plan Section 3 (see `Defs.CodecState.openRs2`)
      resultBytes result = openRs2 self (sealed : Slice Std.U8).val associated_data.val
        now_ms.val ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_rs2_at_spec self sealed associated_data now_ms
    h_count h_len

/--
info: 'Theorems.request_state.RequestStateCodec.open_rs2_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open_rs2_at

/-- E01 `open_authenticated_body`: `MalformedFormat` below 8 bytes, otherwise `Expired` if the
body's expiry has passed, otherwise `Ok` of the bytes after the first 8. -/
theorem Theorems.request_state.RequestStateCodec.open_authenticated_body
    (body : alloc.vec.Vec Std.U8) (now_ms : Std.I64) :
    rmcp.model.request_state.RequestStateCodec.open_authenticated_body body now_ms ⦃ (result :
        core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      match result with
      | .Ok payload =>
        expiryLen ≤ body.val.length ∧
        ¬ Expired (bodyExpiry body.val) now_ms.val ∧
        payload.val = body.val.drop expiryLen
      | .Err e =>
        (body.val.length < expiryLen ∧ e = .MalformedFormat) ∨
        (expiryLen ≤ body.val.length ∧ Expired (bodyExpiry body.val) now_ms.val ∧
          e = .Expired) ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_authenticated_body_spec body now_ms

/--
info: 'Theorems.request_state.RequestStateCodec.open_authenticated_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open_authenticated_body

/-- E03 `validate_key_length`: `Ok ()` iff the key has at least `MIN_KEY_LENGTH = 32` bytes,
otherwise `KeyTooShort { minimum: 32, actual: key.len() }`. -/
theorem Theorems.request_state.RequestStateCodec.validate_key_length (key : Slice Std.U8) :
    rmcp.model.request_state.RequestStateCodec.validate_key_length key ⦃ (result :
        core.result.Result Unit RequestStateError) =>
      match result with
      | .Ok _ => minKeyLength ≤ key.val.length
      | .Err e =>
        key.val.length < minKeyLength ∧
        ∃ minimum actual : Std.Usize, e = .KeyTooShort minimum actual ∧
          minimum.val = minKeyLength ∧ actual.val = key.val.length ⦄ :=
  rmcp.model.request_state.RequestStateCodec.validate_key_length_spec key

/--
info: 'Theorems.request_state.RequestStateCodec.validate_key_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.validate_key_length

/-- E04 `validate_config_kid`: `Ok ()` iff the UTF-8 byte length of `kid` is in `1..=255`; a
length of `0` gives `InvalidKeyring` with the text of `KID_EMPTY_MSG`, a length above 255 gives
`InvalidKeyring` with the text of `KID_TOO_LONG_MSG`. -/
theorem Theorems.request_state.RequestStateCodec.validate_config_kid (kid : Str) :
    rmcp.model.request_state.RequestStateCodec.validate_config_kid kid ⦃ (result :
        core.result.Result Unit RequestStateError) =>
      match result with
      | .Ok _ =>
        1 ≤ (kid : Slice Std.U8).val.length ∧ (kid : Slice Std.U8).val.length ≤ maxKidLen
      | .Err e =>
        ((kid : Slice Std.U8).val.length = 0 ∧
          ∃ msg, e = .InvalidKeyring msg ∧ Defs.RequestState.StrIs msg
            Defs.RequestState.kidEmptyMsg) ∨
        (maxKidLen < (kid : Slice Std.U8).val.length ∧
          ∃ msg, e = .InvalidKeyring msg ∧ Defs.RequestState.StrIs msg
            Defs.RequestState.kidTooLongMsg) ⦄ :=
  rmcp.model.request_state.RequestStateCodec.validate_config_kid_spec kid

/--
info: 'Theorems.request_state.RequestStateCodec.validate_config_kid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 KID_EMPTY_MSG._native.decide.ax_1,
 KID_TOO_LONG_MSG._native.decide.ax_1]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.validate_config_kid

/-- E02 `b64_len`: equals W01; on the no-overflow domain `b64Len len ≤ Usize.max`, the result is
`b64Len len = 4 * ((len + 2) / 3)`. -/
theorem Theorems.request_state.RequestStateCodec.b64_len (len : Std.Usize)
    (h_no_overflow : b64Len len.val ≤ Usize.max) :
    rmcp.model.request_state.RequestStateCodec.b64_len len ⦃ (result : Std.Usize) =>
      result.val = b64Len len.val ⦄ :=
  rmcp.model.request_state.RequestStateCodec.b64_len_spec len h_no_overflow

/--
info: 'Theorems.request_state.RequestStateCodec.b64_len' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.b64_len

/-- S15 `rs1_roundtrip`: sealing with E07 `seal_rs1` and opening any `Str` holding the token's
bytes with E09 `open_rs1_at` (same associated data, accepted key, body of at least 8 bytes, not
expired) returns `Ok (body[8..])`. -/
theorem Theorems.request_state.RequestStateCodec.rs1_roundtrip (self : RequestStateCodec)
    (key : Slice Std.U8) (associated_data : Slice Std.U8) (body : Slice Std.U8)
    (now_ms : Std.I64)
    (h_len : (transcriptV1 associated_data.val body.val).length ≤ Usize.max)
    (h_cap : versionV1.length + 2 + b64Len body.val.length + b64Len 32 ≤
      ExtModel.maxStringBytes)
    (h_body : expiryLen ≤ body.val.length)
    (h_expiry : ¬ Expired (bodyExpiry body.val) now_ms.val)
    (h_key : (∃ k, self.keys = .Single k ∧ k.inner.val = key.val) ∨
      (∃ keys seal_mode rs1_fallbacks kid, self.keys = .Ring keys seal_mode rs1_fallbacks ∧
        kid ∈ rs1_fallbacks.val ∧ lookupKey keys kid = some key.val))
    (h_fallbacks : CodecFallbacksKnown self) :
    rmcp.model.request_state.RequestStateCodec.seal_rs1 key associated_data body ⦃
      (token : String) =>
      (∃ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token) ∧
      ∀ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token →
      rmcp.model.request_state.RequestStateCodec.open_rs1_at self sealed associated_data
        now_ms ⦃ (result : core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
        -- line 640 → E01 line 698: `Ok(payload.to_vec())`, payload = body[8..]
        resultBytes result = .ok (body.val.drop expiryLen) ⦄ ⦄ :=
  rmcp.model.request_state.RequestStateCodec.rs1_roundtrip self key associated_data body now_ms
    h_len h_cap h_body h_expiry h_key h_fallbacks

/--
info: 'Theorems.request_state.RequestStateCodec.rs1_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 VERSION_V1._native.decide.ax_1,
 RequestStateCodec.rs1_fallbacks_verify_loop.body._native.decide.ax_3]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.rs1_roundtrip

/-- S15 `rs2_roundtrip`: sealing with E08 `seal_rs2` and opening any `Str` holding the token's
bytes with E10 `open_rs2_at` (same associated data, UTF-8 kid of 1 to 255 bytes that the ring maps
to the key, body of at least 8 bytes, not expired) returns `Ok (body[8..])`. -/
theorem Theorems.request_state.RequestStateCodec.rs2_roundtrip (self : RequestStateCodec)
    (kid : Str) (key : Slice Std.U8) (associated_data : Slice Std.U8) (body : Slice Std.U8)
    (now_ms : Std.I64) (kidStr : String)
    (h_len : (transcriptV2 (kid : Slice Std.U8).val associated_data.val body.val).length ≤
      Usize.max)
    (h_cap : versionV2.length + 3 + b64Len (kid : Slice Std.U8).val.length +
      b64Len body.val.length + b64Len 32 ≤ ExtModel.maxStringBytes)
    (h_body : expiryLen ≤ body.val.length)
    (h_expiry : ¬ Expired (bodyExpiry body.val) now_ms.val)
    (h_kid_utf8 : (kid : Slice Std.U8).val = ExtModel.utf8 kidStr)
    (h_kid_len : 1 ≤ (kid : Slice Std.U8).val.length ∧
      (kid : Slice Std.U8).val.length ≤ maxKidLen)
    (h_key : ∃ keys seal_mode rs1_fallbacks, self.keys = .Ring keys seal_mode rs1_fallbacks ∧
      lookupKey keys kidStr = some key.val) :
    rmcp.model.request_state.RequestStateCodec.seal_rs2 kid key associated_data body ⦃
      (token : String) =>
      (∃ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token) ∧
      ∀ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token →
      rmcp.model.request_state.RequestStateCodec.open_rs2_at self sealed associated_data
        now_ms ⦃ (result : core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
        -- line 692 → E01 line 698: `Ok(payload.to_vec())`, payload = body[8..]
        resultBytes result = .ok (body.val.drop expiryLen) ⦄ ⦄ :=
  rmcp.model.request_state.RequestStateCodec.rs2_roundtrip self kid key associated_data body
    now_ms kidStr h_len h_cap h_body h_expiry h_kid_utf8 h_kid_len h_key

/--
info: 'Theorems.request_state.RequestStateCodec.rs2_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 VERSION_V2._native.decide.ax_1]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.rs2_roundtrip

/-- S15 `open_at_roundtrip_rs1`: sealing with E07 `seal_rs1` and opening any `Str` holding the
token's bytes with E11 `open_at` returns `Ok (body[8..])`, under the premises of
`rs1_roundtrip`. -/
theorem Theorems.request_state.RequestStateCodec.open_at_roundtrip_rs1 (self : RequestStateCodec)
    (key : Slice Std.U8) (associated_data : Slice Std.U8) (body : Slice Std.U8)
    (now_ms : Std.I64)
    (h_len : (transcriptV1 associated_data.val body.val).length ≤ Usize.max)
    (h_cap : versionV1.length + 2 + b64Len body.val.length + b64Len 32 ≤
      ExtModel.maxStringBytes)
    (h_body : expiryLen ≤ body.val.length)
    (h_expiry : ¬ Expired (bodyExpiry body.val) now_ms.val)
    (h_key : (∃ k, self.keys = .Single k ∧ k.inner.val = key.val) ∨
      (∃ keys seal_mode rs1_fallbacks kid, self.keys = .Ring keys seal_mode rs1_fallbacks ∧
        kid ∈ rs1_fallbacks.val ∧ lookupKey keys kid = some key.val))
    (h_fallbacks : CodecFallbacksKnown self) :
    rmcp.model.request_state.RequestStateCodec.seal_rs1 key associated_data body ⦃
      (token : String) =>
      (∃ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token) ∧
      ∀ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token →
      rmcp.model.request_state.RequestStateCodec.open_at self sealed associated_data now_ms ⦃
        (result : core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
        -- line 566 → line 640 → E01 line 698
        resultBytes result = .ok (body.val.drop expiryLen) ⦄ ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_at_roundtrip_rs1 self key associated_data body
    now_ms h_len h_cap h_body h_expiry h_key h_fallbacks

/--
info: 'Theorems.request_state.RequestStateCodec.open_at_roundtrip_rs1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 VERSION_V1._native.decide.ax_1,
 RequestStateCodec.rs1_fallbacks_verify_loop.body._native.decide.ax_3]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open_at_roundtrip_rs1

/-- S15 `open_at_roundtrip_rs2`: sealing with E08 `seal_rs2` and opening any `Str` holding the
token's bytes with E11 `open_at` returns `Ok (body[8..])`, under the premises of
`rs2_roundtrip`. -/
theorem Theorems.request_state.RequestStateCodec.open_at_roundtrip_rs2 (self : RequestStateCodec)
    (kid : Str) (key : Slice Std.U8) (associated_data : Slice Std.U8) (body : Slice Std.U8)
    (now_ms : Std.I64) (kidStr : String)
    (h_len : (transcriptV2 (kid : Slice Std.U8).val associated_data.val body.val).length ≤
      Usize.max)
    (h_cap : versionV2.length + 3 + b64Len (kid : Slice Std.U8).val.length +
      b64Len body.val.length + b64Len 32 ≤ ExtModel.maxStringBytes)
    (h_body : expiryLen ≤ body.val.length)
    (h_expiry : ¬ Expired (bodyExpiry body.val) now_ms.val)
    (h_kid_utf8 : (kid : Slice Std.U8).val = ExtModel.utf8 kidStr)
    (h_kid_len : 1 ≤ (kid : Slice Std.U8).val.length ∧
      (kid : Slice Std.U8).val.length ≤ maxKidLen)
    (h_key : ∃ keys seal_mode rs1_fallbacks, self.keys = .Ring keys seal_mode rs1_fallbacks ∧
      lookupKey keys kidStr = some key.val) :
    rmcp.model.request_state.RequestStateCodec.seal_rs2 kid key associated_data body ⦃
      (token : String) =>
      (∃ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token) ∧
      ∀ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token →
      rmcp.model.request_state.RequestStateCodec.open_at self sealed associated_data now_ms ⦃
        (result : core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
        -- line 567 → line 692 → E01 line 698
        resultBytes result = .ok (body.val.drop expiryLen) ⦄ ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_at_roundtrip_rs2 self kid key associated_data body
    now_ms kidStr h_len h_cap h_body h_expiry h_kid_utf8 h_kid_len h_key

/--
info: 'Theorems.request_state.RequestStateCodec.open_at_roundtrip_rs2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 VERSION_V2._native.decide.ax_1,
 RequestStateCodec.rs1_fallbacks_verify_loop.body._native.decide.ax_3]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open_at_roundtrip_rs2
