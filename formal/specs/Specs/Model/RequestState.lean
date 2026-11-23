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
statements were signed off by the spec owner on 2026-11-23 (evidence/S05.md); their signed-off
text is in `specs/Drafts/RequestState.lean` at commit `adce319`.

Translated configuration (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
features `--no-default-features --features request-state`, with `overflow-checks=true` and
`debug-assertions=true` (plan Section 1), so arithmetic overflow panics, which Aeneas models as
failure. Aeneas `nightly-2026.08.20-5d08da4`; the translation base is local commit `adce319`
(S04a part 2), not yet a pinned fork commit. Line numbers refer to `request_state.rs` at
`adce319`.

Definitions used: `Defs.Wire` (`expiryLen`, `bodyExpiry`, `Expired`, `minKeyLength`, `maxKidLen`,
`b64Len`) and `Defs.RequestState` (`StrIs`, `kidEmptyMsg`, `kidTooLongMsg`).

External models used (S08–S09, `trusted/Rmcp/FunsExternal.lean`): E04 uses the model of
`core.str.Str.len` (the byte length of the `Str`). E04 also depends on the native-code
assumptions `KID_EMPTY_MSG._native.decide.ax_1` and `KID_TOO_LONG_MSG._native.decide.ax_1`, which
the pinned Aeneas `toStr` declares for the two message literals of the translation (listed in
`trusted/native-axioms.lock`; any statement about `validate_config_kid` reaches them).

Statements here: E01, E03, E04 and E02 (S07), in Rust source order (lines 695, 704, 714, 725).
E07–E11 and E09a are added in Rust source order once proved.
-/

open Aeneas Aeneas.Std Result
open Defs.Wire
open rmcp.model.request_state  -- for `RequestStateError`; theorems named in full

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
