/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire
import Proofs.Model.RequestStateWire.KeyLengthOk
import Proofs.Model.RequestState.Common

/-!
# Spec theorem for `RequestStateCodec::validate_key_length` (E03)

`Ok ()` iff the key has at least `MIN_KEY_LENGTH = 32` bytes, otherwise
`KeyTooShort { minimum: 32, actual: key.len() }`. The proof uses the W02 theorem
`key_length_ok_spec` through `step`, and `Proofs.RequestState.val_MIN_KEY_LENGTH` for the value
of the generated constant `RequestStateCodec::MIN_KEY_LENGTH`.

Source: "crates/rmcp/src/model/request_state.rs", line 704 in the patched copy
(patch 01 on origin/main 7caec76, D2 fallback 2026-11-23); line numbers refer to it.
-/

open Aeneas Aeneas.Std Result
open rmcp
open rmcp.model.request_state
open Defs.Wire (minKeyLength)

namespace rmcp.model.request_state.RequestStateCodec

/-- **Spec theorem for `rmcp::model::request_state::RequestStateCodec::validate_key_length`**
(E03)

With no precondition (the function never panics): `Ok ()` iff the key has at least 32 bytes
(`minKeyLength`, `MIN_KEY_LENGTH`); otherwise `KeyTooShort { minimum: 32, actual: key.len() }`. -/
@[step]
theorem validate_key_length_spec (key : Slice Std.U8) :
    validate_key_length key ⦃ (result : core.result.Result Unit RequestStateError) =>
      match result with
      -- request_state.rs l. 705 and 711 (`key_length_ok(key.len())` holds, `Ok(())`), with
      -- request_state_wire.rs l. 39–41 (`len >= MIN_KEY_LENGTH`) and l. 19 (`= 32`)
      | .Ok _ => minKeyLength ≤ key.val.length
      -- request_state.rs l. 705–710 (`KeyTooShort { minimum: Self::MIN_KEY_LENGTH,
      -- actual: key.len() }`), with request_state.rs l. 270 (`MIN_KEY_LENGTH =
      -- wire::MIN_KEY_LENGTH`) and request_state_wire.rs l. 19 (`= 32`)
      | .Err e =>
        key.val.length < minKeyLength ∧
        ∃ minimum actual : Std.Usize, e = .KeyTooShort minimum actual ∧
          minimum.val = minKeyLength ∧ actual.val = key.val.length ⦄ := by
  unfold validate_key_length
  -- `step*` closes the `Ok` branch from W02; the `KeyTooShort` branch remains.
  step*
  refine ⟨?_, MIN_KEY_LENGTH, Slice.len key, rfl, Proofs.RequestState.val_MIN_KEY_LENGTH, ?_⟩
  · simp_all only [Usize.ofNatCore_val_eq, false_eq_decide_iff, not_le, Bool.not_eq_true]
  · simp only [Usize.ofNatCore_val_eq]

end rmcp.model.request_state.RequestStateCodec
