/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire
import Proofs.Defs.RequestState
import Proofs.External.String
import Proofs.External.Std

/-!
# Shared helpers for the `request_state` codec proofs (E batch)

Facts about generated value constants of `request_state.rs`, used by several E proofs, and about
the UTF-8 content of Aeneas string literals. Unfolding a generated value constant (not a W
function) is allowed by the lead decision recorded in the S05 evidence (git history at 223ff12).
The equations `core.option.Option.ok_or_eq` and `core.result.Result.is_err_eq` are in
`Proofs/External/Std.lean`.
-/

open Aeneas Aeneas.Std Result

namespace Proofs.RequestState

/-- `RequestStateCodec::MIN_KEY_LENGTH` (request_state.rs line 270, `= wire::MIN_KEY_LENGTH`,
request_state_wire.rs line 19, `= 32`) has the value `Defs.Wire.minKeyLength`. -/
theorem val_MIN_KEY_LENGTH :
    rmcp.model.request_state.RequestStateCodec.MIN_KEY_LENGTH.val = Defs.Wire.minKeyLength := by
  simp only [rmcp.model.request_state.RequestStateCodec.MIN_KEY_LENGTH,
    rmcp.model.request_state_wire.MIN_KEY_LENGTH, UScalar.ofNatCore_val_eq, Defs.Wire.minKeyLength]

/-- The Aeneas `toStr` of a literal holds exactly the UTF-8 bytes of the literal. -/
theorem strIs_toStr (s : String) (h : s.toByteArray.size ≤ U32.max) :
    Defs.RequestState.StrIs (toStr s h) s := by
  unfold Defs.RequestState.StrIs
  rw [Proofs.External.Utf8.toStr_val, Proofs.External.Utf8.utf8_eq,
    Proofs.External.Utf8.byteArray_toList, List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply, Proofs.External.Byte.byte_val]
  exact Nat.mod_eq_of_lt (UInt8.toNat_lt x)

/-- `StrIs m s` (bytes compared as natural numbers) says exactly that the bytes of `m` are the
UTF-8 bytes `Defs.utf8Bytes s`. -/
theorem strIs_iff_val_eq_utf8Bytes (m : Str) (s : String) :
    Defs.RequestState.StrIs m s ↔ m.val = Defs.utf8Bytes s := by
  rw [Proofs.External.Utf8.utf8Bytes_eq_utf8, Proofs.External.Utf8.utf8_eq]
  unfold Defs.RequestState.StrIs
  rw [Proofs.External.Utf8.byteArray_toList]
  constructor
  · intro h
    apply List.map_injective_iff.2 (fun a b hab => UScalar.eq_of_val_eq hab)
    rw [h, List.map_map]
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply, Proofs.External.Byte.byte_val]
    exact (Nat.mod_eq_of_lt (UInt8.toNat_lt x)).symm
  · intro h
    rw [h, List.map_map]
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply, Proofs.External.Byte.byte_val]
    exact Nat.mod_eq_of_lt (UInt8.toNat_lt x)

end Proofs.RequestState
