/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.FunsExternal

@[expose] public section

/-!
# Facts about `ExtModel.byte`

`ExtModel.byte n` (`formal/trusted/Rmcp/FunsExternal.lean`) is the byte with value `n % 256`.
These facts are shared by the laws of the Base64url, UTF-8, integer-parsing and IP-address
models (`Proofs.External.{Base64, String, IntParse, Net}`).
-/

open Aeneas Aeneas.Std

namespace Proofs.External.Byte

open ExtModel

/-- The value of `byte n` is `n % 256`. -/
theorem byte_val (n : Nat) : (byte n).val = n % 256 := by
  rfl

/-- `byte n` is the byte `x` whose value is `n`. -/
theorem byte_eq {x : U8} {n : Nat} (h : n = x.val) : byte n = x := by
  apply UScalar.eq_of_val_eq
  rw [byte_val, h]
  have : x.val < 256 := by scalar_tac
  omega

/-- A byte value is below 256. -/
theorem val_lt (x : U8) : x.val < 256 := by scalar_tac

end Proofs.External.Byte
