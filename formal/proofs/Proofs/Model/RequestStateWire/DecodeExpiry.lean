/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire

/-!
# Spec theorem for `decode_expiry` (W12)

`u64::from_be_bytes(head) as i64`: the two's-complement value of 8 big-endian bytes.

The proof computes the value of the Aeneas `BitVec.fromLEBytes` and relates the big-endian
reading to `Defs.Wire.beNat`.

Source: "crates/rmcp/src/model/request_state_wire.rs", line 205 at local commit `46cfb02`
(the translation base; not yet a pinned fork commit).
-/

open Aeneas Aeneas.Std Result

namespace Proofs.RequestStateWire

open Defs.Wire

/-- The value of a little-endian byte list. -/
theorem toNat_fromLEBytes (l : List Byte) :
    (BitVec.fromLEBytes l).toNat = l.foldr (fun b acc => b.toNat + 256 * acc) 0 := by
  induction l with
  | nil => simp [BitVec.fromLEBytes]
  | cons b l ih =>
    rw [BitVec.fromLEBytes]
    have hb : b.toNat < 2 ^ 8 := b.isLt
    have hl : (BitVec.fromLEBytes l).toNat < 2 ^ (8 * l.length) := (BitVec.fromLEBytes l).isLt
    simp only [BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, List.foldr_cons,
      List.length_cons]
    rw [← ih]
    generalize (BitVec.fromLEBytes l).toNat = x at hl ⊢
    generalize b.toNat = c at hb ⊢
    have h1 : 2 ^ (8 * (l.length + 1)) = 2 ^ (8 * l.length) * 2 ^ 8 := by
      rw [← Nat.pow_add, Nat.mul_add, Nat.mul_one]
    have hx : x % 2 ^ (8 * (l.length + 1)) = x := Nat.mod_eq_of_lt (by
      rw [h1]; have : 0 < 2 ^ 8 := by norm_num
      nlinarith)
    have hc : c % 2 ^ (8 * (l.length + 1)) = c := Nat.mod_eq_of_lt (by
      rw [h1]; have : 0 < 2 ^ (8 * l.length) := Nat.pow_pos (by norm_num)
      nlinarith)
    rw [hx, hc, Nat.shiftLeft_eq]
    have hs : x * 2 ^ 8 % 2 ^ (8 * (l.length + 1)) = x * 2 ^ 8 := Nat.mod_eq_of_lt (by
      rw [h1]; have : 0 < 2 ^ 8 := by norm_num
      nlinarith)
    rw [hs, Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hb,
      Nat.shiftLeft_eq]
    omega

/-- The value of a big-endian byte list is `Defs.Wire.beNat`. -/
theorem toNat_fromBEBytes (l : List U8) :
    (BitVec.fromBEBytes (l.map U8.bv)).toNat = beNat l := by
  rw [BitVec.fromBEBytes, BitVec.toNat_cast, toNat_fromLEBytes, List.foldr_reverse, beNat,
    List.foldl_map]
  congr 1
  funext acc x
  exact Nat.add_comm _ _

end Proofs.RequestStateWire

namespace rmcp.model.request_state_wire

open Defs.Wire

/-- **Spec theorem for `rmcp::model::request_state_wire::decode_expiry`** (W12)

`decode_expiry head` is the two's-complement value of the 8 bytes of `head` read big-endian
(plan Section 2.1, W12; lines 204–207: `u64::from_be_bytes(head) as i64`). No precondition. -/
@[step]
theorem decode_expiry_spec (head : Array U8 8#usize) :
    decode_expiry head ⦃ (result : I64) =>
      result.val = toInt64 (beNat head.val) ⦄ := by
  unfold decode_expiry
  step
  have hi : i.val = beNat head.val := by
    simp only [UScalar.val, i_post, BitVec.toNat_cast, Proofs.RequestStateWire.toNat_fromBEBytes]
  have hlt : i.val < 2 ^ 64 := i.bv.isLt
  rw [UScalar.hcast_val_eq, ← hi, toInt64]
  simp only [IScalarTy.I64_numBits_eq, Int.bmod]
  split_ifs <;> omega

end rmcp.model.request_state_wire
