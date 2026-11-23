/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire

/-!
# Spec theorem for `bytes_eq` (W04)

Byte-slice equality: a length check, then a loop comparing the bytes in order.

The loop invariant says that the bytes before the index agree.

Source: "crates/rmcp/src/model/request_state_wire.rs", line 65 in the patched copy
(patch 01 on origin/main 7caec76, D2 fallback 2026-11-23); line numbers refer to it.
-/

open Aeneas Aeneas.Std Result

namespace rmcp.model.request_state_wire

open Defs.Wire

/-- **Spec theorem for `rmcp::model::request_state_wire::bytes_eq`** (W04)

`bytes_eq a b` is `true` iff `a` and `b` are equal as byte lists (plan Section 2.1, W04;
lines 64–77: the length check of lines 66–68, then the bytewise loop of lines 69–76). No
precondition. -/
@[step]
theorem bytes_eq_spec (a : Slice U8) (b : Slice U8) :
    bytes_eq a b ⦃ (result : Bool) =>
      result = decide (a.val = b.val) ⦄ := by
  unfold bytes_eq
  dsimp only
  split
  · have hne : a.val.length ≠ b.val.length := by
      intro heq
      simp_all [Slice.len]
    simp only [WP.spec_ok]
    simp only [false_eq_decide_iff]
    intro h
    exact hne (by rw [h])
  · unfold bytes_eq_loop
    apply loop.spec_decr_nat (measure := fun i : Usize => a.length - i.val)
      (inv := fun i : Usize => i.val ≤ a.length ∧
        ∀ j (h1 : j < i.val), a.val[j]? = b.val[j]?)
    · intro i ⟨hi, hinv⟩
      unfold bytes_eq_loop.body
      step*
      · have hlt : i.val < a.val.length := by scalar_tac
        have hlb : i.val < b.val.length := by scalar_tac
        refine ⟨by scalar_tac, fun j hj => ?_, by scalar_tac⟩
        by_cases hji : j < i.val
        · exact hinv j hji
        · have : j = i.val := by omega
          subst this
          rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hlb, ← i2_post, ← i3_post]
          simp_all only [bne_iff_ne, ne_eq, Decidable.not_not]
      · have hab : a.val.length = b.val.length := by
          simp_all [Slice.len]
        have hia : i.val = a.val.length := by scalar_tac
        simp only [true_eq_decide_iff]
        apply List.ext_getElem?
        intro j
        by_cases hj : j < i.val
        · exact hinv j hj
        · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    · exact ⟨by scalar_tac, fun j hj => absurd hj (by scalar_tac)⟩

end rmcp.model.request_state_wire
