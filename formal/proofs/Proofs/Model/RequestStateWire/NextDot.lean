/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire

/-!
# Spec theorem for `next_dot` (W05)

Index of the first `.` at or after `start`, or `s.len()` if there is none.

The loop invariant says that the index has not moved below `start` and that no `.` lies in
`[start, i)`; the measure is `s.len() - i`.

Source: "crates/rmcp/src/model/request_state_wire.rs", line 80 at local commit `46cfb02`
(the translation base; not yet a pinned fork commit).
-/

open Aeneas Aeneas.Std Result

namespace rmcp.model.request_state_wire

open Defs.Wire

/-- **Spec theorem for `rmcp::model::request_state_wire::next_dot`** (W05)

`next_dot s start` is the least index `i ≥ start` with `s[i] = '.'`, or `s.len()` if there is
none (plan Section 2.1, W05; lines 79–89). The first conjunct says that no `.` lies in
`[start, result)`; the second that `result` is `s.len()` or a `.` at or after `start`. Together
they determine `result`. When `start > s.len()` the loop does not run and the result is
`s.len()` (line 88; plan Section 7, `start > len`). No precondition: `i + 1` (line 86) is only
computed for `i < s.len() ≤ Usize.max`. -/
@[step]
theorem next_dot_spec (s : Slice U8) (start : Usize) :
    next_dot s start ⦃ (result : Usize) =>
      (∀ j, start.val ≤ j → j < result.val → s.val[j]? ≠ some dot) ∧
      (result.val = s.length ∨
        (start.val ≤ result.val ∧ s.val[result.val]? = some dot)) ⦄ := by
  unfold next_dot next_dot_loop
  apply loop.spec_decr_nat (measure := fun i : Usize => s.length - i.val)
    (inv := fun i : Usize => start.val ≤ i.val ∧
      ∀ j, start.val ≤ j → j < i.val → s.val[j]? ≠ some dot)
  · intro i ⟨hsi, hinv⟩
    unfold next_dot_loop.body
    step*
    · have hlt : i.val < s.val.length := by scalar_tac
      refine ⟨hinv, Or.inr ⟨hsi, ?_⟩⟩
      rw [List.getElem?_eq_getElem hlt, ← i2_post]
      simp_all [dot]
    · have hlt : i.val < s.val.length := by scalar_tac
      refine ⟨by omega, fun j h1 h2 => ?_, by scalar_tac⟩
      by_cases hj : j < i.val
      · exact hinv j h1 hj
      · have : j = i.val := by omega
        subst this
        rw [List.getElem?_eq_getElem hlt, ← i2_post]
        simp_all [dot]
  · exact ⟨le_refl _, fun j h1 h2 => absurd h2 (by omega)⟩

end rmcp.model.request_state_wire
