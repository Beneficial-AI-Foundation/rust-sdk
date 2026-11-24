/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Aeneas

/-!
# Spec of the slice iterator `next`

Spec theorem for `core::slice::iter::Iter::next` as modelled by the Aeneas library
(`Aeneas/Std/SliceIter.lean`, an index into the slice): it yields the element at the index and
advances, or returns `None` at the end without changing the iterator. Its equation forms
`next_eq_some_of_lt` and `next_eq_none_of_le` serve loop proofs that unfold the loop body. Used
by the `for` loop of `rs1_fallbacks_verify` (E09a, "crates/rmcp/src/model/request_state.rs",
line 651 in the patched copy: patch 01 on origin/main 7caec76; line numbers refer to it).
-/

open Aeneas Aeneas.Std Result

/-- Below the end of the slice, `next` yields the element at the index and moves one index on.
An equation form of `next_spec` for loop proofs. -/
theorem core.slice.iter.IteratorSliceIter.next_eq_some_of_lt {T : Type} (s : Slice T) (i : Nat)
    (h : i < s.val.length) :
    core.slice.iter.IteratorSliceIter.next (⟨s, i⟩ : core.slice.iter.Iter T) =
      ok (some s.val[i], ⟨s, i + 1⟩) := by
  rw [core.slice.iter.IteratorSliceIter.next, dif_pos (by rw [Slice.len_val]; exact h)]
  rfl

/-- At or beyond the end of the slice, `next` yields `none` and leaves the iterator unchanged.
An equation form of `next_spec` for loop proofs. -/
theorem core.slice.iter.IteratorSliceIter.next_eq_none_of_le {T : Type} (s : Slice T) (i : Nat)
    (h : s.val.length ≤ i) :
    core.slice.iter.IteratorSliceIter.next (⟨s, i⟩ : core.slice.iter.Iter T) =
      ok (none, ⟨s, i⟩) := by
  rw [core.slice.iter.IteratorSliceIter.next,
    dif_neg (by rw [Slice.len_val]; exact Nat.not_lt.2 h)]

/-- **Spec theorem for `core::slice::iter::{impl Iterator for Iter<'_, T>}::next`**

Below the end of the slice, `next` returns the element at index `it.i` and the iterator moved one
index on; at or beyond the end it returns `None` and the iterator unchanged. It never panics. -/
@[step]
theorem core.slice.iter.IteratorSliceIter.next_spec {T : Type} [Inhabited T]
    (it : core.slice.iter.Iter T) :
    core.slice.iter.IteratorSliceIter.next it ⦃ (result : Option T × core.slice.iter.Iter T) =>
      (it.i < it.slice.length ∧ result.1 = some (it.slice.val[it.i]!) ∧
        result.2 = {it with i := it.i + 1}) ∨
      (it.slice.length ≤ it.i ∧ result = (none, it)) ⦄ := by
  obtain ⟨s, i⟩ := it
  by_cases h : i < s.val.length
  · rw [core.slice.iter.IteratorSliceIter.next_eq_some_of_lt s i h, WP.spec_ok]
    exact Or.inl ⟨h, by rw [getElem!_pos s.val i h], rfl⟩
  · rw [core.slice.iter.IteratorSliceIter.next_eq_none_of_le s i (Nat.not_lt.1 h), WP.spec_ok]
    exact Or.inr ⟨Nat.not_lt.1 h, rfl⟩
