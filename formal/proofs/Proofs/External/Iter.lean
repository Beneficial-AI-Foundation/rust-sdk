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
advances, or returns `None` at the end without changing the iterator. Used by the `for` loop of
`rs1_fallbacks_verify` (E09a, "crates/rmcp/src/model/request_state.rs", line 651).
-/

open Aeneas Aeneas.Std Result

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
  unfold core.slice.iter.IteratorSliceIter.next
  split
  · rename_i h
    simp only [WP.spec_ok]
    left
    refine ⟨by simpa [Slice.len, Slice.length] using h, ?_⟩
    simp [Slice.len] at h
    simp [getElem!_def, List.getElem?_eq_getElem h]
    rfl
  · rename_i h
    simp only [WP.spec_ok]
    right
    simpa [Slice.len, Slice.length] using h
