/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Aeneas

@[expose] public section

/-!
# Weakest-precondition and `Result` helpers

`exists_ok_of_spec`: a computation that meets a postcondition returns `ok` of a value satisfying
it. Used to turn the signed-off spec theorems of the external models into equations
(`Proofs.External.String`; `Proofs.External.Std`: `ok_or_eq`, `is_err_eq` and the Phase 2 proofs
of `sliceEqSameLength_spec` and `strip_suffix_spec`), and in the proofs of `SamplingContent` (M10,
M12), `NumberOrString` (M06, M07), `Reference` (M13, M14), `Rs1FallbacksVerify` (E09a), `Auth`
(`bind_if_ok_true_spec`), `AsyncRw` (C05) and `Tower` (T08). `Proofs.Model.RequestStateWire.Common`
imports this module.

The section "Results" adds generic facts about `Result` and the Aeneas `Vec`, used first by the
`metadata_resolver.rs` proofs (`Proofs.Transport.MetadataResolver.Common`): a bind that returned
`ok` ran its first computation to `ok` (`bind_eq_ok_iff`, by `Result.cases` and the Aeneas lemmas
`ok_not_vis`, `ok_not_div`); `bind_ok` for a `Str` computation that returns a byte
slice (`bind_ok_str`) and after `into_iter` (`bind_into_iter`); `List.anyM` of a function that
always returns `ok` (`anyM_eq_ok`); and `Vec.push` on success and on a full vector
(`val_eq_of_push_eq_ok`, `push_eq_ok`, `push_eq_fail`).
-/

open Aeneas Aeneas.Std Result

namespace Proofs.External.WP

/-- A computation that meets a postcondition returns `ok` of a value satisfying it. The same as
`WP.spec_imp_exists` (removed from the Aeneas library in nightly-2026.11.24), proved by case
analysis. Since the Aeneas upgrade of 2026-11-24 it depends on `[propext, Classical.choice,
Quot.sound]`, through `WP.spec_ok` and `WP.spec_fail` of the new library, so M10 and M12
(`rmcp.model.SamplingContent.is_empty_spec`, `first_spec`) now list these three (pending the human
batch re-sign-off). Until 2026-11-24 it depended only on `propext`, which is why this form was
used: it kept the signed-off lists `[propext]` of M10 and M12. -/
theorem exists_ok_of_spec {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ x => P x ⦄) :
    ∃ y, m = ok y ∧ P y := by
  cases m with
  | ret y => exact ⟨y, rfl, (WP.spec_ok y).1 h⟩
  | vis i k =>
    cases i with
    | fail e =>
      have hk : k = PEmpty.elim := funext fun x => x.elim
      subst hk
      exact ((WP.spec_fail (p := P) e).1 (by rw [Result.fail_eq_vis]; exact h)).elim
  | div => exact (WP.spec_div.1 h).elim

/-! ## Results -/

universe u v

/-- A bind returns `ok` exactly when its first computation returns `ok x` and the continuation
returns `ok` on `x`. Stated for `Std.bind`, the bind of the extracted code (and of every `do` block
in a module that imports `Aeneas`). -/
theorem bind_eq_ok_iff {α : Type u} {β : Type v} {m : Result α} {f : α → Result β} {r : β} :
    Aeneas.Std.bind m f = ok r ↔ ∃ x, m = ok x ∧ f x = ok r := by
  constructor
  · intro h
    cases m using Result.cases with
    | ret x => exact ⟨x, rfl, by rwa [bind_ok] at h⟩
    | vis i k => rw [bind_vis] at h; exact absurd h.symm ok_not_vis
    | div => rw [bind_div] at h; exact absurd h.symm ok_not_div
  · rintro ⟨x, rfl, h⟩
    rwa [bind_ok]

/-- `bind_ok` for a `Str` computation that returns a slice of bytes (`Str` is `Slice U8`, but not
reducibly so, so `bind_ok` does not rewrite `bind (ok (α := Str) x) f` for `x : Slice U8`). -/
theorem bind_ok_str {β : Type v} (x : Slice U8) (f : Str → Result β) :
    Aeneas.Std.bind (ok (α := Str) x) f = f x :=
  bind_ok x f

/-- `into_iter` of a `Vec` returns the vector itself as an iterator (`IntoIter` is `Vec`, but not
reducibly so, so `bind_ok` does not rewrite the bind after `into_iter` is unfolded). -/
theorem bind_into_iter {T : Type u} {β : Type v} (v : alloc.vec.Vec T)
    (f : alloc.vec.into_iter.IntoIter T → Result β) :
    Aeneas.Std.bind (alloc.vec.IntoIteratorVec.into_iter v) f = f v :=
  bind_ok _ f

/-- `List.anyM` of a function that always returns `ok` is `ok` of `List.any`. -/
theorem anyM_eq_ok {α : Type u} (f : α → Result Bool) (g : α → Bool)
    (hf : ∀ x, f x = ok (g x)) (l : List α) : List.anyM f l = ok (l.any g) := by
  induction l with
  | nil => rw [List.anyM_nil]; rfl
  | cons x l ih =>
    rw [List.anyM_cons, hf, List.any_cons]
    cases g x
    · rw [bind_tc_ok, ite_eq_right Bool.false_ne_true, ih, Bool.false_or]
    · rw [bind_tc_ok, ite_eq_left rfl, Bool.true_or]; rfl

theorem val_eq_of_push_eq_ok {α : Type u} {v w : alloc.vec.Vec α} {x : α}
    (h : alloc.vec.Vec.push v x = ok w) : w.val = v.val ++ [x] := by
  unfold alloc.vec.Vec.push at h
  dsimp only at h
  split at h
  · rw [ok.injEq] at h; subst h
    rw [alloc.vec.Vec.from_val, List.concat_eq_append]
  · exact absurd h.symm ok_not_fail

theorem push_eq_ok {α : Type u} (v : alloc.vec.Vec α) (x : α) (h : v.val.length < Usize.max) :
    alloc.vec.Vec.push v x =
      ok (alloc.vec.Vec.from (v.val ++ [x]) (by rw [List.length_append]; exact h)) := by
  unfold alloc.vec.Vec.push
  rw [dite_eq_left (by rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]; omega)]
  simp only [List.concat_eq_append]

theorem push_eq_fail {α : Type u} (v : alloc.vec.Vec α) (x : α)
    (h : ¬ v.val.length < Usize.max) :
    alloc.vec.Vec.push v x = fail .maximumSizeExceeded := by
  unfold alloc.vec.Vec.push
  have hu : U32.max ≤ Usize.max := by
    simp only [U32.max, Usize.max, U32.numBits, Usize.numBits]
    rcases System.Platform.numBits_eq with h | h <;> simp [h]
  rw [dite_eq_right]
  rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq, not_or]
  omega

end Proofs.External.WP
