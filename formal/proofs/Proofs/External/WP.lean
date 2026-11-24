/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Aeneas

@[expose] public section

/-!
# A weakest-precondition helper

`exists_ok_of_spec`: a computation that meets a postcondition returns `ok` of a value satisfying
it. Used to turn the signed-off spec theorems of the external models into equations
(`Proofs.External.String`; `Proofs.External.Std`: `ok_or_eq`, `is_err_eq` and the Phase 2 proofs
of `sliceEqSameLength_spec` and `strip_suffix_spec`), and in the proofs of `SamplingContent` (M10,
M12), `NumberOrString` (M06, M07), `Reference` (M13, M14), `Rs1FallbacksVerify` (E09a), `Auth`
(`bind_if_ok_true_spec`), `AsyncRw` (C05) and `Tower` (T08). `Proofs.Model.RequestStateWire.Common`
imports this module.
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

end Proofs.External.WP
