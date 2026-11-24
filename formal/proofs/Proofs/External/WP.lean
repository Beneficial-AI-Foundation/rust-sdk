/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Aeneas

/-!
# A weakest-precondition helper

`exists_ok_of_spec`: a computation that meets a postcondition returns `ok` of a value satisfying
it. Used to turn the signed-off spec theorems of the external models into equations
(`Proofs.External.{String, Std}`), and in the proofs of `SamplingContent` (M10, M12),
`Rs1FallbacksVerify` (E09a) and `Auth` (`bind_if_ok_true_spec`).
-/

open Aeneas Aeneas.Std Result

namespace Proofs.External.WP

/-- A computation that meets a postcondition returns `ok` of a value satisfying it. The same as
`WP.spec_imp_exists`, but proved by case analysis, so it depends only on `propext`. M10 and M12
(`rmcp.model.SamplingContent.is_empty_spec`, `first_spec`) need this form to keep their
signed-off axioms `[propext]`; the joint lemmas that use it depend on `[propext,
Classical.choice, Quot.sound]` anyway. -/
theorem exists_ok_of_spec {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ x => P x ⦄) :
    ∃ y, m = ok y ∧ P y := by
  cases m with
  | ok y => exact ⟨y, rfl, (WP.spec_ok y).1 h⟩
  | fail e => exact ((WP.spec_fail e).1 h).elim
  | div => exact (WP.spec_div.1 h).elim

end Proofs.External.WP
