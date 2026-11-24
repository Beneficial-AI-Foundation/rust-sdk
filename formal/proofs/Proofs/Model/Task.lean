/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs

@[expose] public section

/-!
# Spec theorem for `TaskStatus::is_terminal` (M08)

`true` exactly for the statuses `Completed`, `Failed` and `Cancelled`.

Source: "crates/rmcp/src/model/task.rs", line 38 at `7caec76`
-/

open Aeneas Aeneas.Std Result

namespace rmcp.model.task.TaskStatus

/-- **Spec theorem for `rmcp::model::task::TaskStatus::is_terminal`** (M08)

`true` exactly for `Completed`, `Failed` and `Cancelled`; `false` for `Working` and
`InputRequired` (plan Section 16.1, M08; `task.rs` lines 37–40, doc comment "Returns `true` for
terminal statuses (`completed`, `failed`, `cancelled`)" and `matches!(self, Self::Completed |
Self::Failed | Self::Cancelled)`). Restated as `Theorems.task.TaskStatus.is_terminal`. -/
@[step]
theorem is_terminal_spec (self : model.task.TaskStatus) :
    is_terminal self ⦃ (result : Bool) =>
      (result = true ↔ self = .Completed ∨ self = .Failed ∨ self = .Cancelled) ⦄ := by
  match self with
  | .Working =>
    simp only [is_terminal, reduceCtorEq, or_self, iff_false, Bool.not_eq_true, WP.spec_ok]
  | .InputRequired =>
    simp only [is_terminal, reduceCtorEq, or_self, iff_false, Bool.not_eq_true, WP.spec_ok]
  | .Completed => simp only [is_terminal, reduceCtorEq, or_self, or_false, iff_true, WP.spec_ok]
  | .Failed => simp only [is_terminal, reduceCtorEq, or_false, or_true, iff_true, WP.spec_ok]
  | .Cancelled => simp only [is_terminal, reduceCtorEq, or_true, iff_true, WP.spec_ok]

end rmcp.model.task.TaskStatus
