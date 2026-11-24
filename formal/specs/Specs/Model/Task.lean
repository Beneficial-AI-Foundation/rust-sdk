/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Defs
import Proofs.Model.Task

/-!
# Spec file for crates/rmcp/src/model/task.rs (Phase 2, public API: M08)

Summary (index of all guarantees: `formal/specs/README.md`). The row says that the call does not
panic and that its result satisfies the guarantee.

| ID | Function | Guarantee | Assumptions |
|---|---|---|---|
| M08 | `TaskStatus::is_terminal` | `true` exactly for `Completed`, `Failed`, `Cancelled` | none |

This file holds only the public API of `task.rs` (functions `pub` in upstream rmcp; human
decision 2026-11-24); `is_terminal` is `pub`, with the Rust path
`rmcp::model::TaskStatus::is_terminal` (`model.rs` line 38 re-exports `task` by `pub use task::*`).

The statement of `TaskStatus::is_terminal` (M08, plan Section 16.1), restated as
`Theorems.task.TaskStatus.is_terminal`, proved by the spec theorem in `Proofs/Model/Task.lean`
and followed by the assumptions its proof depends on, checked by `#print axioms` under
`#guard_msgs`. Signed off by the spec owner on 2026-11-24 (S24/S25 spec cycle,
`formal/docs/STATUS.md`); the signed-off text was in `specs/Drafts/Model.lean`, removed at
incorporation.

Translated configuration (the proof holds only for it): target `x86_64-unknown-linux-gnu`,
`--no-default-features` with the features `request-state`, `server`, `client`, `client-side-sse`,
`transport-streamable-http-server`, `transport-streamable-http-client` and `auth` (widened for
Phase 2, plan Section 15), with `overflow-checks=true` and `debug-assertions=true` (plan
Section 1). Aeneas `nightly-2026.08.20-5d08da4`. Line numbers refer to upstream `7caec76`.

Definitions used: none beyond plain Lean. External models used: none. Native-code assumptions
reached: none.

Statements here: M08 (line 38).

Not translated (outside the Phase 2 scope, plan Section 13, "Not claimed"): every other item of
`task.rs`.
-/

open Aeneas Aeneas.Std Result
open rmcp  -- for `model.…` in the statement; theorem named in full

/-- M08 `is_terminal`: `true` exactly for `Completed`, `Failed` and `Cancelled`. -/
theorem Theorems.task.TaskStatus.is_terminal (self : model.task.TaskStatus) :
    rmcp.model.task.TaskStatus.is_terminal self ⦃ (result : Bool) =>
      (result = true ↔ self = .Completed ∨ self = .Failed ∨ self = .Cancelled) ⦄ :=
  rmcp.model.task.TaskStatus.is_terminal_spec self

/--
info: 'Theorems.task.TaskStatus.is_terminal' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.task.TaskStatus.is_terminal
