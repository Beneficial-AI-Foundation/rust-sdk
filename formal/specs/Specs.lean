/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Defs
import Proofs
import Specs.Model
import Specs.Model.Task
import Specs.Model.RequestState

/-!
# Specs

Root of the `Specs` library: the specifications of the public rmcp API (functions `pub` in upstream
rmcp), one spec file per Rust source file, each statement restated as a `theorem` in the `Theorems`
namespace and checked with `#guard_msgs` on `#print axioms` (plan Section 5; human decision
2026-11-24). Maintained by hand; nothing imports this library. Start at `formal/specs/README.md`.
Spec files: `Specs.Model` (M01–M05, M09–M14, the Section 16.1 joint lemmas, C03) and
`Specs.Model.Task` (M08), and `Specs.Model.RequestState` (R01–R08, the public `request_state.rs`
functions). Statements about private, crate-internal and patch-only functions and the
laws of the external models are in `formal/proofs/Proofs/Internal/`, imported from `Proofs`.
-/
