/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Defs
public import Specs.Model
public import Specs.Model.Task
public import Specs.Model.RequestState
public import Specs.Model.Skill

@[expose] public section

/-!
# Specs

Root of the `Specs` library: the specifications of the top-level public rmcp API (functions `pub`
in upstream rmcp that no other verified function calls; human decision 2026-11-28), one spec file
per Rust source file, each statement restated as a `theorem` in the `Theorems`
namespace and checked with `#guard_msgs` on `#print axioms` (plan Section 5; human decision
2026-11-24). Maintained by hand; nothing imports this library. Start at `formal/specs/README.md`.
Spec files: `Specs.Model` (M01–M05, M09–M14, the Section 16.1 joint lemmas, C03) and
`Specs.Model.Task` (M08), and `Specs.Model.RequestState` (the top-level public `request_state.rs`
functions R01–R04, R06, R07, R09, R11–R13, R15), and `Specs.Model.Skill` (the top-level public
`skill.rs` functions K01–K03, K05, K06, K08–K11, K16–K20, with their corollaries and compositions;
signed off 2026-11-25). Statements about intermediate public functions (called by a top-level
one: R05, R08, R10, R14, K04, K07, K12–K15), the consequences of the `Defs.Skill` model, private,
crate-internal and patch-only functions and the laws of the external models are in
`formal/proofs/Proofs/Internal/`, imported from `Proofs`.
-/
