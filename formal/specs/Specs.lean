/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Defs
import Proofs
import Specs.Model.RequestStateWire
import Specs.Model.RequestState
import Specs.External

/-!
# Specs

Root of the `Specs` library: one spec file per Rust source file, each statement restated
as a `theorem` in the `Theorems` namespace and checked with `#guard_msgs` on `#print axioms`
(plan Section 5).
Maintained by hand; nothing imports this library. Spec files:
`Specs.Model.RequestStateWire` (W01–W15, `frame_roundtrip`);
`Specs.Model.RequestState` (E01–E04);
`Specs.External` (laws of the external models, S08–S09).
-/
