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
import Specs.Model
import Specs.Model.Task
import Specs.Transport.Common.ClientSideSse
import Specs.Transport.AsyncRw
import Specs.Transport.StreamableHttpServer.Tower
import Specs.Transport.Auth

/-!
# Specs

Root of the `Specs` library: one spec file per Rust source file, each statement restated
as a `theorem` in the `Theorems` namespace and checked with `#guard_msgs` on `#print axioms`
(plan Section 5).
Maintained by hand; nothing imports this library. Spec files:
`Specs.Model.RequestStateWire` (W01–W15, `frame_roundtrip`);
`Specs.Model.RequestState` (E01–E04);
`Specs.External` (laws of the external models, S08–S09, S26–S27);
Phase 2 (2026-11-24): `Specs.Model` (M01–M07, M09–M14, joint lemmas, C03), `Specs.Model.Task`
(M08), `Specs.Transport.Common.ClientSideSse` (T01–T03, C01, C02), `Specs.Transport.AsyncRw`
(T04–T06, C05), `Specs.Transport.StreamableHttpServer.Tower` (T07, T08), `Specs.Transport.Auth`
(A01–A03, C04).
-/
