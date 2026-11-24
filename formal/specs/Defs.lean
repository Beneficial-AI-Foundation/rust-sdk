/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Aeneas
import Defs.Bytes
import Defs.IntParse
import Defs.JsonRpc
import Defs.Wire
import Defs.CodecState

/-!
# Defs

Root of the `Defs` library: the definitions used by the public spec statements (plan Section 5).
Maintained by hand (docs/WORKFLOW_AND_PR_GUIDE.md, "Library roots"). Imports `Defs.Bytes`,
`Defs.IntParse` and `Defs.JsonRpc` (signed off at S24, 2026-11-24) and `Defs.Wire`,
`Defs.CodecState` (signed off at S05; back here since the public `request_state.rs` statements use
them). The definitions used only by internal statements (`Defs.RequestState` signed off at S05;
`Defs.Methods`, `Defs.Tower` at S24; `Defs.Sse`, `Defs.Net` at S25) live in modules
`Proofs.Defs.*` under `formal/proofs/Proofs/Defs/`, with their Lean names unchanged (human decision
2026-11-24).
-/
