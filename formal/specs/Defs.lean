/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Aeneas
import Defs.Wire
import Defs.RequestState
import Defs.CodecState
import Defs.Bytes
import Defs.IntParse
import Defs.JsonRpc
import Defs.Methods
import Defs.Tower
import Defs.Sse
import Defs.Net

/-!
# Defs

Root of the `Defs` library: definitions used by the spec statements (plan Section 5).
Maintained by hand (docs/WORKFLOW_AND_PR_GUIDE.md, "Library roots").

Imports `Defs.Wire`, `Defs.RequestState` and `Defs.CodecState`, whose definitions the spec owner
signed off at S05 (2026-11-23; the S05 evidence (git history at 223ff12)), as the workflow guide's "Library roots"
requires.

Phase 2: `Defs.Bytes`, `Defs.IntParse`, `Defs.JsonRpc`, `Defs.Methods` and `Defs.Tower` (signed
off at S24) and `Defs.Sse` and `Defs.Net` (signed off at S25), both on 2026-11-24 by the spec owner
(`formal/docs/STATUS.md`, "S24 spec cycle" and "S25 spec cycle").
-/
