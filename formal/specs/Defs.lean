/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Aeneas
import Defs.Wire
import Defs.RequestState

/-!
# Defs

Root of the `Defs` library: definitions used by the spec statements (plan Section 5).
Maintained by hand (docs/WORKFLOW_AND_PR_GUIDE.md, "Library roots").

The root currently imports the S05 draft modules `Defs.Wire` and `Defs.RequestState` so that
the drafts under `formal/specs/Drafts/` can be checked against them (lead decision at S05).
Their definitions are not yet signed off: before this lands, the spec owner signs them off or
they are removed from this root (workflow guide, "Library roots").
-/
