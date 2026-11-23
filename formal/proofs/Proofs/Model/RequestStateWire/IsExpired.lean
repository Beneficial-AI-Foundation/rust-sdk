/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire

/-!
# Spec theorem for `is_expired` (W13)

An expiry is reached when it is nonzero and `now_ms` is strictly after it (signed comparison).

Source: "crates/rmcp/src/model/request_state_wire.rs", line 210 at local commit `22b9f13`
(the translation base; not yet a pinned fork commit).
-/

open Aeneas Aeneas.Std Result

namespace rmcp.model.request_state_wire

open Defs.Wire

/-- **Spec theorem for `rmcp::model::request_state_wire::is_expired`** (W13)

`is_expired expiry now_ms` is `true` iff `expiry ≠ 0 ∧ now_ms > expiry`, compared as signed
integers (plan Section 2.1, W13; plan Section 3, "W14/E01 — expiry"; lines 209–212). No
precondition. -/
@[step]
theorem is_expired_spec (expiry : I64) (now_ms : I64) :
    is_expired expiry now_ms ⦃ (result : Bool) =>
      result = decide (Expired expiry.val now_ms.val) ⦄ := by
  unfold is_expired
  simp [Expired]
  split_ifs <;> simp_all

end rmcp.model.request_state_wire
