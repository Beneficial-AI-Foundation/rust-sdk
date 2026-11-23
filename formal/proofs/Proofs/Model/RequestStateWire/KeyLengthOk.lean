/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire

/-!
# Spec theorem for `key_length_ok` (W02)

Whether a key length reaches `MIN_KEY_LENGTH = 32` bytes.

Source: "crates/rmcp/src/model/request_state_wire.rs", line 39 at local commit `22b9f13`
(the translation base; not yet a pinned fork commit).
-/

open Aeneas Aeneas.Std Result

namespace rmcp.model.request_state_wire

open Defs.Wire

/-- **Spec theorem for `rmcp::model::request_state_wire::key_length_ok`** (W02)

`key_length_ok len` is `true` iff `len ≥ MIN_KEY_LENGTH = 32` (plan Section 2.1, W02;
lines 19 and 38–41). No precondition. -/
@[step]
theorem key_length_ok_spec (len : Usize) :
    key_length_ok len ⦃ (result : Bool) =>
      result = decide (minKeyLength ≤ len.val) ⦄ := by
  unfold key_length_ok
  simp [MIN_KEY_LENGTH, minKeyLength]

end rmcp.model.request_state_wire
