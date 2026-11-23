/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire

/-!
# Spec theorem for `check_kid_len` (W03)

Checks a key-id length: `0` is `Empty`, more than `MAX_KID_LEN = 255` is `TooLong`,
otherwise `Ok`.

Source: "crates/rmcp/src/model/request_state_wire.rs", line 54 at local commit `22b9f13`
(the translation base; not yet a pinned fork commit).
-/

open Aeneas Aeneas.Std Result

namespace rmcp.model.request_state_wire

open Defs.Wire

/-- **Spec theorem for `rmcp::model::request_state_wire::check_kid_len`** (W03)

`check_kid_len len` returns `Err Empty` iff `len = 0` (lines 55–57), `Err TooLong` iff
`len > MAX_KID_LEN = 255` (lines 21, 58–60), and `Ok ()` otherwise (line 61); plan Section 2.1,
W03. The arms are in the Rust order of checks. Any length in `1..=255` is accepted, with no
alphabet restriction (plan Section 3, "W03/E04 — kid alphabet"). No precondition. -/
@[step]
theorem check_kid_len_spec (len : Usize) :
    check_kid_len len ⦃ (result : core.result.Result Unit KidError) =>
      match result with
      | .Err .Empty => len.val = 0
      | .Err .TooLong => maxKidLen < len.val
      | .Ok () => 0 < len.val ∧ len.val ≤ maxKidLen ⦄ := by
  unfold check_kid_len
  simp [MAX_KID_LEN, maxKidLen]
  split_ifs <;> simp_all
  scalar_tac

end rmcp.model.request_state_wire
