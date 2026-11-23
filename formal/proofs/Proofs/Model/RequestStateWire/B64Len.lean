/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire

/-!
# Spec theorem for `b64_len` (W01)

Length of the unpadded Base64url encoding rounded up to whole quads: `4 * ceil(len / 3)`,
computed as `len / 3 * 4`, plus 4 when `len % 3 ≠ 0`. Stated on the no-overflow domain.

Source: "crates/rmcp/src/model/request_state_wire.rs", line 33 in the patched copy
(patch 01 on origin/main 7caec76, D2 fallback 2026-11-23); line numbers refer to it.
-/

open Aeneas Aeneas.Std Result

namespace rmcp.model.request_state_wire

open Defs.Wire

/-- **Spec theorem for `rmcp::model::request_state_wire::b64_len`** (W01)

On the no-overflow domain `4 * ceil(len / 3) ≤ Usize.max`, `b64_len len` returns
`4 * ceil(len / 3)` (plan Section 2.1, W01; lines 27–36). Overflow is failure in the Aeneas
model, matching debug builds with `overflow-checks` on (plan Section 3, "W01 and the seal
capacities"; Section 1). The hypothesis excludes the overflow case; that it is also necessary
(`len / 3 * 4 ≤ b64Len len`) is argued and checked by evaluation (evidence S05), not proved. -/
@[step]
theorem b64_len_spec (len : Usize)
    (h_no_overflow : b64Len len.val ≤ Usize.max) :
    b64_len len ⦃ (result : Usize) =>
      result.val = b64Len len.val ⦄ := by
  unfold b64_len
  unfold b64Len at h_no_overflow ⊢
  step*

end rmcp.model.request_state_wire
