/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire
import Proofs.Model.RequestStateWire.B64Len

/-!
# Spec theorem for `RequestStateCodec::b64_len` (E02)

Delegates to `request_state_wire::b64_len`; the proof uses the W01 theorem `b64_len_spec`
through `step`, without unfolding the W function.

Source: "crates/rmcp/src/model/request_state.rs", line 725 at local commit `46cfb02`
(the translation base; not yet a pinned fork commit).
-/

open Aeneas Aeneas.Std Result
open rmcp
open rmcp.model.request_state
open Defs.Wire (b64Len)

namespace rmcp.model.request_state.RequestStateCodec

/-- **Spec theorem for `rmcp::model::request_state::RequestStateCodec::b64_len`** (E02)

The unpadded Base64url length bound `Defs.Wire.b64Len len = 4 * ceil(len / 3)`, the same value
and the same premise as the W01 statement of `request_state_wire::b64_len` (plan Section 2.2,
"equals W01"; lead decision at S05: use the `Defs.Wire` definitions).

Domain: `h_no_overflow : b64Len len ≤ Usize.max`. This is exactly the set of inputs on which
the Rust code does not overflow: `len / 3 * 4` overflows only if `4 * (len / 3)` exceeds
`usize::MAX`, and `full + 4` (taken iff `len % 3 ≠ 0`, when `len / 3 + 1 = (len + 2) / 3`)
only if `4 * ((len + 2) / 3)` does. Equivalently `len ≤ 3 * (Usize.max / 4)`; on a 64-bit
`Usize` the largest admissible `len` is `13835058055282163709` (plan Section 7, W01/E02).
Overflow is failure in the Lean model, which matches debug
builds (`overflow-checks=true`, plan Sections 1 and 3); release builds would wrap. -/
@[step]
theorem b64_len_spec (len : Std.Usize)
    (h_no_overflow : b64Len len.val ≤ Usize.max) :
    b64_len len ⦃ (result : Std.Usize) =>
      -- request_state.rs l. 725–727 (`wire::b64_len(len)`), with request_state_wire.rs
      -- l. 33–36 (`full = len / 3 * 4`; `full` if `len % 3 == 0`, else `full + 4`)
      result.val = b64Len len.val ⦄ := by
  unfold b64_len
  step*

end rmcp.model.request_state.RequestStateCodec
