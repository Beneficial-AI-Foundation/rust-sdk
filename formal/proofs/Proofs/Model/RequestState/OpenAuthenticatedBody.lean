/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Defs.Wire
public import Defs.CodecState
public import Proofs.Model.RequestStateWire.OpenFrame

@[expose] public section

/-!
# Spec theorem for `RequestStateCodec::open_authenticated_body` (E01)

Checks the framing and the expiry of an authenticated body with `request_state_wire::open_frame`
and maps its errors (`TooShort` to `MalformedFormat`, `Expired` to `Expired`); on success it
copies the payload into a new vector. The proof uses the W14 theorem `open_frame_spec` through
`step`, without unfolding the W function. The corollary `open_authenticated_body_openBody`
restates E01 as `Defs.CodecState.openBody` of the body bytes, the form E09 and E10 use.

Source: "crates/rmcp/src/model/request_state.rs", line 695 in the patched copy
(patch 01 on origin/main 7caec76, D2 fallback 2026-11-23); line numbers refer to it.
-/

open Aeneas Aeneas.Std Result
open rmcp
open rmcp.model.request_state
open Defs.Wire (bodyExpiry Expired expiryLen)

namespace rmcp.model.request_state.RequestStateCodec

/-- **Spec theorem for `rmcp::model::request_state::RequestStateCodec::open_authenticated_body`**
(E01)

Checks the framing and the expiry of an authenticated body and returns its payload, with no
precondition (the function never panics):

* a body shorter than `expiryLen = 8` bytes gives `MalformedFormat` (W14 `TooShort`);
* otherwise, a body that is expired at `now_ms` gives `Expired` (W14 `Expired`): with
  `Defs.Wire.bodyExpiry` (the signed big-endian value of the first 8 bytes) and
  `Defs.Wire.Expired` (nonzero and strictly before `now_ms`), the same terms as the W14
  statement of `open_frame`, so that it applies without conversion;
* otherwise the result is `Ok` of the bytes after the first 8 (`payload.to_vec()`).

The three cases are exclusive and exhaustive, so the result is determined exactly. The function
performs no authentication (plan Section 3, "W14/E01 — expiry"). -/
@[step]
theorem open_authenticated_body_spec (body : alloc.vec.Vec Std.U8) (now_ms : Std.I64) :
    open_authenticated_body body now_ms ⦃ (result :
        core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      match result with
      -- request_state.rs l. 698 (`Ok(payload) => Ok(payload.to_vec())`), with
      -- request_state_wire.rs l. 226 and 232 (not too short, not expired) and l. 235
      -- (`payload = &body[EXPIRY_LEN..]`, `EXPIRY_LEN = 8`, l. 17)
      | .Ok payload =>
        expiryLen ≤ body.val.length ∧
        ¬ Expired (bodyExpiry body.val) now_ms.val ∧
        payload.val = body.val.drop expiryLen
      | .Err e =>
        -- request_state.rs l. 699 (`TooShort => MalformedFormat`), with
        -- request_state_wire.rs l. 226–228 (`body.len() < EXPIRY_LEN`); checked first
        (body.val.length < expiryLen ∧ e = .MalformedFormat) ∨
        -- request_state.rs l. 700 (`Expired => Expired`), with request_state_wire.rs
        -- l. 229–234 (`is_expired(decode_expiry(head), now_ms)`); checked second
        (expiryLen ≤ body.val.length ∧ Expired (bodyExpiry body.val) now_ms.val ∧
          e = .Expired) ⦄ := by
  unfold open_authenticated_body
  step
  split
  · step
    simp_all only [Slice.length, alloc.vec.Vec.deref, Slice.from_val, alloc.vec.Vec.val,
      not_false_eq_true, and_self]
  · rename_i fe
    cases fe <;> simp_all only [Slice.length, alloc.vec.Vec.deref, Slice.from_val,
      and_false, WP.spec_ok, reduceCtorEq, or_false, and_true, false_or]

/-- E01 in the form used by E09 and E10: the result of `open_authenticated_body`, as
`Defs.CodecState.resultBytes`, is `Defs.CodecState.openBody` of the body bytes. -/
theorem open_authenticated_body_openBody (body : alloc.vec.Vec Std.U8) (now_ms : Std.I64) :
    open_authenticated_body body now_ms ⦃ (result :
        core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      Defs.CodecState.resultBytes result = Defs.CodecState.openBody body.val now_ms.val ⦄ := by
  apply WP.spec_mono (open_authenticated_body_spec body now_ms)
  intro r hr
  unfold Defs.CodecState.openBody
  rcases r with p | e
  · obtain ⟨h1, h2, h3⟩ := hr
    rw [ite_eq_right (by omega), ite_eq_right h2, ← h3]
    rfl
  · rcases hr with ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
    · rw [ite_eq_left h1]
      rfl
    · rw [ite_eq_right (by omega), ite_eq_left h2]
      rfl

end rmcp.model.request_state.RequestStateCodec
