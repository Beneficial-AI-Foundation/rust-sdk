/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire
import Proofs.Model.RequestStateWire.Common
import Proofs.Model.RequestStateWire.OpenFrame

/-!
# Spec theorem for `frame` (W15) and `frame_roundtrip`

Builds an authenticated body: the 8 big-endian bytes of `expiry as u64`, then the payload.
The round trip composes `frame_spec` with `open_frame_spec` (W14), using
`Proofs.RequestStateWire.bodyExpiry_frameBytes`.

Source: "crates/rmcp/src/model/request_state_wire.rs", line 239 in the patched copy
(patch 01 on origin/main 7caec76, D2 fallback 2026-11-23); line numbers refer to it.
-/

open Aeneas Aeneas.Std Result

namespace rmcp.model.request_state_wire

open Defs.Wire Proofs.RequestStateWire

/-- **Spec theorem for `rmcp::model::request_state_wire::frame`** (W15)

`frame expiry payload` is `be64(expiry as u64) ++ payload`: the 8 big-endian bytes of the
two's-complement representation of `expiry`, then the payload (plan Section 2.1, W15;
lines 238–244). The function does no arithmetic (plan Section 3).

Lean-model domain (plan Section 3, "Lean-model domains"): `h_len` says that the output fits in
`Usize.max` bytes, which excludes the Aeneas failure case of both `extend_from_slice` calls
(lines 241, 242; only this direction is proved); see `transcript_v1_spec` (TranscriptV1.lean). -/
@[step]
theorem frame_spec (expiry : I64) (payload : Slice U8)
    (h_len : (frameBytes expiry.val payload.val).length ≤ Usize.max) :
    frame expiry payload ⦃ (result : alloc.vec.Vec U8) =>
      result.val = frameBytes expiry.val payload.val ⦄ := by
  rw [length_frameBytes] at h_len
  unfold frame
  step*
  have hi : i.val = (expiry.val % 2 ^ 64).toNat := by
    rw [UScalar.val, i_post]
    exact IScalar.hcast_val_eq UScalarTy.U64 expiry
  rw [result_post, body_post, s_post, List.nil_append, Array.val_to_slice, a_post,
    map_mk_toBEBytes, hi, frameBytes, be64OfInt]

/-- **Frame round trip** (W15 then W14)

Opening a frame built by `frame expiry payload` at a time `now_ms` at which `expiry` is not
expired returns `Ok payload` (plan Section 3, "Round-trip": `open_frame (frame e p) now = Ok p`
when `¬ is_expired e now`). Premises: the frame fits in `Usize.max` bytes (`h_len`, the domain of
`frame_spec`), and `expiry` is `0` or `now_ms ≤ expiry` (`h_live`, the negation of the W13
predicate). About the translated functions `frame` and `open_frame`; the frame is passed to
`open_frame` as the slice of the returned vector (`Vec::deref`). The statement covers both
calls: it shows that both succeed and gives the final result. -/
theorem frame_roundtrip (expiry : I64) (payload : Slice U8) (now_ms : I64)
    (h_len : (frameBytes expiry.val payload.val).length ≤ Usize.max)
    (h_live : ¬ Expired expiry.val now_ms.val) :
    (do
      let body ← frame expiry payload
      open_frame (alloc.vec.Vec.deref body) now_ms)
      ⦃ (result : core.result.Result (Slice U8) FrameError) =>
      result = .Ok payload ⦄ := by
  have hE : bodyExpiry (frameBytes expiry.val payload.val) = expiry.val :=
    bodyExpiry_frameBytes _ _ (by scalar_tac) (by scalar_tac)
  step*
  have hd : (alloc.vec.Vec.deref body).val = frameBytes expiry.val payload.val := body_post
  have hlen : (alloc.vec.Vec.deref body).length = 8 + payload.length := by
    simp only [Slice.length, hd, length_frameBytes]
  rcases result with p' | e
  · obtain ⟨-, -, hp⟩ := result_post
    rw [hd, frameBytes, expiryLen, List.drop_left' (by simp [be64OfInt, be64])] at hp
    rw [Subtype.ext hp]
  · cases e with
    | TooShort =>
      simp only [hlen, expiryLen] at result_post
      omega
    | Expired =>
      obtain ⟨-, hx⟩ := result_post
      rw [hd, hE] at hx
      exact absurd hx h_live

end rmcp.model.request_state_wire
