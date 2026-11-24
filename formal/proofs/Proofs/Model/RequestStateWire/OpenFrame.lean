/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Proofs.Defs.Wire
import Proofs.Model.RequestStateWire.DecodeExpiry
import Proofs.Model.RequestStateWire.IsExpired

/-!
# Spec theorem for `open_frame` (W14)

Opens an authenticated body: `TooShort` below 8 bytes, `Expired` when W13 holds for the W12
value of the first 8 bytes, otherwise the bytes after the expiry prefix. The proof uses
`decode_expiry_spec` and `is_expired_spec` through `step`.

Source: "crates/rmcp/src/model/request_state_wire.rs", line 225 in the patched copy
(patch 01 on origin/main 7caec76, D2 fallback 2026-11-23); line numbers refer to it.
-/

open Aeneas Aeneas.Std Result

namespace rmcp.model.request_state_wire

open Defs.Wire

/-- **Spec theorem for `rmcp::model::request_state_wire::open_frame`** (W14)

`open_frame body now_ms` (plan Section 2.1, W14; lines 224–236), in the Rust order of checks:
`Err TooShort` iff `body` is shorter than `EXPIRY_LEN = 8` bytes (lines 17, 226–228);
`Err Expired` iff it has at least 8 bytes and W13 holds for the W12 value of its first 8 bytes
(lines 229–234); otherwise `Ok (body[8..])` (line 235). `now_ms = expiry` is accepted, and a
negative nonzero expiry is compared as a signed value (plan Section 3, "W14/E01 — expiry").
The returned slice is determined by its byte list. No precondition. -/
@[step]
theorem open_frame_spec (body : Slice U8) (now_ms : I64) :
    open_frame body now_ms ⦃ (result : core.result.Result (Slice U8) FrameError) =>
      match result with
      | .Err .TooShort => body.length < expiryLen
      | .Err .Expired => expiryLen ≤ body.length ∧ Expired (bodyExpiry body.val) now_ms.val
      | .Ok payload =>
        expiryLen ≤ body.length ∧ ¬ Expired (bodyExpiry body.val) now_ms.val ∧
        payload.val = body.val.drop expiryLen ⦄ := by
  unfold open_frame
  simp only [EXPIRY_LEN]
  step*
  · simp only [expiryLen]; scalar_tac
  all_goals
    have hlen : 8 ≤ body.length := by scalar_tac
    have hE : bodyExpiry body.val = i9.val := by
      rw [i9_post, bodyExpiry, expiryLen]
      congr 2
      apply List.ext_getElem
      · simp only [List.length_take, List.Vector.length_val, UScalar.ofNatCore_val_eq, inf_eq_left]
        omega
      · intro n h1 h2
        simp only [List.length_take] at h1
        have : n < 8 := by omega
        rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n
        all_goals first | omega | simp only [zero_add, Nat.reduceAdd, List.getElem_take, Array.make,
          List.getElem_cons_succ, List.getElem_cons_zero, i1_post, i2_post, i3_post, i4_post,
          i5_post, i6_post, i7_post, i8_post]
    rw [hE]
    simp_all only [true_eq_decide_iff, false_eq_decide_iff, Bool.not_eq_true, Slice.length,
      List.length_drop, expiryLen, not_false_eq_true, and_self]

end rmcp.model.request_state_wire
