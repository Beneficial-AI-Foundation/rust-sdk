/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Proofs.Defs.Wire
import Proofs.Defs.RequestState
import Proofs.External.Std
import Proofs.Model.RequestStateWire.CheckKidLen
import Proofs.Model.RequestState.Common

/-!
# Spec theorem for `RequestStateCodec::validate_config_kid` (E04)

Checks the byte length of a configured key id: `0` gives `InvalidKeyring(KID_EMPTY_MSG)`, more
than `MAX_KID_LEN = 255` gives `InvalidKeyring(KID_TOO_LONG_MSG)`, otherwise `Ok(())`.

Source: "crates/rmcp/src/model/request_state.rs", line 714 in the patched copy
(patch 01 on origin/main 7caec76, D2 fallback 2026-11-23); line numbers refer to it.
-/

open Aeneas Aeneas.Std Result
open rmcp
open rmcp.model.request_state
open Defs.Wire (maxKidLen)

namespace rmcp.model.request_state.RequestStateCodec

/-- **Spec theorem for `rmcp::model::request_state::RequestStateCodec::validate_config_kid`**
(E04)

With no precondition (the function never panics), on the UTF-8 byte length of `kid` (the length
of the byte list that the translated `Str` is):

* `Ok ()` iff the length is in `1..=maxKidLen` (`MAX_KID_LEN = 255`);
* a length of `0` gives `InvalidKeyring` with the text of `KID_EMPTY_MSG`;
* a length above 255 gives `InvalidKeyring` with the text of `KID_TOO_LONG_MSG`.

The two message texts differ. Any bytes are accepted: there is no alphabet restriction (plan
Section 3, "W03/E04 — kid alphabet"). The length is read by `core.str.Str.len` (request_state.rs
l. 715, `kid.len()`), modelled since S09 as the byte length of `kid` (plan Section 4). -/
@[step]
theorem validate_config_kid_spec (kid : Str) :
    validate_config_kid kid ⦃ (result : core.result.Result Unit RequestStateError) =>
      match result with
      -- request_state.rs l. 715–716 (`check_kid_len(kid.len())` is `Ok`), with
      -- request_state_wire.rs l. 54–62 (`len != 0`, `len <= MAX_KID_LEN`) and l. 21 (`= 255`)
      | .Ok _ =>
        1 ≤ (kid : Slice Std.U8).val.length ∧ (kid : Slice Std.U8).val.length ≤ maxKidLen
      | .Err e =>
        -- request_state.rs l. 717 (`Empty => InvalidKeyring(KID_EMPTY_MSG)`), with
        -- request_state_wire.rs l. 55–57 (`len == 0`); checked first. Message text:
        -- request_state.rs l. 86
        ((kid : Slice Std.U8).val.length = 0 ∧
          ∃ msg, e = .InvalidKeyring msg ∧ Defs.RequestState.StrIs msg
            Defs.RequestState.kidEmptyMsg) ∨
        -- request_state.rs l. 718–720 (`TooLong => InvalidKeyring(KID_TOO_LONG_MSG)`), with
        -- request_state_wire.rs l. 58–60 (`len > MAX_KID_LEN`, `MAX_KID_LEN = 255`, l. 21);
        -- checked second. Message text: request_state.rs l. 88
        (maxKidLen < (kid : Slice Std.U8).val.length ∧
          ∃ msg, e = .InvalidKeyring msg ∧ Defs.RequestState.StrIs msg
            Defs.RequestState.kidTooLongMsg) ⦄ := by
  -- Proof method: `step` uses the W03 theorem `check_kid_len_spec` (the W function is not
  -- unfolded) and `core.str.Str.len_spec`, the S09 model of `kid.len()` as the byte length.
  unfold validate_config_kid
  -- `step*` closes the `Ok` branch from W03; the `Empty` and `TooLong` branches remain.
  step*
  · rename_i hr hke
    subst hr hke
    refine Or.inl ⟨?_, KID_EMPTY_MSG, rfl, ?_⟩
    · rw [← i_post]; exact r_post
    · unfold KID_EMPTY_MSG Defs.RequestState.kidEmptyMsg
      exact Proofs.RequestState.strIs_toStr _ _
  · rename_i hr hke
    subst hr hke
    refine Or.inr ⟨?_, KID_TOO_LONG_MSG, rfl, ?_⟩
    · rw [← i_post]; exact r_post
    · unfold KID_TOO_LONG_MSG Defs.RequestState.kidTooLongMsg
      exact Proofs.RequestState.strIs_toStr _ _

end rmcp.model.request_state.RequestStateCodec
