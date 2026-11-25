/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Defs.Wire
public import Defs.CodecState
public import Proofs.External.Base64
public import Proofs.Model.RequestStateWire.Common
public import Proofs.Model.RequestState.Public

@[expose] public section

/-!
# Spec theorems for `open_json_with` (R14) and `open_json` (R13)

`open_json_with` opens the token with `open_with` (R08) and passes the payload to the opaque
`serde_json::from_slice` model; `open_json` is `open_json_with` with no associated data, whose
transcript premises hold for every token as for R07. Statements signed off by the spec owner on
2026-11-25.

Source: "crates/rmcp/src/model/request_state.rs", lines 509–531 in the patched copy (patches 01,
02 and 03 on origin/main `7caec76`).
-/

open Aeneas Aeneas.Std Result
open Defs.Wire (components versionV1 versionV2 transcriptV1 transcriptV2 minKeyLength maxKidLen
  expiryLen frameBytes domainV1 domainV2 b64Len dot Expired)
open Defs.CodecState (CodecValid CodecFallbacksKnown openAt resultBytes keyIds lookupKey
  sealModeKid)
open Defs.RequestState (StrIs kidEmptyMsg kidTooLongMsg)
open rmcp.model.request_state (SealOptions RequestStateCodec Keys SealMode RequestStateError)

namespace rmcp.model.request_state.RequestStateCodec

/-! ## Opening JSON (R13, R14) -/

/-- **R14. Spec theorem for `rmcp::model::request_state::RequestStateCodec::open_json_with`**

Opens `sealed` as `open_with` does (`self.open_with(sealed, associated_data)?`, patched line 526,
upstream 536): if `openAt self sealed associated_data t` (`t = ExtModel.nowMs`, the reading of
`open_with`) is an error, that error, unchanged; otherwise, for the opened payload `p`, the outcome
`ExtModel.serdeJsonFromSlice` of `serde_json::from_slice::<T>(&p)` (line 527) for the
`Deserialize` instance of `T`, with `Ok value ↦ Ok value` and `Err error ↦
Err(Deserialization(error))` (lines 528–529, patch 03 hunk 2; upstream
`.map_err(RequestStateError::Deserialization)`, line 537). JSON rule: the statement says only
that the result is that opaque outcome for the opened payload; it relates no two calls. Clock as
R08 (one reading, parametric; nothing about two calls).

Premises (T) `h_len1`/`h_len2` and (F) `h_fallbacks`, as R08. Inherited exceptions: (K), (H),
(V) as R08; (J) the stated exceptions of the `from_slice` model (a `Deserialize` impl that
panics, does not terminate, is non-deterministic or has side effects). Rust tests:
`seal_open_roundtrips_json` (patched lines 827–842), `serde_is_reached_only_after_integrity_
verification` (lines 1425–1439). -/
@[step]
theorem open_json_with_spec {T : Type} (serde_coredeDeserializeOwnedInst :
    serde_core.de.DeserializeOwned T) (self : RequestStateCodec) (sealed : Str)
    (associated_data : Slice Std.U8)
    (h_len1 : ∀ b t body, components (sealed : Slice Std.U8).val = [versionV1, b, t] →
      ExtModel.b64Decode b = some body →
      (transcriptV1 associated_data.val body).length ≤ Usize.max)
    (h_len2 : ∀ k b t kid body, components (sealed : Slice Std.U8).val = [versionV2, k, b, t] →
      ExtModel.b64Decode k = some kid → ExtModel.b64Decode b = some body →
      (transcriptV2 kid associated_data.val body).length ≤ Usize.max)
    (h_fallbacks : (components (sealed : Slice Std.U8).val).head? = some versionV1 →
      CodecFallbacksKnown self) :
    open_json_with serde_coredeDeserializeOwnedInst self sealed associated_data ⦃ (result :
        core.result.Result T RequestStateError) =>
      match openAt self (sealed : Slice Std.U8).val associated_data.val ExtModel.nowMs.val with
      | .error e => result = .Err e
      | .ok payload =>
        result =
          match ExtModel.serdeJsonFromSlice serde_coredeDeserializeOwnedInst.DeserializeInst
              payload with
          | .Ok value => .Ok value
          | .Err error => .Err (.Deserialization error) ⦄ := by
  unfold open_json_with
  step with open_with_spec self sealed associated_data h_len1 h_len2 h_fallbacks as ⟨r, hr⟩
  rcases r with v | e
  · simp only [Defs.CodecState.resultBytes] at hr
    rw [← hr]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, serde_json.de.from_slice,
      alloc.vec.Vec.deref, Slice.from_val]
    rcases ExtModel.serdeJsonFromSlice serde_coredeDeserializeOwnedInst.DeserializeInst v.val
      with x | x <;> simp only [WP.spec_ok]
  · simp only [Defs.CodecState.resultBytes] at hr
    rw [← hr]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]

/-- **R13. Spec theorem for `rmcp::model::request_state::RequestStateCodec::open_json`**

`self.open_json_with(sealed, &[])` (patched lines 509–511, upstream 519–521): as R14 with no
associated data, `openAt self sealed [] t` at the reading `t = ExtModel.nowMs`, then the opaque
JSON outcome for the opened payload. Clock and JSON rules as R14. Premise (F) only (the
transcript premises hold for every token with empty associated data, as for R07). Inherited
exceptions (K), (H), (J); (V) does not arise (as R07). -/
@[step]
theorem open_json_spec {T : Type} (serde_coredeDeserializeOwnedInst :
    serde_core.de.DeserializeOwned T) (self : RequestStateCodec) (sealed : Str)
    (h_fallbacks : (components (sealed : Slice Std.U8).val).head? = some versionV1 →
      CodecFallbacksKnown self) :
    open_json serde_coredeDeserializeOwnedInst self sealed ⦃ (result :
        core.result.Result T RequestStateError) =>
      match openAt self (sealed : Slice Std.U8).val [] ExtModel.nowMs.val with
      | .error e => result = .Err e
      | .ok payload =>
        result =
          match ExtModel.serdeJsonFromSlice serde_coredeDeserializeOwnedInst.DeserializeInst
              payload with
          | .Ok value => .Ok value
          | .Err error => .Err (.Deserialization error) ⦄ := by
  unfold open_json
  simp only [lift, bind_ok]
  have hU := Usize.cMax_bound_concrete.1
  have hs : (sealed : Slice Std.U8).val.length ≤ Usize.max := sealed.property
  have had : (Array.to_slice (Std.Array.empty Std.U8)).val = [] := rfl
  rw [← had]
  refine open_json_with_spec serde_coredeDeserializeOwnedInst self sealed _ ?_ ?_ h_fallbacks
  · intro b t body hc hb
    have h1 := Proofs.RequestStateWire.length_eq_sum_map_length_components
      (sealed : Slice Std.U8).val
    rw [hc] at h1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at h1
    have h2 := Proofs.External.Base64.four_mul_length_le_of_b64Decode b body hb
    rw [Proofs.RequestStateWire.length_transcriptV1, had, List.length_nil]
    omega
  · intro k b t kid body hc hk hb
    have h1 := Proofs.RequestStateWire.length_eq_sum_map_length_components
      (sealed : Slice Std.U8).val
    rw [hc] at h1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at h1
    have h2 := Proofs.External.Base64.four_mul_length_le_of_b64Decode b body hb
    have h3 := Proofs.External.Base64.four_mul_length_le_of_b64Decode k kid hk
    rw [Proofs.RequestStateWire.length_transcriptV2, had, List.length_nil]
    omega

end rmcp.model.request_state.RequestStateCodec
