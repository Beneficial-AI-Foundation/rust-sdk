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
public import Proofs.External.String
public import Proofs.External.Prim
public import Proofs.External.Std
public import Proofs.Model.RequestStateWire.ParseRs2
public import Proofs.Model.RequestStateWire.CheckKidLen
public import Proofs.Model.RequestStateWire.TranscriptV2
public import Proofs.Model.RequestState.OpenAuthenticatedBody
public import Proofs.Model.RequestState.Common

@[expose] public section

/-!
# Spec theorem for `RequestStateCodec::open_rs2_at` (E10)

Opens an `rs2` token: the result is exactly `Defs.CodecState.openRs2`, which fixes the error
order `MalformedFormat`, `InvalidKeyId` (encoded kid too long), `InvalidEncoding` (kid),
`InvalidKeyId` (decoded kid length, UTF-8), `UnknownKeyId`, `InvalidEncoding` (body, tag),
`IntegrityCheckFailed`, then E01 on the decoded body.

Source: "crates/rmcp/src/model/request_state.rs", lines 659–693 in the patched copy
(patch 01 on origin/main 7caec76, D2 fallback 2026-11-23); line numbers refer to it.
-/

open Aeneas Aeneas.Std Result
open rmcp
open rmcp.model.request_state
open Defs.Wire (dot versionV2 components transcriptV2)
open Defs.CodecState (openRs2 resultBytes)

namespace rmcp.model.request_state.RequestStateCodec

open core.result.Result.Insts open_rs2_at.closure.Insts

/-- **Spec theorem for `rmcp::model::request_state::RequestStateCodec::open_rs2_at`** (E10)

`resultBytes result = openRs2 …`: the result is exactly the expected result of
`Defs.CodecState.openRs2`. Preconditions: fewer than `Usize.max` `.` bytes in the token
(`h_count`, W09 domain) and, for a token whose kid and body decode, a W11 transcript of at most
`Usize.max` bytes (`h_len`). No codec-state premise. The statement is that of the draft spec
file `formal/specs/Drafts/RequestState.lean`. -/
@[step]
theorem open_rs2_at_spec (self : RequestStateCodec) (sealed : Str)
    (associated_data : Slice Std.U8) (now_ms : Std.I64)
    (h_count : (sealed : Slice Std.U8).val.count dot < Usize.max)
    (h_len : ∀ k b t kid body, components (sealed : Slice Std.U8).val = [versionV2, k, b, t] →
      ExtModel.b64Decode k = some kid → ExtModel.b64Decode b = some body →
      (transcriptV2 kid associated_data.val body).length ≤ Usize.max) :
    open_rs2_at self sealed associated_data now_ms ⦃ (result :
        core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      -- lines 665–692, in the order of plan Section 3 (see `Defs.CodecState.openRs2`)
      resultBytes result = openRs2 self (sealed : Slice Std.U8).val associated_data.val
        now_ms.val ⦄ := by
  unfold open_rs2_at
  step as ⟨s, hs⟩
  step as ⟨o, ho⟩
  cases o with
  | none =>
    simp only at ho
    simp only [WP.spec_ok, resultBytes]
    unfold openRs2
    split
    · rename_i v k b t hc
      have hv : v ≠ versionV2 := by
        rintro rfl; exact ho k b t (hs ▸ hc)
      simp only [ne_eq, hv, not_false_eq_true, ↓reduceIte]
    · rfl
  | some rp =>
    simp only at ho
    rw [hs] at ho
    unfold openRs2
    rw [ho]
    simp only [ne_eq, not_true_eq_false, ite_false]
    by_cases hk : Defs.CodecState.maxEncodedKidLen < rp.kid.val.length
    · have hk' : rp.kid.len > MAX_ENCODED_KID_LEN := by
        simp only [MAX_ENCODED_KID_LEN, request_state_wire.MAX_ENCODED_KID_LEN,
          Defs.CodecState.maxEncodedKidLen] at hk ⊢
        scalar_tac
      simp only [gt_iff_lt, hk', ↓reduceIte, resultBytes, hk, WP.spec_ok]
    · have hk' : ¬ rp.kid.len > MAX_ENCODED_KID_LEN := by
        simp only [MAX_ENCODED_KID_LEN, request_state_wire.MAX_ENCODED_KID_LEN,
          Defs.CodecState.maxEncodedKidLen] at hk ⊢
        scalar_tac
      simp only [hk', hk, ite_false]
      apply WP.spec_bind (model.request_state_wire.prim.b64_decode_spec rp.kid)
      intro o1 hkd
      cases o1 with
      | none =>
        simp only [Option.map_none] at hkd
        simp only [core.option.Option.ok_or_eq, CoreOpsTry.branch,
          CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
          bind_ok, bind_tc_ok, resultBytes, ← hkd, WP.spec_ok]
      | some kv =>
        simp only [Option.map_some] at hkd
        simp only [core.option.Option.ok_or_eq, CoreOpsTry.branch, ← hkd]
        step as ⟨r1, hr1⟩
        rw [alloc.vec.Vec.len_val] at hr1
        simp only [alloc.vec.Vec.length] at hr1
        rcases r1 with ⟨⟩ | ⟨⟨⟩ | ⟨⟩⟩
        · have hbad : ¬ (kv.val.length = 0 ∨ Defs.Wire.maxKidLen < kv.val.length) := by omega
          simp only [hbad, ite_false, core.result.Result.is_err_eq, bind_ok]
          apply WP.spec_bind (alloc.string.String.from_utf8_spec _)
          rintro (ks | e) hku
          · have hks : ExtModel.strOfBytes? kv.val = some ks :=
              (Proofs.External.Utf8.strOfBytes?_eq_some_iff _ _).2 hku
            simp only [hks, bind_ok, core.result.Result.map_err_ok]
            cases hkeys : self.keys with
            | Single k1 => simp only [resultBytes, WP.spec_ok]
            | Ring keys sm fb =>
              apply WP.spec_bind (std.collections.hash.map.HashMap.get_string_spec keys ks)
              intro o hget
              simp only [Defs.CodecState.lookupKey]
              cases o with
              | none =>
                have hf := Option.map_eq_none_iff.1 hget.symm
                simp only [hf, Option.map_none,
                  CoreOpsTry_traitFromResidualResult.from_residual,
                  core.convert.FromSame.from, bind_ok, bind_tc_ok, resultBytes, WP.spec_ok]
              | some key =>
                obtain ⟨ent, hf, rfl⟩ := Option.map_eq_some_iff.1 hget.symm
                simp only [hf, Option.map_some, bind_ok]
                apply WP.spec_bind (model.request_state_wire.prim.b64_decode_spec rp.body)
                intro o2 hbd
                cases o2 with
                | none =>
                  simp only [Option.map_none] at hbd
                  simp only [CoreOpsTry_traitFromResidualResult.from_residual,
                    core.convert.FromSame.from, bind_ok, bind_tc_ok, resultBytes, ← hbd,
                    WP.spec_ok]
                | some bv =>
                  simp only [Option.map_some] at hbd
                  simp only [bind_ok]
                  apply WP.spec_bind (model.request_state_wire.prim.b64_decode_spec rp.tag)
                  intro o3 htd
                  cases o3 with
                  | none =>
                    simp only [Option.map_none] at htd
                    simp only [CoreOpsTry_traitFromResidualResult.from_residual,
                      core.convert.FromSame.from, bind_ok, bind_tc_ok, resultBytes, ← hbd,
                      ← htd, WP.spec_ok]
                  | some tv =>
                    simp only [Option.map_some] at htd
                    simp only [bind_ok]
                    rw [← hbd, ← htd]
                    have hksz : ks.utf8ByteSize ≤ Usize.max := by
                      have : kv.val.length ≤ 255 := by
                        simp only [Defs.Wire.maxKidLen] at hbad; omega
                      rw [← Proofs.External.Utf8.length_utf8, ← hku]; scalar_tac
                    step as ⟨s1, hs1⟩
                    step as ⟨tr, htr⟩
                    · rw [hs1, ← hku, alloc.vec.Vec.deref, Slice.from_val]
                      exact h_len _ _ _ _ _ ho hkd.symm hbd.symm
                    step as ⟨v, hv⟩
                    step as ⟨b1, hb1⟩
                    simp only [alloc.vec.Vec.deref, Slice.from_val, hv, htr, hs1, ← hku] at hb1
                    by_cases ht : Defs.CodecState.TagVerifies ent.2.inner.val
                        (transcriptV2 kv.val associated_data.val bv.val) tv.val
                    · have hb : b1 = true := by
                        rw [hb1]; exact decide_eq_true ht
                      simp only [hb, ite_true, ht]
                      exact open_authenticated_body_openBody _ now_ms
                    · have hb : b1 = false := by
                        rw [hb1]; exact decide_eq_false ht
                      simp only [hb, Bool.false_eq_true, ↓reduceIte, resultBytes, ht, WP.spec_ok]
          · have hks : ExtModel.strOfBytes? kv.val = none :=
              (Proofs.External.Utf8.strOfBytes?_eq_none_iff _).2 hku.1
            simp only [CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_ok, bind_tc_ok, core.result.Result.map_err_err,
              CoreOpsFunctionFnOnceTupleFromUtf8ErrorRequestStateError.call_once, resultBytes, hks,
              WP.spec_ok]
        · simp only [core.result.Result.is_err_eq, ↓reduceIte, resultBytes, hr1,
            not_lt_zero, or_false, bind_ok, WP.spec_ok]
        · simp only [core.result.Result.is_err_eq, ↓reduceIte, resultBytes,
            List.length_eq_zero_iff, hr1, or_true, bind_ok, WP.spec_ok]

end rmcp.model.request_state.RequestStateCodec
