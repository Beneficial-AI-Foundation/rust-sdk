/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire
import Defs.CodecState
import Proofs.External.Base64
import Proofs.External.String
import Proofs.External.Prim
import Proofs.External.Std
import Proofs.Model.RequestStateWire.ParseRs2
import Proofs.Model.RequestStateWire.CheckKidLen
import Proofs.Model.RequestStateWire.TranscriptV2
import Proofs.Model.RequestState.OpenAuthenticatedBody
import Proofs.Model.RequestState.Common

/-!
# Spec theorem for `RequestStateCodec::open_rs2_at` (E10)

Opens an `rs2` token: the result is exactly `Defs.CodecState.openRs2`, which fixes the error
order `MalformedFormat`, `InvalidKeyId` (encoded kid too long), `InvalidEncoding` (kid),
`InvalidKeyId` (decoded kid length, UTF-8), `UnknownKeyId`, `InvalidEncoding` (body, tag),
`IntegrityCheckFailed`, then E01 on the decoded body.

Source: "crates/rmcp/src/model/request_state.rs", lines 659–693 at local commit `46cfb02`
(the translation base; not yet a pinned fork commit).
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
      simp [hv]
    · rfl
  | some rp =>
    simp only at ho
    rw [hs] at ho
    unfold openRs2
    rw [ho]
    simp only [ne_eq, not_true_eq_false, if_false]
    have hkl : rp.kid.len.val = rp.kid.val.length := Slice.len_val _
    by_cases hk : Defs.CodecState.maxEncodedKidLen < rp.kid.val.length
    · have hk' : rp.kid.len > MAX_ENCODED_KID_LEN := by
        simp only [MAX_ENCODED_KID_LEN, request_state_wire.MAX_ENCODED_KID_LEN,
          Defs.CodecState.maxEncodedKidLen] at hk ⊢
        scalar_tac
      simp [hk', hk, resultBytes]
    · have hk' : ¬ rp.kid.len > MAX_ENCODED_KID_LEN := by
        simp only [MAX_ENCODED_KID_LEN, request_state_wire.MAX_ENCODED_KID_LEN,
          Defs.CodecState.maxEncodedKidLen] at hk ⊢
        scalar_tac
      simp only [hk', hk, if_false, model.request_state_wire.prim.b64_decode]
      split
      · rename_i hkd
        simp [hkd, core.option.Option.ok_or, CoreOpsTry.branch,
          CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from, resultBytes]
      · rename_i kid hkd
        simp only [hkd, core.option.Option.ok_or, CoreOpsTry.branch,
          bind_tc_ok]
        step as ⟨r1, hr1⟩
        have hvl : ∀ v : alloc.vec.Vec U8, v.val = kid → v.len.val = kid.length := by
          intro v hv; rw [alloc.vec.Vec.len_val, ← hv]
        rcases r1 with ⟨⟩ | ⟨⟨⟩ | ⟨⟩⟩
        · rw [hvl _ rfl] at hr1
          have hbad : ¬ (kid.length = 0 ∨ Defs.Wire.maxKidLen < kid.length) := by omega
          simp only [hbad, if_false, core.result.Result.is_err, bind_tc_ok, Bool.false_eq_true]
          unfold alloc.string.String.from_utf8
          split
          · rename_i ks hks
            simp only [hks, bind_tc_ok, core.result.Result.map_err_Ok]
            have hku : kid = ExtModel.utf8 ks :=
              (Proofs.External.Utf8.strOfBytes?_eq_some_iff _ _).1 hks
            cases hkeys : self.keys with
            | Single k1 => simp [resultBytes]
            | Ring keys sm fb =>
              simp only [std.collections.hash.map.HashMap.get_eq,
                Proofs.External.HashMap.find_string, bind_tc_ok, Defs.CodecState.lookupKey]
              cases hf : keys.entries.find? (fun e => decide (e.1 = ks)) with
              | none =>
                simp [resultBytes,
                  CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from]
              | some ent =>
                simp only [Option.map_some, bind_tc_ok]
                split
                · rename_i hbd
                  simp [hbd, resultBytes,
                    CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from]
                · rename_i body hbd
                  simp only [hbd, bind_tc_ok]
                  split
                  · rename_i htd
                    simp [htd, resultBytes,
                      CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      core.convert.FromSame.from]
                  · rename_i tag htd
                    simp only [htd, bind_tc_ok]
                    have hksz : ks.utf8ByteSize ≤ Usize.max := by
                      have : kid.length ≤ 255 := by simp only [Defs.Wire.maxKidLen] at hbad; omega
                      rw [← Proofs.External.Utf8.length_utf8, ← hku]; scalar_tac
                    step as ⟨s1, hs1⟩
                    step as ⟨tr, htr⟩
                    · rw [hs1, ← hku]; exact h_len _ _ _ _ _ ho hkd hbd
                    step as ⟨v, hv⟩
                    step as ⟨b1, hb1⟩
                    simp only [alloc.vec.Vec.deref, hv, htr, hs1, ← hku] at hb1
                    by_cases ht : Defs.CodecState.TagVerifies ent.2.inner.val
                        (transcriptV2 kid associated_data.val body) tag
                    · have hb : b1 = true := by
                        rw [hb1]; exact decide_eq_true ht
                      simp only [hb, if_true, ht]
                      step as ⟨res, hres⟩
                      unfold Defs.CodecState.openBody
                      rcases res with pl | e
                      · obtain ⟨h1, h2, h3⟩ := hres
                        have h1' : ¬ body.length < Defs.Wire.expiryLen := by
                          omega
                        simp [resultBytes, h1', h2, h3]
                      · rcases hres with ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
                        · simp [resultBytes, h1]
                        · have h1' : ¬ body.length < Defs.Wire.expiryLen := by omega
                          simp [resultBytes, h1', h2]
                    · have hb : b1 = false := by
                        rw [hb1]; exact decide_eq_false ht
                      simp [hb, ht, resultBytes]
          · rename_i hks
            simp [hks, resultBytes,
              CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from,
              CoreOpsFunctionFnOnceTupleFromUtf8ErrorRequestStateError.call_once]
        · rw [hvl _ rfl] at hr1
          simp [hr1, core.result.Result.is_err, resultBytes]
        · rw [hvl _ rfl] at hr1
          simp [hr1, core.result.Result.is_err, resultBytes]

end rmcp.model.request_state.RequestStateCodec
