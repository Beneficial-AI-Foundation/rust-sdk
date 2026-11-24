/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Proofs.Defs.Wire
import Proofs.Defs.CodecState
import Proofs.External.Base64
import Proofs.External.String
import Proofs.External.Prim
import Proofs.External.Std
import Proofs.Model.RequestStateWire.TranscriptV2
import Proofs.Model.RequestState.B64Len
import Proofs.Model.RequestState.Common

/-!
# Spec theorem for `RequestStateCodec::seal_rs2` (E08)

Builds the `rs2` token `"rs2." ++ b64 kid ++ "." ++ b64 body ++ "." ++ b64 tag`, where `tag` is
the HMAC SHA-256 of the W11 transcript of `kid`, `associated_data` and `body` under `key`.

Source: "crates/rmcp/src/model/request_state.rs", lines 585–605 in the patched copy
(patch 01 on origin/main 7caec76, D2 fallback 2026-11-23); line numbers refer to it.
-/

open Aeneas Aeneas.Std Result
open rmcp
open rmcp.model.request_state
open Defs.Wire (dot versionV2 transcriptV2 b64Len)

namespace rmcp.model.request_state.RequestStateCodec

open ExtModel Proofs.External.Utf8 Proofs.External.Base64

/-- The generated constant `VERSION_V2` (request_state.rs line 81, `"rs2"`) holds the bytes
`versionV2`. -/
theorem val_VERSION_V2 : model.request_state.VERSION_V2.val = versionV2 := by
  unfold model.request_state.VERSION_V2; rw [toStr_val]; decide +kernel

/-- The UTF-8 bytes of the literal `"rs2"` are `versionV2`. -/
theorem utf8_rs2 : utf8 "rs2" = versionV2 := by decide +kernel

/-- **Spec theorem for `rmcp::model::request_state::RequestStateCodec::seal_rs2`** (E08)

The `rs2` token `"rs2." ++ b64 kid ++ "." ++ b64 body ++ "." ++ b64 tag`, as UTF-8 bytes, where
`tag = hmacSha256 key (transcriptV2 kid associated_data body)` (W11); any kid is accepted.
Preconditions: the transcript fits in `Usize.max` bytes (`h_len`) and the capacity sum of
lines 590–596 is at most `ExtModel.maxStringBytes` (`h_cap`). The statement is that of the
draft spec file `formal/specs/Drafts/RequestState.lean`. -/
@[step]
theorem seal_rs2_spec (kid : Str) (key : Slice Std.U8) (associated_data : Slice Std.U8)
    (body : Slice Std.U8)
    (h_len : (transcriptV2 (kid : Slice Std.U8).val associated_data.val body.val).length ≤
      Usize.max)
    (h_cap : versionV2.length + 3 + b64Len (kid : Slice Std.U8).val.length +
      b64Len body.val.length + b64Len 32 ≤ ExtModel.maxStringBytes) :
    seal_rs2 kid key associated_data body ⦃ (result : String) =>
      -- lines 597–604: "rs2", '.', b64(kid), '.', b64(body), '.', b64(tag); tag from 586–589
      ExtModel.utf8 result =
        versionV2 ++ [dot] ++ ExtModel.b64 (kid : Slice Std.U8).val ++ [dot] ++
          ExtModel.b64 body.val ++ [dot] ++
          ExtModel.b64 (ExtModel.hmacSha256 key.val
            (transcriptV2 (kid : Slice Std.U8).val associated_data.val body.val)).val ⦄ := by
  have hM := maxStringBytes_le_usize_max
  have hv2 : versionV2.length = 3 := rfl
  have hb32 : b64Len 32 = 44 := rfl
  have hlk := length_b64_le_b64Len (kid : Slice Std.U8).val
  have hlb := length_b64_le_b64Len body.val
  have hdot : utf8 (String.ofList ['.']) = [dot] := by decide +kernel
  have hdl : '.'.utf8Size = 1 := rfl
  unfold seal_rs2
  step as ⟨s, hs⟩
  step as ⟨v, hv⟩
  step as ⟨tag, htag⟩
  step as ⟨i, hi⟩
  rw [val_VERSION_V2] at hi
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  step as ⟨i4, hi4⟩
  step as ⟨i6, hi6⟩
  step as ⟨i7, hi7⟩
  simp only [lift, bind_tc_ok]
  have hts : (tag.to_slice).val = tag.val := rfl
  have htl : tag.val.length = 32 := tag.property
  step as ⟨i9, hi9⟩
  step as ⟨i10, hi10⟩
  step as ⟨out, hout⟩
  step with alloc.string.String.push_str_spec out model.request_state.VERSION_V2 "rs2"
    (by rw [val_VERSION_V2, utf8_rs2])
    (by rw [hout, val_VERSION_V2]; simp only [String.utf8ByteSize_empty, zero_add]; omega)
    as ⟨out1, hout1, hout1'⟩
  have hl1 : out1.utf8ByteSize = 3 := by
    rw [← length_utf8, hout1', hout, val_VERSION_V2, utf8_empty]; rfl
  step with alloc.string.String.push_spec out1 '.' (by rw [hl1]; omega)
    as ⟨out2, hout2, hout2'⟩
  have hl2 : out2.utf8ByteSize = 4 := by
    rw [← length_utf8, hout2', hout1', hdot, hout, val_VERSION_V2, utf8_empty]; rfl
  step with model.request_state_wire.prim.b64_encode_into_spec s out2
    (by rw [hl2]; simp only [Slice.length]; rw [hs, ← length_b64]; omega) as ⟨out3, hout3⟩
  have hl3 : out3.utf8ByteSize = 4 + (b64 (kid : Slice Std.U8).val).length := by
    rw [← length_utf8, hout3, List.length_append, length_utf8, hl2, hs]
  step with alloc.string.String.push_spec out3 '.' (by rw [hl3]; omega)
    as ⟨out4, hout4, hout4'⟩
  have hl4 : out4.utf8ByteSize = 5 + (b64 (kid : Slice Std.U8).val).length := by
    rw [← length_utf8, hout4', List.length_append, length_utf8, hl3, hdot]
    simp only [List.length_cons, List.length_nil, zero_add]; omega
  step with model.request_state_wire.prim.b64_encode_into_spec body out4
    (by rw [hl4]; simp only [Slice.length]; rw [← length_b64]; omega) as ⟨out5, hout5⟩
  have hl5 : out5.utf8ByteSize =
      5 + (b64 (kid : Slice Std.U8).val).length + (b64 body.val).length := by
    rw [← length_utf8, hout5, List.length_append, length_utf8, hl4]
  step with alloc.string.String.push_spec out5 '.' (by rw [hl5]; omega)
    as ⟨out6, hout6, hout6'⟩
  have hl6 : out6.utf8ByteSize =
      6 + (b64 (kid : Slice Std.U8).val).length + (b64 body.val).length := by
    rw [← length_utf8, hout6', List.length_append, length_utf8, hl5, hdot]
    simp only [List.length_cons, List.length_nil, zero_add]; omega
  step with model.request_state_wire.prim.b64_encode_into_spec tag.to_slice out6
    (by rw [hl6]; simp only [Slice.length, hts, htl]; omega) as ⟨out7, hout7⟩
  have hv' : v.deref.val = transcriptV2 (kid : Slice Std.U8).val associated_data.val body.val := by
    rw [← hs]; exact hv
  rw [hout7, hout6', hout5, hout4', hout3, hout2', hout1', hout, val_VERSION_V2, utf8_empty, hdot,
    hts, htag, hv', hs]
  simp only [List.nil_append, List.append_assoc, List.cons_append]

end rmcp.model.request_state.RequestStateCodec
