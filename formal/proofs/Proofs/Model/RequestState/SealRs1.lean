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
import Proofs.Model.RequestStateWire.TranscriptV1
import Proofs.Model.RequestState.B64Len
import Proofs.Model.RequestState.Common

/-!
# Spec theorem for `RequestStateCodec::seal_rs1` (E07)

Builds the `rs1` token `"rs1." ++ b64 body ++ "." ++ b64 tag`, where `tag` is the HMAC SHA-256
of the W10 transcript of `associated_data` and `body` under `key`.

Source: "crates/rmcp/src/model/request_state.rs", lines 572–583 in the patched copy
(patch 01 on origin/main 7caec76, D2 fallback 2026-11-23); line numbers refer to it.
-/

open Aeneas Aeneas.Std Result
open rmcp
open rmcp.model.request_state
open Defs.Wire (dot versionV1 transcriptV1 b64Len)

namespace rmcp.model.request_state.RequestStateCodec

open ExtModel Proofs.External.Utf8 Proofs.External.Base64

/-- The generated constant `VERSION_V1` (request_state.rs line 78, `"rs1"`) holds the bytes
`versionV1`. -/
theorem val_VERSION_V1 : model.request_state.VERSION_V1.val = versionV1 := by
  unfold model.request_state.VERSION_V1; rw [toStr_val]; decide +kernel

/-- The UTF-8 bytes of the literal `"rs1"` are `versionV1`. -/
theorem utf8_rs1 : utf8 "rs1" = versionV1 := by decide +kernel

/-- **Spec theorem for `rmcp::model::request_state::RequestStateCodec::seal_rs1`** (E07)

The `rs1` token `"rs1." ++ b64 body ++ "." ++ b64 tag`, as UTF-8 bytes, where
`tag = hmacSha256 key (transcriptV1 associated_data body)` (W10). Preconditions: the transcript
fits in `Usize.max` bytes (`h_len`) and the capacity sum of lines 574–576 is at most
`ExtModel.maxStringBytes` (`h_cap`). The statement is that of the draft spec file
`formal/specs/Drafts/RequestState.lean`. -/
@[step]
theorem seal_rs1_spec (key : Slice Std.U8) (associated_data : Slice Std.U8)
    (body : Slice Std.U8)
    (h_len : (transcriptV1 associated_data.val body.val).length ≤ Usize.max)
    (h_cap : versionV1.length + 2 + b64Len body.val.length + b64Len 32 ≤
      ExtModel.maxStringBytes) :
    seal_rs1 key associated_data body ⦃ (result : String) =>
      -- lines 577–582: "rs1", '.', b64(body), '.', b64(tag); tag from line 573
      ExtModel.utf8 result =
        versionV1 ++ [dot] ++ ExtModel.b64 body.val ++ [dot] ++
          ExtModel.b64 (ExtModel.hmacSha256 key.val
            (transcriptV1 associated_data.val body.val)).val ⦄ := by
  have hM := maxStringBytes_le_usize_max
  have hv1 : versionV1.length = 3 := rfl
  have hb32 : b64Len 32 = 44 := rfl
  have hlb := length_b64_le_b64Len body.val
  unfold seal_rs1
  step as ⟨v, hv⟩
  step as ⟨tag, htag⟩
  step as ⟨i, hi⟩
  rw [val_VERSION_V1] at hi
  step as ⟨i1, hi1⟩
  step as ⟨i3, hi3⟩
  have hi3' : i3.val = b64Len body.val.length := by simpa using hi3
  have hv' : v.deref.val = transcriptV1 associated_data.val body.val := hv
  step as ⟨i4, hi4⟩
  simp only [lift, bind_tc_ok]
  have hts : (tag.to_slice).val = tag.val := rfl
  have htl : tag.val.length = 32 := tag.property
  step as ⟨i6, hi6⟩
  have hi6' : i6.val = 44 := by
    rw [hi6]; simp only [Slice.len_val, Slice.length, hts, htl]; rfl
  step as ⟨i7, hi7⟩
  step as ⟨out, hout⟩
  step with alloc.string.String.push_str_spec out model.request_state.VERSION_V1 "rs1"
    (by rw [val_VERSION_V1, utf8_rs1]) (by rw [hout, val_VERSION_V1]; simp; omega)
    as ⟨out1, hout1, hout1'⟩
  have hl1 : out1.utf8ByteSize = 3 := by
    rw [← length_utf8, hout1', hout, val_VERSION_V1, utf8_empty]; rfl
  step as ⟨out2, hout2, hout2'⟩
  · rw [hl1]; have : '.'.utf8Size = 1 := rfl; omega
  have hdot : utf8 (String.ofList ['.']) = [dot] := by decide +kernel
  have hl2 : out2.utf8ByteSize = 4 := by
    rw [← length_utf8, hout2', hout1', hdot, hout, val_VERSION_V1, utf8_empty]; rfl
  step as ⟨out3, hout3⟩
  · rw [hl2]; simp only [Slice.length]; rw [← length_b64]; omega
  have hl3 : out3.utf8ByteSize = 4 + (b64 body.val).length := by
    rw [← length_utf8, hout3, List.length_append, length_utf8, hl2]
  step as ⟨out4, hout4, hout4'⟩
  · rw [hl3]; have : '.'.utf8Size = 1 := rfl; omega
  have hl4 : out4.utf8ByteSize = 5 + (b64 body.val).length := by
    rw [← length_utf8, hout4', List.length_append, length_utf8, hl3, hdot]; simp; omega
  step as ⟨out5, hout5⟩
  rw [hout5, hout4', hout3, hout2', hout1', hout, val_VERSION_V1, utf8_empty, hdot, hts,
    htag, hv']
  simp

end rmcp.model.request_state.RequestStateCodec
