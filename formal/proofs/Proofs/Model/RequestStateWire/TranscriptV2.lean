/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire
import Proofs.Model.RequestStateWire.Common

/-!
# Spec theorem for `transcript_v2` (W11)

Builds the `rs2` MAC transcript: `DOMAIN_V2`, the big-endian length of the key id, the key id,
the big-endian length of the associated data, the associated data, then the body, by six
`Vec::extend_from_slice` calls.

Same proof as `transcript_v1_spec` (W10) with two more appended slices.

Source: "crates/rmcp/src/model/request_state_wire.rs", line 193 at local commit `46cfb02`
(the translation base; not yet a pinned fork commit).
-/

open Aeneas Aeneas.Std Result

namespace rmcp.model.request_state_wire

open Defs.Wire Proofs.RequestStateWire

/-- **Spec theorem for `rmcp::model::request_state_wire::transcript_v2`** (W11)

`transcript_v2 kid associated_data body` is
`DOMAIN_V2 ++ be64(len kid) ++ kid ++ be64(len ad) ++ ad ++ body` (plan Section 2.1, W11;
lines 192–202). Both length prefixes are exact byte lengths (casts on lines 196 and 198; see
`transcript_v1_spec`).

Lean-model domain: as for `transcript_v1_spec`, `h_len` excludes the Aeneas failure case of
`extend_from_slice` (only this direction is proved).
`Proofs.RequestStateWire.length_transcriptV2` gives the length as
`42 + len(kid) + len(ad) + len(body)`. -/
@[step]
theorem transcript_v2_spec (kid : Slice U8) (associated_data : Slice U8) (body : Slice U8)
    (h_len : (transcriptV2 kid.val associated_data.val body.val).length ≤ Usize.max) :
    transcript_v2 kid associated_data body ⦃ (result : alloc.vec.Vec U8) =>
      result.val = transcriptV2 kid.val associated_data.val body.val ⦄ := by
  rw [length_transcriptV2] at h_len
  have hd : domainV2.length = 26 := rfl
  unfold transcript_v2
  have hk : (Array.to_slice (core.num.U64.to_be_bytes
      (UScalar.cast .U64 kid.len))).val = be64 kid.length := by
    rw [val_to_slice_to_be_bytes, val_cast_U64, Slice.len_val]
  have hs : (Array.to_slice (core.num.U64.to_be_bytes
      (UScalar.cast .U64 associated_data.len))).val = be64 associated_data.length := by
    rw [val_to_slice_to_be_bytes, val_cast_U64, Slice.len_val]
  step as ⟨t, ht⟩
  rw [List.nil_append, val_DOMAIN_V2] at ht
  simp only [lift, bind_tc_ok]
  have h1 : t.length + (Array.to_slice (core.num.U64.to_be_bytes
      (UScalar.cast .U64 kid.len))).length ≤ Usize.max := by
    simp only [alloc.vec.Vec.length, Slice.length, hd, length_be64, ht, hk]; omega
  step as ⟨t1, ht1⟩
  rw [hk, ht] at ht1
  have h2 : t1.length + kid.length ≤ Usize.max := by
    simp only [alloc.vec.Vec.length, Slice.length, List.length_append, hd, length_be64, ht1]; omega
  step as ⟨t2, ht2⟩
  rw [ht1] at ht2
  have h3 : t2.length + (Array.to_slice (core.num.U64.to_be_bytes
      (UScalar.cast .U64 associated_data.len))).length ≤ Usize.max := by
    simp only [alloc.vec.Vec.length, Slice.length, List.length_append, hd, length_be64, ht2, hs]
    omega
  step as ⟨t3, ht3⟩
  rw [hs, ht2] at ht3
  have h4 : t3.length + associated_data.length ≤ Usize.max := by
    simp only [alloc.vec.Vec.length, Slice.length, List.length_append, hd, length_be64, ht3]; omega
  step as ⟨t4, ht4⟩
  rw [ht3] at ht4
  have h5 : t4.length + body.length ≤ Usize.max := by
    simp only [alloc.vec.Vec.length, Slice.length, List.length_append, hd, length_be64, ht4]; omega
  step as ⟨r, hr⟩
  rw [hr, ht4, transcriptV2]

end rmcp.model.request_state_wire
