/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Defs.Wire
public import Proofs.Model.RequestStateWire.Common

@[expose] public section

/-!
# Spec theorem for `transcript_v1` (W10)

Builds the `rs1` MAC transcript: `DOMAIN_V1`, the 8 big-endian bytes of the length of the
associated data, the associated data, then the body, by four `Vec::extend_from_slice` calls.

Uses `Proofs.RequestStateWire.extend_from_slice_spec` through `step`; the length prefix is
`be64` of the exact length by `val_to_slice_to_be_bytes` and `val_cast_u64`.

Source: "crates/rmcp/src/model/request_state_wire.rs", line 183 in the patched copy
(patch 01 on origin/main 7caec76, D2 fallback 2026-11-23); line numbers refer to it.
-/

open Aeneas Aeneas.Std Result

namespace rmcp.model.request_state_wire

open Defs.Wire Proofs.RequestStateWire

/-- **Spec theorem for `rmcp::model::request_state_wire::transcript_v1`** (W10)

`transcript_v1 associated_data body` is `DOMAIN_V1 ++ be64(len ad) ++ ad ++ body` (plan
Section 2.1, W10; lines 182–190). The length prefix is the byte length of `associated_data`
as a natural number: the cast `usize → u64` (line 186, `UScalar.cast .U64` in the translation)
zero-extends and is exact whether `Usize` has 32 or 64 bits in the Aeneas model, so no
target-width hypothesis is needed (plan Section 3, "W10/W11 — transcripts").

Lean-model domain (plan Section 3, "Lean-model domains"): each `extend_from_slice` fails in the
Aeneas model when the vector would exceed `Usize.max` elements. `h_len` excludes the Aeneas
failure case of `extend_from_slice`: under it no call fails (only this direction is proved; the
theorem says nothing about longer inputs). It holds whenever Rust can allocate the result, since
a `Vec<u8>` holds at most `isize::MAX` bytes (allocation failure is an explicit assumption, plan
Section 3). `Proofs.RequestStateWire.length_transcriptV1` gives the length as
`34 + len(ad) + len(body)`. -/
@[step]
theorem transcript_v1_spec (associated_data : Slice U8) (body : Slice U8)
    (h_len : (transcriptV1 associated_data.val body.val).length ≤ Usize.max) :
    transcript_v1 associated_data body ⦃ (result : alloc.vec.Vec U8) =>
      result.val = transcriptV1 associated_data.val body.val ⦄ := by
  rw [length_transcriptV1] at h_len
  have hd : domainV1.length = 26 := rfl
  unfold transcript_v1
  have hs : (Array.to_slice (core.num.U64.to_be_bytes
      (UScalar.cast .U64 associated_data.len))).val = be64 associated_data.length := by
    rw [val_to_slice_to_be_bytes, val_cast_u64, Slice.len_val]
  step as ⟨t, ht⟩
  rw [alloc.vec.Vec.from_val, List.nil_append, val_DOMAIN_V1] at ht
  simp only [lift]
  have h1 : t.length + (Array.to_slice (core.num.U64.to_be_bytes
      (UScalar.cast .U64 associated_data.len))).length ≤ Usize.max := by
    simp only [alloc.vec.Vec.length, Slice.length, ht, hs, hd, length_be64]; omega
  step as ⟨t1, ht1⟩
  rw [hs, ht] at ht1
  have h2 : t1.length + associated_data.length ≤ Usize.max := by
    simp only [alloc.vec.Vec.length, Slice.length, ht1, List.length_append, hd, length_be64]
    omega
  step as ⟨t2, ht2⟩
  have h3 : t2.length + body.length ≤ Usize.max := by
    simp only [alloc.vec.Vec.length, Slice.length, ht2, ht1, List.length_append, hd, length_be64]
    omega
  step as ⟨r, hr⟩
  rw [hr, ht2, ht1, transcriptV1]

end rmcp.model.request_state_wire
