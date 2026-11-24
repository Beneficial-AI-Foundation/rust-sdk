/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire
import Proofs.Model.RequestStateWire.NextDot

/-!
# Shared lemmas for the `request_state_wire` proofs

Lemmas used by more than one proof file of `Proofs/Model/RequestStateWire/` (and planned for the
S07 and S10 proofs): facts about the `Defs.Wire` definitions (component count, frame length,
big-endian round trip, expiry of a frame), counting `.` bytes in a prefix, a step lemma for
`Vec::extend_from_slice` on bytes, the bytes of `u64::to_be_bytes` as `Defs.Wire.be64`, and a
bound on the result of `next_dot` (from W05). Nothing here is a statement of the spec; all
lemmas are in the namespace `Proofs.RequestStateWire`.

Added for S10 (W07–W11): splitting on `.` at the indices returned by `next_dot`, the bytes of
the constants `VERSION_V1`, `VERSION_V2`, `DOMAIN_V1`, `DOMAIN_V2`, the exact cast
`usize as u64`, the lengths of the transcripts and a bound on the number of `.` bytes (for
callers that must discharge the `h_len` and `h_count` premises of W06 and W08–W11).

Naming: the `…_of_next_dot_post` lemmas name their premise after the postcondition of
`next_dot_spec`, as the S06 lemma `le_length_of_next_dot_post` does.
-/

open Aeneas Aeneas.Std Result

namespace Proofs.RequestStateWire

open Defs.Wire

/-! ## Facts about the `Defs.Wire` definitions -/

/-- `List.splitOnP` returns one more piece than the number of separators. -/
theorem length_splitOnP {α : Type} (p : α → Bool) (l : List α) :
    (l.splitOnP p).length = l.countP p + 1 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.splitOnP_cons_eq_if_modifyHead, List.countP_cons]
    split <;> simp_all

/-- The number of `.`-components is one more than the number of `.` bytes. -/
theorem length_components (s : List U8) : (components s).length = s.count dot + 1 := by
  rw [components, List.splitOn, length_splitOnP, List.count]

/-- A frame is 8 bytes longer than its payload. -/
theorem length_frameBytes (e : Int) (p : List U8) : (frameBytes e p).length = 8 + p.length := by
  simp [frameBytes, be64OfInt, be64]

/-- Reading back the 8 big-endian bytes of `n` gives `n mod 2 ^ 64`. -/
theorem beNat_be64 (n : Nat) : beNat (be64 n) = n % 2 ^ 64 := by
  simp only [beNat, be64, byteOf, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  simp only [UScalar.val, BitVec.toNat_ofNat]
  simp only [UScalarTy.U8_numBits_eq]
  omega

/-- The expiry read from a frame is the expiry it was built with, for any value in the `i64`
range. -/
theorem bodyExpiry_frameBytes (e : Int) (p : List U8) (h1 : -2 ^ 63 ≤ e) (h2 : e < 2 ^ 63) :
    bodyExpiry (frameBytes e p) = e := by
  have hl : (be64OfInt e).length = 8 := by simp [be64OfInt, be64]
  rw [bodyExpiry, frameBytes, expiryLen, List.take_append_of_le_length (by omega),
    List.take_of_length_le (by omega), be64OfInt, beNat_be64, toInt64]
  split_ifs <;> omega

/-- Counting `.` bytes in a prefix one byte longer. -/
theorem count_take_add_one (s : List U8) (i : Nat) (h : i < s.length) :
    (s.take (i + 1)).count dot = (s.take i).count dot + if s[i] = dot then 1 else 0 := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.count_append,
    List.count_singleton]
  by_cases hd : s[i] = dot
  · simp [hd]
  · simp [hd]

/-! ## Translated library functions -/

/-- `Vec::extend_from_slice` on bytes appends the slice, provided the result fits in
`Usize.max` elements. -/
@[step]
theorem extend_from_slice_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ (r : alloc.vec.Vec U8) =>
      r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  rw [dif_pos h]
  obtain ⟨s', hs', heq⟩ := WP.spec_imp_exists
    (Slice.clone_spec (clone := core.clone.CloneU8.clone) (s := s) (fun _ _ => rfl))
  subst heq
  split
  · simp_all
  · simp_all
  · simp_all

/-- The big-endian bytes of a 64-bit bit vector: byte `i` is `v / 256 ^ (7 - i)` mod 256. -/
theorem toBEBytes_eq (v : BitVec 64) :
    v.toBEBytes = (List.range 8).map fun i => BitVec.ofNat 8 (v.toNat / 256 ^ (7 - i)) := by
  rw [BitVec.toBEBytes]
  iterate 9 (rw [BitVec.toLEBytes]; simp only [gt_iff_lt, Nat.reduceSub, Nat.lt_irrefl,
    Nat.ofNat_pos, if_true, if_false])
  simp only [List.reverse_cons, List.reverse_nil, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append]
  have hv : v.toNat < 2 ^ 64 := v.isLt
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    omega

/-- The bytes of `u64::to_be_bytes x` in the form given by the Aeneas step lemma
`core.num.U64.to_be_bytes.step_spec` (`x.bv.toBEBytes.map UScalar.mk`) are `be64 x.val`. -/
theorem map_mk_toBEBytes (x : U64) :
    x.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8) = be64 x.val := by
  rw [toBEBytes_eq, be64, List.map_map]
  rfl

/-- The bytes of `u64::to_be_bytes x` are `be64 x.val`. -/
theorem val_to_be_bytes (x : U64) : (core.num.U64.to_be_bytes x).val = be64 x.val :=
  map_mk_toBEBytes x

/-- The slice `(x.to_be_bytes())[..]` passed to `extend_from_slice` in `frame`, `transcript_v1`
and `transcript_v2` (`Array.to_slice` in `Rmcp.Funs`) holds the bytes `be64 x.val`. -/
theorem val_to_slice_to_be_bytes (x : U64) :
    (Array.to_slice (core.num.U64.to_be_bytes x)).val = be64 x.val := by
  rw [Array.val_to_slice, val_to_be_bytes]

/-! ## Corollaries of the spec theorems -/

/-- A result of `next_dot` that satisfies the second conjunct of the postcondition of
`next_dot_spec` (W05) is at most `s.len()`. -/
theorem le_length_of_next_dot_post (s : Slice U8) (start r : Usize)
    (h : r.val = s.length ∨ (start.val ≤ r.val ∧ s.val[r.val]? = some dot)) :
    r.val ≤ s.length := by
  rcases h with h | ⟨-, h⟩
  · exact h.le
  · exact (List.getElem?_eq_some_iff.mp h).1.le

/-- `next_dot s start` succeeds with a result at most `s.len()` (corollary of `next_dot_spec`,
W05). -/
theorem next_dot_le_length (s : Slice U8) (start : Usize) :
    rmcp.model.request_state_wire.next_dot s start ⦃ (result : Usize) =>
      result.val ≤ s.length ⦄ :=
  WP.spec_mono (rmcp.model.request_state_wire.next_dot_spec s start)
    fun r hr => le_length_of_next_dot_post s start r hr.2

/-! ## Splitting on `.` and the results of `next_dot` (for S10: W07–W09) -/

/-- A byte string without `.` is its own single component. -/
theorem components_eq_singleton (l : List U8) (h : ∀ x ∈ l, x ≠ dot) : components l = [l] := by
  rw [components, List.splitOn_eq_splitOnP]
  exact List.splitOnP_eq_singleton fun x hx => by
    simpa only [beq_eq_false_iff_ne, ne_eq, UScalar.neq_to_neq_val] using h x hx

/-- Splitting at the first `.`: the part before it is the first component. -/
theorem components_append_dot (a b : List U8) (h : ∀ x ∈ a, x ≠ dot) :
    components (a ++ dot :: b) = a :: components b := by
  rw [components, List.splitOn_eq_splitOnP]
  exact List.splitOnP_append_cons_of_forall_mem (fun x hx => by
    simpa only [beq_eq_false_iff_ne, ne_eq, UScalar.neq_to_neq_val] using h x hx) dot
    (by simp only [BEq.rfl]) b

/-- A byte string with exactly one component is that component. -/
theorem components_eq_singleton_of_length_eq_one (l : List U8) (h : (components l).length = 1) :
    components l = [l] := by
  rw [length_components] at h
  apply components_eq_singleton
  intro x hx hxd
  subst hxd
  have := List.count_pos_iff.mpr hx
  omega

/-- The components of `s.drop start`, given an index `d` that satisfies the postcondition of
`next_dot_spec` (W05): either `d = s.len()` and `s.drop start` has no `.`, or `d` is a `.` and
the first component is `s[start..d]` (`List.slice start d s`, the form of the Aeneas range-index
step lemmas), followed by the components of `s.drop (d + 1)`. No bound on `start` is needed:
for `start > s.len()` only the first case can hold, and `s.drop start = []` has one component. -/
theorem components_drop_of_next_dot_post (s : List U8) (start d : Nat)
    (h1 : ∀ j, start ≤ j → j < d → s[j]? ≠ some dot)
    (h2 : d = s.length ∨ (start ≤ d ∧ s[d]? = some dot)) :
    (d = s.length ∧ components (s.drop start) = [s.drop start]) ∨
    (start ≤ d ∧ d < s.length ∧
      components (s.drop start) = s.slice start d :: components (s.drop (d + 1))) := by
  rcases h2 with h2 | ⟨hsd, h2⟩
  · left
    refine ⟨h2, components_eq_singleton _ ?_⟩
    intro x hx hxd
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_drop] at hxd
    rw [List.length_drop] at hk
    exact h1 (start + k) (by omega) (by omega) (by rw [List.getElem?_eq_getElem (by omega), hxd])
  · right
    have hd : d < s.length := (List.getElem?_eq_some_iff.mp h2).1
    have hsd' : s[d] = dot := (List.getElem?_eq_some_iff.mp h2).2
    refine ⟨hsd, hd, ?_⟩
    have hsplit : s.drop start = s.slice start d ++ dot :: s.drop (d + 1) := by
      rw [List.slice, ← hsd', ← List.drop_eq_getElem_cons hd]
      conv_lhs => rw [← List.take_append_drop (d - start) (s.drop start)]
      rw [List.drop_drop, Nat.add_sub_cancel' hsd]
    rw [hsplit, components_append_dot]
    intro x hx hxd
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    simp only [List.slice, List.getElem_take, List.getElem_drop] at hxd
    simp only [List.slice, List.length_take, List.length_drop] at hk
    exact h1 (start + k) (by omega) (by omega) (by rw [List.getElem?_eq_getElem (by omega), hxd])

/-! ## Constants and casts of the translation (for S10) -/

/-- The bytes of `VERSION_V1` are `Defs.Wire.versionV1`. -/
theorem val_VERSION_V1 : rmcp.model.request_state_wire.VERSION_V1.val = versionV1 := by
  unfold rmcp.model.request_state_wire.VERSION_V1
  rfl

/-- The bytes of `VERSION_V2` are `Defs.Wire.versionV2`. -/
theorem val_VERSION_V2 : rmcp.model.request_state_wire.VERSION_V2.val = versionV2 := by
  unfold rmcp.model.request_state_wire.VERSION_V2
  rfl

/-- The bytes of `DOMAIN_V1` are `Defs.Wire.domainV1`. -/
theorem val_DOMAIN_V1 : rmcp.model.request_state_wire.DOMAIN_V1.val = domainV1 := by
  unfold rmcp.model.request_state_wire.DOMAIN_V1
  rfl

/-- The bytes of `DOMAIN_V2` are `Defs.Wire.domainV2`. -/
theorem val_DOMAIN_V2 : rmcp.model.request_state_wire.DOMAIN_V2.val = domainV2 := by
  unfold rmcp.model.request_state_wire.DOMAIN_V2
  rfl

/-- `be64 n` has 8 bytes. -/
theorem length_be64 (n : Nat) : (be64 n).length = 8 := by
  simp only [be64, List.length_map, List.length_range]

/-- The cast `usize as u64` is exact: `Usize` has 32 or 64 bits. -/
theorem val_cast_u64 (x : Usize) : (UScalar.cast .U64 x).val = x.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  simp only [UScalarTy.Usize_numBits_eq, UScalarTy.U64_numBits_eq]
  rcases System.Platform.numBits_eq with h | h <;> omega

/-! ## Transcript lengths and the number of `.` bytes (for S10 and its callers) -/

/-- An `rs1` transcript has `34 + len(ad) + len(body)` bytes: 26 bytes of `DOMAIN_V1` and 8 of
the length prefix. -/
theorem length_transcriptV1 (ad body : List U8) :
    (transcriptV1 ad body).length = 34 + ad.length + body.length := by
  have hd : domainV1.length = 26 := rfl
  simp only [transcriptV1, List.length_append, length_be64, hd]

/-- An `rs2` transcript has `42 + len(kid) + len(ad) + len(body)` bytes: 26 bytes of
`DOMAIN_V2` and two 8-byte length prefixes. -/
theorem length_transcriptV2 (kid ad body : List U8) :
    (transcriptV2 kid ad body).length = 42 + kid.length + ad.length + body.length := by
  have hd : domainV2.length = 26 := rfl
  simp only [transcriptV2, List.length_append, length_be64, hd]
  omega

/-- A byte string shorter than `Usize.max` has fewer than `Usize.max` `.` bytes: a sufficient
condition for the `h_count` premise of W06, W08 and W09. -/
theorem count_dot_lt_of_length_lt (s : List U8) (h : s.length < Usize.max) :
    s.count dot < Usize.max :=
  lt_of_le_of_lt (List.count_le_length) h

end Proofs.RequestStateWire
