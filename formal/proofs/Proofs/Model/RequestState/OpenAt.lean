/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire
import Defs.CodecState
import Proofs.Model.RequestStateWire.Common
import Proofs.Model.RequestStateWire.VersionOf
import Proofs.Model.RequestState.OpenRs1At
import Proofs.Model.RequestState.OpenRs2At

/-!
# Spec theorem for `RequestStateCodec::open_at` (E11)

Dispatches on the version of the token: the result is exactly `Defs.CodecState.openAt`, that
is `openRs1` for an `rs1` token, `openRs2` for an `rs2` token and `MalformedFormat` otherwise.
The callees are used through their spec theorems (W07, E09, E10). E11 has no `.`-count premise:
`count_dot_lt_of_head` derives the `h_count` of E09 and E10 from the first component.

Source: "crates/rmcp/src/model/request_state.rs", lines 559–570 at local commit `adce319`
(the translation base; not yet a pinned fork commit).
-/

open Aeneas Aeneas.Std Result
open rmcp
open rmcp.model.request_state
open Defs.Wire (dot versionV1 versionV2 components transcriptV1 transcriptV2)
open Defs.CodecState (CodecFallbacksKnown openAt resultBytes)

namespace rmcp.model.request_state.RequestStateCodec

/-- A byte list of at most `Usize.max` bytes whose first `.`-component contains a byte other
than `.` has fewer than `Usize.max` `.` bytes (the `h_count` premise of E09 and E10). -/
theorem count_dot_lt_of_head (l : List U8) (hl : l.length ≤ Usize.max) (v : List U8)
    (hv : (components l).head? = some v) (x : U8) (hx : x ∈ v) (hxd : x ≠ dot) :
    l.count dot < Usize.max := by
  obtain ⟨rest, hrest⟩ : ∃ rest, components l = v :: rest := by
    cases h : components l with
    | nil => rw [h] at hv; simp only [List.head?_nil, reduceCtorEq] at hv
    | cons a r =>
      rw [h] at hv; simp only [List.head?_cons, Option.some.injEq] at hv
      exact ⟨r, by rw [hv]⟩
  have hxl : x ∈ l := by
    have := List.intercalate_splitOn (xs := l) dot
    rw [show l.splitOn dot = components l from rfl, hrest] at this
    cases rest with
    | nil => rw [← this]; simpa only [List.intercalate_singleton] using hx
    | cons r rs =>
      rw [← this]
      simp only [List.intercalate_cons_cons, List.append_assoc, List.cons_append,
        List.nil_append, List.mem_append, hx, List.mem_cons, true_or]
  have hle : l.count dot ≤ l.length := List.count_le_length
  have hne : l.count dot ≠ l.length := by
    intro heq
    rw [List.count, List.countP_eq_length] at heq
    have := heq x hxl
    simp only [beq_iff_eq] at this
    exact hxd this
  omega

/-- **Spec theorem for `rmcp::model::request_state::RequestStateCodec::open_at`** (E11)

`resultBytes result = openAt …`: the result is exactly the expected result of
`Defs.CodecState.openAt`, which dispatches on the first `.`-component of the token. The
premises are those of E09 (`h_len1`, and `h_fallbacks` for an `rs1` token) and E10 (`h_len2`);
the `.`-count premise of E09 and E10 follows from `count_dot_lt_of_head`. The statement is that
of the draft spec file `formal/specs/Drafts/RequestState.lean`. -/
@[step]
theorem open_at_spec (self : RequestStateCodec) (sealed : Str) (associated_data : Slice Std.U8)
    (now_ms : Std.I64)
    (h_len1 : ∀ b t body, components (sealed : Slice Std.U8).val = [versionV1, b, t] →
      ExtModel.b64Decode b = some body →
      (transcriptV1 associated_data.val body).length ≤ Usize.max)
    (h_len2 : ∀ k b t kid body, components (sealed : Slice Std.U8).val = [versionV2, k, b, t] →
      ExtModel.b64Decode k = some kid → ExtModel.b64Decode b = some body →
      (transcriptV2 kid associated_data.val body).length ≤ Usize.max)
    (h_fallbacks : (components (sealed : Slice Std.U8).val).head? = some versionV1 →
      CodecFallbacksKnown self) :
    open_at self sealed associated_data now_ms ⦃ (result :
        core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      -- lines 565–568; `openAt` (Defs.CodecState) dispatches on `(components _).head?`
      resultBytes result = openAt self (sealed : Slice Std.U8).val associated_data.val
        now_ms.val ⦄ := by
  unfold open_at
  simp only [core.str.Str.as_bytes, bind_tc_ok]
  step as ⟨o, ho⟩
  rcases o with _ | ⟨_ | _⟩
  · simp only at ho
    simp only [resultBytes, openAt, ho.1, ↓reduceIte, ho.2, WP.spec_ok]
  · simp only at ho
    have hc := count_dot_lt_of_head (sealed : Slice Std.U8).val sealed.property versionV1 ho
      114#u8 (by decide) (by decide)
    apply WP.spec_mono
      (open_rs1_at_spec self sealed associated_data now_ms hc h_len1 (h_fallbacks ho))
    intro r hr
    simp only [hr, openAt, ho, ↓reduceIte]
  · simp only at ho
    have hv12 : versionV1 ≠ versionV2 := by decide
    have hc := count_dot_lt_of_head (sealed : Slice Std.U8).val sealed.property versionV2 ho
      114#u8 (by decide) (by decide)
    apply WP.spec_mono (open_rs2_at_spec self sealed associated_data now_ms hc h_len2)
    intro r hr
    simp only [hr, openAt, ho, Option.some.injEq, hv12.symm, ↓reduceIte]

end rmcp.model.request_state.RequestStateCodec
