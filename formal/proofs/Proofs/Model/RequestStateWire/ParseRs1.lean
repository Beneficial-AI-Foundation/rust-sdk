/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire
import Proofs.Model.RequestStateWire.Common
import Proofs.Model.RequestStateWire.BytesEq
import Proofs.Model.RequestStateWire.ComponentCount

/-!
# Spec theorem for `parse_rs1` (W08)

Parses an `rs1` token: requires exactly three `.`-components (`component_count`, W06), finds the
two dots (`next_dot`, W05), compares the first component with `VERSION_V1` (`bytes_eq`, W04) and
returns the second and third components as subslices.

W04–W06 are used through `step`. With three components both dots exist, so neither `next_dot`
returns `s.len()`; `Proofs.RequestStateWire.components_drop_of_next_dot_post` gives the
components one dot at a time, and `components_eq_singleton_of_length_eq_one` the last one.

Source: "crates/rmcp/src/model/request_state_wire.rs", line 137 in the patched copy
(patch 01 on origin/main 7caec76, D2 fallback 2026-11-23); line numbers refer to it.
-/

open Aeneas Aeneas.Std Result

namespace rmcp.model.request_state_wire

open Defs.Wire Proofs.RequestStateWire

/-- **Spec theorem for `rmcp::model::request_state_wire::parse_rs1`** (W08)

`parse_rs1 s` is `Some {body, tag}` iff `splitOn '.' s = ["rs1", body, tag]`, and `None` iff
`s` does not split into `"rs1"` and two further components (plan Section 2.1, W08; plan
Section 3, "W06–W09 — splitting"; lines 136–150: component count `≠ 3` gives `None`
(138–140), first component `≠ "rs1"` gives `None` (143–145), otherwise the two remaining
components (146–149)). The returned slices are determined by their byte lists.

Lean-model domain: `h_count` is the hypothesis of W06, whose `component_count` is called first
(line 138); see `component_count_spec`. -/
@[step]
theorem parse_rs1_spec (s : Slice U8)
    (h_count : s.val.count dot < Usize.max) :
    parse_rs1 s ⦃ (result : Option Rs1Parts) =>
      match result with
      | some p => components s.val = [versionV1, p.body.val, p.tag.val]
      | none => ∀ body tag, components s.val ≠ [versionV1, body, tag] ⦄ := by
  unfold parse_rs1
  step as ⟨c, hc, _⟩
  split
  · rename_i hne
    rw [WP.spec_ok]
    intro body tag heq
    rw [heq] at hc
    simp only [bne_iff_ne, ne_eq] at hne
    apply hne
    scalar_tac
  · rename_i hne
    have hc3 : (components s.val).length = 3 := by
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
      rw [← hc, hne]; rfl
    have hsl : s.length ≤ Usize.max := s.property
    step as ⟨d1, hd1a, hd1b⟩
    rcases components_drop_of_next_dot_post s.val 0 d1.val hd1a hd1b with
      ⟨-, hc1⟩ | ⟨-, hd1, hc1⟩
    · rw [List.drop_zero] at hc1
      rw [hc1] at hc3
      simp only [List.length_cons, List.length_nil, zero_add, OfNat.one_ne_ofNat] at hc3
    rw [List.drop_zero] at hc1
    step as ⟨i1, hi1⟩
    step as ⟨d2, hd2a, hd2b⟩
    rcases components_drop_of_next_dot_post s.val i1.val d2.val hd2a hd2b with
      ⟨-, hc2⟩ | ⟨hd12, hd2, hc2⟩
    · rw [hi1] at hc2
      rw [hc1, hc2] at hc3
      simp only [List.slice_zero_j, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
        Nat.reduceEqDiff] at hc3
    rw [hi1] at hc2 hd12
    rw [hc2] at hc1
    rw [hc1] at hc3
    have hc3' := components_eq_singleton_of_length_eq_one _ (by
      simpa only [List.slice_zero_j, List.length_cons, Nat.reduceEqDiff] using hc3)
    rw [hc3'] at hc1
    step as ⟨s1, hs1, _⟩
    step as ⟨b, hb⟩
    rw [val_VERSION_V1] at hb
    split
    · rename_i h
      rw [h] at hb
      step as ⟨s2, hs2, _⟩
      step as ⟨i2, hi2⟩
      step as ⟨s3, hs3, _⟩
      rw [hc1, hs2, hs3, ← of_decide_eq_true hb.symm, ← hs1, hi1, hi2]
    · rename_i h
      rw [Bool.not_eq_true] at h
      rw [h] at hb
      rw [WP.spec_ok]
      intro body tag heq
      rw [hc1] at heq
      simp only [List.cons.injEq] at heq
      exact of_decide_eq_false hb.symm (hs1 ▸ heq.1)

end rmcp.model.request_state_wire
