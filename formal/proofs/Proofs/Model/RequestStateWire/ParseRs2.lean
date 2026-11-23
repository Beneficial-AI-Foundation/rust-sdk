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
# Spec theorem for `parse_rs2` (W09)

Parses an `rs2` token: requires exactly four `.`-components (`component_count`, W06), finds the
three dots (`next_dot`, W05), compares the first component with `VERSION_V2` (`bytes_eq`, W04)
and returns the other three components as subslices.

Same proof as `parse_rs1_spec` (W08) with one more dot.

Source: "crates/rmcp/src/model/request_state_wire.rs", line 165 at local commit `adce319`
(the translation base; not yet a pinned fork commit).
-/

open Aeneas Aeneas.Std Result

namespace rmcp.model.request_state_wire

open Defs.Wire Proofs.RequestStateWire

/-- **Spec theorem for `rmcp::model::request_state_wire::parse_rs2`** (W09)

`parse_rs2 s` is `Some {kid, body, tag}` iff `splitOn '.' s = ["rs2", kid, body, tag]`, and
`None` otherwise (plan Section 2.1, W09; plan Section 3, "W06–W09 — splitting"; lines 164–180:
component count `≠ 4` gives `None` (166–168), first component `≠ "rs2"` gives `None`
(172–174), otherwise the three remaining components (175–179)).

Lean-model domain: `h_count` is the hypothesis of W06 (line 166); see
`component_count_spec`. -/
@[step]
theorem parse_rs2_spec (s : Slice U8)
    (h_count : s.val.count dot < Usize.max) :
    parse_rs2 s ⦃ (result : Option Rs2Parts) =>
      match result with
      | some p => components s.val = [versionV2, p.kid.val, p.body.val, p.tag.val]
      | none => ∀ kid body tag, components s.val ≠ [versionV2, kid, body, tag] ⦄ := by
  unfold parse_rs2
  step as ⟨c, hc, _⟩
  split
  · rename_i hne
    rw [WP.spec_ok]
    intro kid body tag heq
    rw [heq] at hc
    simp only [bne_iff_ne, ne_eq] at hne
    apply hne
    scalar_tac
  · rename_i hne
    have hc4 : (components s.val).length = 4 := by
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
      rw [← hc, hne]; rfl
    have hsl : s.length ≤ Usize.max := s.property
    step as ⟨d1, hd1a, hd1b⟩
    rcases components_drop_of_next_dot_post s.val 0 d1.val hd1a hd1b with
      ⟨-, hc1⟩ | ⟨-, hd1, hc1⟩
    · rw [List.drop_zero] at hc1
      rw [hc1] at hc4
      simp only [List.length_cons, List.length_nil, zero_add, OfNat.one_ne_ofNat] at hc4
    rw [List.drop_zero] at hc1
    step as ⟨i1, hi1⟩
    step as ⟨d2, hd2a, hd2b⟩
    rcases components_drop_of_next_dot_post s.val i1.val d2.val hd2a hd2b with
      ⟨-, hc2⟩ | ⟨hd12, hd2, hc2⟩
    · rw [hi1] at hc2
      rw [hc1, hc2] at hc4
      simp only [List.slice_zero_j, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
        Nat.reduceEqDiff] at hc4
    rw [hi1] at hc2 hd12
    rw [hc2] at hc1
    step as ⟨i2, hi2⟩
    step as ⟨d3, hd3a, hd3b⟩
    rcases components_drop_of_next_dot_post s.val i2.val d3.val hd3a hd3b with
      ⟨-, hc3⟩ | ⟨hd23, hd3, hc3⟩
    · rw [hi2] at hc3
      rw [hc1, hc3] at hc4
      simp only [List.slice_zero_j, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
        Nat.reduceEqDiff] at hc4
    rw [hi2] at hc3 hd23
    rw [hc3] at hc1
    rw [hc1] at hc4
    have hc4' := components_eq_singleton_of_length_eq_one _ (by
      simpa only [List.slice_zero_j, List.length_cons, Nat.reduceEqDiff] using hc4)
    rw [hc4'] at hc1
    step as ⟨s1, hs1, _⟩
    step as ⟨b, hb⟩
    rw [val_VERSION_V2] at hb
    split
    · rename_i h
      rw [h] at hb
      step as ⟨s2, hs2, _⟩
      step as ⟨s3, hs3, _⟩
      step as ⟨i3, hi3⟩
      step as ⟨s4, hs4, _⟩
      rw [hc1, hs2, hs3, hs4, ← of_decide_eq_true hb.symm, ← hs1, hi1, hi2, hi3]
    · rename_i h
      rw [Bool.not_eq_true] at h
      rw [h] at hb
      rw [WP.spec_ok]
      intro kid body tag heq
      rw [hc1] at heq
      simp only [List.cons.injEq] at heq
      exact of_decide_eq_false hb.symm (hs1 ▸ heq.1)

end rmcp.model.request_state_wire
