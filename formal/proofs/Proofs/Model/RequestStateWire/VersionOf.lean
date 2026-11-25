/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Defs.Wire
public import Proofs.Model.RequestStateWire.Common
public import Proofs.Model.RequestStateWire.BytesEq

@[expose] public section

/-!
# Spec theorem for `version_of` (W07)

Version tag of a token: the prefix up to the first `.` (found with `next_dot`, W05) is compared
with `VERSION_V1`, then `VERSION_V2` (with `bytes_eq`, W04).

W05 and W04 are used through `step`. `Proofs.RequestStateWire.components_drop_of_next_dot_post`
turns the postcondition of `next_dot_spec` into "the prefix is the first component".

Source: "crates/rmcp/src/model/request_state_wire.rs", line 115 in the patched copy
(patch 01 on origin/main 7caec76, D2 fallback 2026-11-23); line numbers refer to it.
-/

open Aeneas Aeneas.Std Result

namespace rmcp.model.request_state_wire

open Defs.Wire Proofs.RequestStateWire

/-- **Spec theorem for `rmcp::model::request_state_wire::version_of`** (W07)

`version_of s` is `Some V1` iff the first `.`-component of `s` is `"rs1"`, `Some V2` iff it is
`"rs2"`, and `None` otherwise (plan Section 2.1, W07; lines 114–124: the prefix up to the first
`.` (line 116) is compared with `VERSION_V1` (line 117), then `VERSION_V2` (line 119)).
`components s` is never empty, so `head?` is its first component. No precondition. -/
@[step]
theorem version_of_spec (s : Slice U8) :
    version_of s ⦃ (result : Option Version) =>
      match result with
      | some .V1 => (components s.val).head? = some versionV1
      | some .V2 => (components s.val).head? = some versionV2
      | none =>
        (components s.val).head? ≠ some versionV1 ∧
        (components s.val).head? ≠ some versionV2 ⦄ := by
  unfold version_of
  step as ⟨i, hi1, hi2⟩
  have hhead : (components s.val).head? = some (s.val.slice 0 i.val) := by
    rcases components_drop_of_next_dot_post s.val 0 i.val hi1 hi2 with
      ⟨hl, hc⟩ | ⟨-, -, hc⟩
    · rw [List.drop_zero] at hc
      rw [hc, hl, List.slice, List.drop_zero, Nat.sub_zero, List.take_length]; rfl
    · rw [List.drop_zero] at hc
      rw [hc]; rfl
  have hle : i.val ≤ s.length := le_length_of_next_dot_post s 0#usize i hi2
  step as ⟨first, hf, _⟩
  rw [← hf] at hhead
  step as ⟨b, hb⟩
  rw [val_VERSION_V1] at hb
  split
  · rename_i h
    rw [h] at hb
    rw [hhead, of_decide_eq_true hb.symm, WP.spec_ok]
  · rename_i h
    rw [Bool.not_eq_true] at h
    rw [h] at hb
    step as ⟨b1, hb1⟩
    rw [val_VERSION_V2] at hb1
    split
    · rename_i h1
      rw [h1] at hb1
      rw [hhead, of_decide_eq_true hb1.symm, WP.spec_ok]
    · rename_i h1
      rw [Bool.not_eq_true] at h1
      rw [h1] at hb1
      rw [WP.spec_ok, hhead, ne_eq, Option.some.injEq, ne_eq, Option.some.injEq]
      exact ⟨of_decide_eq_false hb.symm, of_decide_eq_false hb1.symm⟩

end rmcp.model.request_state_wire
