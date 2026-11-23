/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire
import Proofs.Model.RequestStateWire.Common

/-!
# Spec theorem for `component_count` (W06)

Number of `.`-components of a byte string: a counter starting at 1, incremented at every `.`.

The loop invariant says that the counter is one more than the number of `.` bytes before the
index; `Proofs.RequestStateWire.length_components` relates that count to `components`.

Source: "crates/rmcp/src/model/request_state_wire.rs", line 92 in the patched copy
(patch 01 on origin/main 7caec76, D2 fallback 2026-11-23); line numbers refer to it.
-/

open Aeneas Aeneas.Std Result

namespace rmcp.model.request_state_wire

open Defs.Wire Proofs.RequestStateWire

/-- **Spec theorem for `rmcp::model::request_state_wire::component_count`** (W06)

`component_count s` is the number of `.`-components of `s`, `(splitOn '.' s).length`, which is
one more than the number of `.` bytes (plan Section 2.1, W06; plan Section 3, "W06–W09 —
splitting"; lines 91–102).

Lean-model domain (plan Section 3, "Lean-model domains"): the counter starts at 1 and is
incremented once per `.` byte (lines 93, 96–98), so the counter can overflow only when the slice
has `Usize.max` or more `.` bytes. `h_count` excludes that; it holds for every Rust slice, whose
length is at most `isize::MAX < usize::MAX`. -/
@[step]
theorem component_count_spec (s : Slice U8)
    (h_count : s.val.count dot < Usize.max) :
    component_count s ⦃ (result : Usize) =>
      result.val = (components s.val).length ∧
      result.val = s.val.count dot + 1 ⦄ := by
  unfold component_count component_count_loop
  rw [length_components]
  apply loop.spec_decr_nat (measure := fun x : Usize × Usize => s.length - x.2.val)
    (inv := fun x : Usize × Usize => x.2.val ≤ s.length ∧
        x.1.val = (s.val.take x.2.val).count dot + 1)
  · rintro ⟨n, i⟩ ⟨hi, hn⟩
    unfold component_count_loop.body
    simp only at hi hn
    step*
    · have hlt : i.val < s.val.length := by scalar_tac
      have hc := count_take_add_one s.val i.val hlt
      have hle := (List.take_sublist (i.val + 1) s.val).count_le dot
      split
      · have hd : s.val[i.val] = dot := by rw [← i2_post]; simp_all [dot]
        rw [if_pos hd] at hc
        step*
      · have hd : ¬ s.val[i.val] = dot := by rw [← i2_post]; simp_all [dot]
        rw [if_neg hd] at hc
        step*
    · have hia : i.val = s.val.length := by scalar_tac
      rw [hn, hia, List.take_length]
      exact ⟨rfl, rfl⟩
  · simp

end rmcp.model.request_state_wire
