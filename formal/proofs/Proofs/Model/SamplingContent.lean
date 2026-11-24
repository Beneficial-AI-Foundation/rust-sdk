/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Proofs.External.Std

/-!
# Spec theorems for `SamplingContent` (M09–M12 and their joint lemmas)

`into_vec` (M09), `is_empty` (M10), `len` (M11) and `first` (M12) of
`rmcp::model::SamplingContent`, and the joint lemmas of plan Section 16.1 relating them
(`is_empty_eq_len_eq_zero`, `first_eq_head?_into_vec`, `len_eq_len_into_vec`). `Vec::is_empty`
and `slice::first` are used through their laws in `Proofs/External/Std.lean`.

Source: "crates/rmcp/src/model.rs", lines 2926–2963 at `7caec76`
-/

open Aeneas Aeneas.Std Result
open Proofs.External.WP (exists_ok_of_spec)

namespace rmcp.model.SamplingContent

/-- **Spec theorem for `rmcp::model::SamplingContent::into_vec`** (M09)

`Single x` gives the one-element vector `[x]`; `Multiple v` gives `v` (plan Section 16.1, M09;
`model.rs` lines 2925–2931, doc comment "Convert to a Vec regardless of whether it's single or
multiple", `Single(item) => vec![item]`, `Multiple(items) => items`). -/
@[step]
theorem into_vec_spec {T : Type} (self : model.SamplingContent T) :
    into_vec self ⦃ (result : alloc.vec.Vec T) =>
      match self with
      | .Single x => result.val = [x]
      | .Multiple v => result = v ⦄ := by
  match self with
  | .Single x =>
    simp only [into_vec, lift, Array.to_slice, Array.make, alloc.slice.Slice.into_vec, bind_tc_ok,
      WP.spec_ok]
  | .Multiple v => simp only [into_vec, WP.spec_ok]

/-- **Spec theorem for `rmcp::model::SamplingContent::is_empty`** (M10)

`Single _` is never empty; `Multiple v` is empty exactly when `v` has no element (plan Section
16.1, M10; `model.rs` lines 2933–2939, `Single(_) => false`, `Multiple(items) =>
items.is_empty()`). -/
@[step]
theorem is_empty_spec {T : Type} (self : model.SamplingContent T) :
    is_empty self ⦃ (result : Bool) =>
      match self with
      | .Single _ => result = false
      | .Multiple v => (result = true ↔ v.val = []) ⦄ := by
  match self with
  | .Single _ => simp only [is_empty, WP.spec_ok]
  | .Multiple v =>
    obtain ⟨b, hb, hbv⟩ := exists_ok_of_spec (alloc.vec.Vec.is_empty_spec Global v)
    simp only [is_empty, hb, hbv, WP.spec_ok, decide_eq_true_eq]

/-- **Spec theorem for `rmcp::model::SamplingContent::len`** (M11)

`Single _` has 1 item; `Multiple v` has `v.length` items (plan Section 16.1, M11; `model.rs`
lines 2941–2947, `Single(_) => 1`, `Multiple(items) => items.len()`). -/
@[step]
theorem len_spec {T : Type} (self : model.SamplingContent T) :
    len self ⦃ (result : Usize) =>
      match self with
      | .Single _ => result.val = 1
      | .Multiple v => result.val = v.val.length ⦄ := by
  match self with
  | .Single _ => simp only [len, WP.spec_ok, UScalar.ofNatCore_val_eq]
  | .Multiple v => simp only [len, alloc.vec.Vec.len, WP.spec_ok, Usize.ofNatCore_val_eq]

/-- **Spec theorem for `rmcp::model::SamplingContent::first`** (M12)

`Single x` gives `some x`; `Multiple v` gives the first element of `v`, `none` when `v` is empty
(plan Section 16.1, M12; `model.rs` lines 2957–2963, doc comment "Get the first item if present",
`Single(item) => Some(item)`, `Multiple(items) => items.first()`). Rust returns `Option<&T>`; the
translation returns the element itself. -/
@[step]
theorem first_spec {T : Type} (self : model.SamplingContent T) :
    first self ⦃ (result : Option T) =>
      match self with
      | .Single x => result = some x
      | .Multiple v => result = v.val.head? ⦄ := by
  match self with
  | .Single x => simp only [first, WP.spec_ok]
  | .Multiple v =>
    obtain ⟨r, hr, hrv⟩ :=
      exists_ok_of_spec (core.slice.Slice.first_spec (alloc.vec.Vec.deref v))
    simp only [first, hr, hrv, WP.spec_ok]
    rfl

/-- Joint lemma M10 `= (M11 = 0)`: `is_empty` is `len = 0` (plan Section 16.1; `model.rs` lines
2934–2947). -/
theorem is_empty_eq_len_eq_zero {T : Type} (self : model.SamplingContent T) :
    is_empty self = (do let n ← len self; ok (decide (n.val = 0))) := by
  match self with
  | .Single _ =>
    simp only [is_empty, len, bind_tc_ok, UScalar.ofNatCore_val_eq, one_ne_zero, decide_false]
  | .Multiple v =>
    obtain ⟨b, hb, hbv⟩ := exists_ok_of_spec (alloc.vec.Vec.is_empty_spec Global v)
    simp only [is_empty, hb, hbv, List.length_eq_zero_iff, len, alloc.vec.Vec.len, bind_tc_ok,
      Usize.ofNatCore_val_eq]

/-- Joint lemma M12 `= (M09).head?`: `first` is the first element of `into_vec` (plan Section
16.1; `model.rs` lines 2926–2931 and 2958–2963). In Rust `first` borrows and `into_vec`
consumes; the translation passes both the value. -/
theorem first_eq_head?_into_vec {T : Type} (self : model.SamplingContent T) :
    first self = (do let v ← into_vec self; ok v.val.head?) := by
  match self with
  | .Single x =>
    simp only [first, into_vec, lift, Array.to_slice, Array.make, alloc.slice.Slice.into_vec,
      bind_tc_ok, List.head?_cons]
  | .Multiple v =>
    obtain ⟨r, hr, hrv⟩ :=
      exists_ok_of_spec (core.slice.Slice.first_spec (alloc.vec.Vec.deref v))
    simp only [first, hr, hrv, into_vec, bind_tc_ok]
    rfl

/-- Joint lemma M11 `= (M09).length`: `len` is the length of `into_vec` (plan Section 16.1;
`model.rs` lines 2926–2931 and 2942–2947). -/
theorem len_eq_len_into_vec {T : Type} (self : model.SamplingContent T) :
    len self = (do let v ← into_vec self; ok (alloc.vec.Vec.len v)) := by
  match self with
  | .Single x =>
    simp only [len, into_vec, lift, Array.to_slice, Array.make, alloc.slice.Slice.into_vec,
      bind_tc_ok, alloc.vec.Vec.len, List.length_cons, List.length_nil, zero_add, ok.injEq]
    rfl
  | .Multiple v => simp only [len, alloc.vec.Vec.len, into_vec, bind_tc_ok]

end rmcp.model.SamplingContent
