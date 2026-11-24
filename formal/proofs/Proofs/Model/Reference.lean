/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Bytes
import Proofs.External.String

/-!
# Spec theorems for `Reference` (M13, M14)

`as_prompt_name` (M13) and `as_resource_uri` (M14) of `rmcp::model::Reference` return the
dereferenced `String` of the matching variant. The proofs use the signed-off `String` deref laws
of `Proofs/External/String.lean`: `deref_spec` (the UTF-8 bytes, when `String.utf8ByteSize` is at
most `Usize.max`) and `deref_fail` (the other case, used by the `_fail` theorems).

Source: "crates/rmcp/src/model.rs", lines 3741–3754 at `7caec76`
-/

open Aeneas Aeneas.Std Result

namespace rmcp.model.Reference

/-- **Spec theorem for `rmcp::model::Reference::as_prompt_name`** (M13)

For a prompt reference `p`, `Some s` where `s` holds exactly the UTF-8 bytes of `p.name`; for a
resource reference, `None` (plan Section 16.1, M13; `model.rs` lines 3740–3746, doc comment
"Extract prompt name if this is a prompt reference", `Self::Prompt(prompt_ref) =>
Some(&prompt_ref.name)`, `_ => None`). Premise: the name of a prompt reference has at most
`Usize.max` bytes (Lean-model domain; see `as_prompt_name_fail`). -/
@[step]
theorem as_prompt_name_spec (self : model.Reference)
    (h_size : ∀ p, self = .Prompt p → p.«name».utf8ByteSize ≤ Usize.max) :
    as_prompt_name self ⦃ (result : Option Str) =>
      match self with
      | .Prompt p => ∃ s, result = some s ∧ s.val = Defs.utf8Bytes p.«name»
      | .Resource _ => result = none ⦄ := by
  match self with
  | .Resource _ => simp only [as_prompt_name, WP.spec_ok]
  | .Prompt p =>
    obtain ⟨s, hs, hv⟩ := WP.spec_imp_exists
      (alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec p.«name» (h_size p rfl))
    simp only [as_prompt_name, hs, bind_tc_ok, WP.spec_ok]
    exact ⟨s, rfl, hv⟩

/-- M13, failing case: a prompt reference whose name has more than `Usize.max` bytes (a Lean
`String` that no Rust `String` is) gives `fail maximumSizeExceeded`, the failure of the `String`
deref model. With `as_prompt_name_spec` this covers every input. -/
theorem as_prompt_name_fail (p : model.PromptReference)
    (h_big : Usize.max < p.«name».utf8ByteSize) :
    as_prompt_name (.Prompt p) = fail .maximumSizeExceeded := by
  simp only [as_prompt_name,
    alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_fail p.«name» h_big, bind_tc_fail]

/-- **Spec theorem for `rmcp::model::Reference::as_resource_uri`** (M14)

For a resource reference `r`, `Some s` where `s` holds exactly the UTF-8 bytes of `r.uri`; for
a prompt reference, `None` (plan Section 16.1, M14; `model.rs` lines 3748–3754, doc comment
"Extract resource URI if this is a resource reference", `Self::Resource(resource_ref) =>
Some(&resource_ref.uri)`, `_ => None`). Premise: the URI of a resource reference has at most
`Usize.max` bytes (Lean-model domain; see `as_resource_uri_fail`). -/
@[step]
theorem as_resource_uri_spec (self : model.Reference)
    (h_size : ∀ r, self = .Resource r → r.uri.utf8ByteSize ≤ Usize.max) :
    as_resource_uri self ⦃ (result : Option Str) =>
      match self with
      | .Resource r => ∃ s, result = some s ∧ s.val = Defs.utf8Bytes r.uri
      | .Prompt _ => result = none ⦄ := by
  match self with
  | .Prompt _ => simp only [as_resource_uri, WP.spec_ok]
  | .Resource r =>
    obtain ⟨s, hs, hv⟩ := WP.spec_imp_exists
      (alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec r.uri (h_size r rfl))
    simp only [as_resource_uri, hs, bind_tc_ok, WP.spec_ok]
    exact ⟨s, rfl, hv⟩

/-- M14, failing case: a resource reference whose URI has more than `Usize.max` bytes gives
`fail maximumSizeExceeded`. With `as_resource_uri_spec` this covers every input. -/
theorem as_resource_uri_fail (r : model.ResourceTemplateReference)
    (h_big : Usize.max < r.uri.utf8ByteSize) :
    as_resource_uri (.Resource r) = fail .maximumSizeExceeded := by
  simp only [as_resource_uri,
    alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_fail r.uri h_big, bind_tc_fail]

end rmcp.model.Reference
