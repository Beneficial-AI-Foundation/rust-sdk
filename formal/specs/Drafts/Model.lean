/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Bytes
import Defs.IntParse
import Defs.JsonRpc

/-!
# Draft statements for the message model (M01–M14, C03, Section 16.1 joint lemmas)

Drafted by AI (Claude Code `mcp-spec`, model `claude-opus-5-5`) on 2026-11-24, plan step S24.
**spec: DRAFT.** Spec owner: Hoang Le Truong. None of these statements is signed off; each
needs at least two independent `mcp-review` runs and the spec owner's sign-off (plan Section 21).
The prover of a statement must not be its drafter (docs/WORKFLOW_AND_PR_GUIDE.md, "AI
contributions", rule 4).

Draft specification statements for the Phase 2 targets of `crates/rmcp/src/model.rs` (M01–M07,
M09–M14) and `crates/rmcp/src/model/task.rs` (M08), the composition theorem C03
`into_result_eq` (plan Section 16.4), the four joint lemmas of plan Section 16.1, and
the law `model = Defs.parseI64` of the `i64::from_str` model deferred from S27 (marked "S27
deferred law"). They are stated against the translated functions of `Rmcp.Funs` (Aeneas
`nightly-2026.08.20-5d08da4`; target `x86_64-unknown-linux-gnu`, `--no-default-features
--features <list>`, where `<list>` joins with commas the features `request-state`, `server`,
`client`, `client-side-sse`, `transport-streamable-http-server`,
`transport-streamable-http-client` and `auth`; plan Section 15) and use only `Defs.JsonRpc`,
`Defs.IntParse` (`Defs.parseI64`), `Defs.Bytes` (`Defs.utf8Bytes`) and plain Lean. Line
numbers refer to upstream `7caec76`, unmodified (plan Section 13); the generated `Source:` lines
of `model.rs` are two higher (patch 01).

Proof names follow plan Section 20: `<generated name>_spec`, restated later as
`Theorems.model.<Type>.<function>` (`Theorems.task.TaskStatus.is_terminal` for M08). At
incorporation the statements are split by Rust file: M08 goes to `Specs/Model/Task.lean`, the
rest to `Specs/Model.lean`; the S27 deferred law goes to `Specs/External.lean`.

This file is a draft: it lives in `formal/specs/Drafts/`, belongs to no library and is never
built by `lake build`. Each proof is a placeholder, allowed only here.

A statement `f x ⦃ (result : T) => P result ⦄` says that `f x` terminates without panicking and
that its result satisfies `P` (plan Section 3, "What a spec means"; Section 17). The
postcondition of each spec theorem M01–M14 (the `_spec` statements) determines the result
uniquely (M06 through the injectivity of `I64.val`), and the `_fail` statements, the joint
equations `is_empty_eq_len_eq_zero`, `first_eq_head?_into_vec`, `len_eq_len_into_vec` and the
composition theorem C03 fix the outcome exactly. Two statements do not determine their result,
by design: the joint lemma `exactly_one_some` says only that exactly one of the four results is
`some` (the spec theorems M01–M04 pin each of them), and the S27 deferred law leaves the
`ParseIntError` of an `Err` result unconstrained (M06 discards it). The only premise is the
size premise of M13/M14, inherited from the `String` deref model (a Lean `String` may exceed
`Usize.max` bytes, no Rust `String` does); each of M13/M14 has a companion statement for the
failing case, so every input is covered.
-/

open Aeneas Aeneas.Std Result
open Defs.JsonRpc

namespace rmcp.model.JsonRpcMessage

/-! ## M01–M05: classifying a JSON-RPC message (`model.rs` lines 819–850)

Generic in `Req`, `Resp`, `Noti`, with no premise (plan Section 17, "M01–M05"). The arms are
over the result; `Defs.JsonRpc.request` etc. are the values of the Rust constructors
(`model.rs` lines 789–818), and `Defs.JsonRpc.kind` the variant. -/

/-- **Spec theorem for `rmcp::model::JsonRpcMessage::into_request`** (M01)

`Some (request, id)` exactly when the message is the request with payload `request` and id
`id`; `None` for a response, a notification or an error (plan Section 16.1, M01; `model.rs`
lines 819–824: `JsonRpcMessage::Request(r) => Some((r.request, r.id))`, `_ => None`). -/
@[step]
theorem into_request_spec {Req Resp Noti : Type} (self : model.JsonRpcMessage Req Resp Noti) :
    into_request self ⦃ (result : Option (Req × model.NumberOrString)) =>
      match result with
      | some (request, id) => self = Defs.JsonRpc.request request id
      | none => kind self ≠ .request ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::JsonRpcMessage::into_response`** (M02)

`Some (result, id)` exactly when the message is the response with result `result` and id `id`;
`None` otherwise (plan Section 16.1, M02; `model.rs` lines 825–830:
`JsonRpcMessage::Response(r) => Some((r.result, r.id))`, `_ => None`). -/
@[step]
theorem into_response_spec {Req Resp Noti : Type} (self : model.JsonRpcMessage Req Resp Noti) :
    into_response self ⦃ (result : Option (Resp × model.NumberOrString)) =>
      match result with
      | some (response, id) => self = Defs.JsonRpc.response response id
      | none => kind self ≠ .response ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::JsonRpcMessage::into_notification`** (M03)

`Some notification` exactly when the message is the notification with that payload; `None`
otherwise (plan Section 16.1, M03; `model.rs` lines 831–836:
`JsonRpcMessage::Notification(n) => Some(n.notification)`, `_ => None`). -/
@[step]
theorem into_notification_spec {Req Resp Noti : Type}
    (self : model.JsonRpcMessage Req Resp Noti) :
    into_notification self ⦃ (result : Option Noti) =>
      match result with
      | some notification => self = Defs.JsonRpc.notification notification
      | none => kind self ≠ .notification ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::JsonRpcMessage::into_error`** (M04)

`Some (error, id)` exactly when the message is the error with data `error` and optional id `id`
(an error may have `id = None`, plan Section 22); `None` otherwise (plan Section 16.1, M04;
`model.rs` lines 837–842: `JsonRpcMessage::Error(e) => Some((e.error, e.id))`, `_ => None`). -/
@[step]
theorem into_error_spec {Req Resp Noti : Type} (self : model.JsonRpcMessage Req Resp Noti) :
    into_error self ⦃ (result : Option (model.ErrorData × Option model.NumberOrString)) =>
      match result with
      | some (error, id) => self = Defs.JsonRpc.error error id
      | none => kind self ≠ .error ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::JsonRpcMessage::into_result`** (M05)

A response with result `r` and id `i` gives `Some (Ok r, Some i)`; an error with data `e` and
optional id `i` gives `Some (Err e, i)`; a request or a notification gives `None` (plan Section
16.1, M05; `model.rs` lines 843–850). A result `Some (Ok _, None)` never occurs (its arm is
`False`): a response always has an id. -/
@[step]
theorem into_result_spec {Req Resp Noti : Type} (self : model.JsonRpcMessage Req Resp Noti) :
    into_result self ⦃ (result : Option (core.result.Result Resp model.ErrorData ×
        Option model.NumberOrString)) =>
      match result with
      | some (.Ok response, some id) => self = Defs.JsonRpc.response response id
      | some (.Ok _, none) => False
      | some (.Err error, id) => self = Defs.JsonRpc.error error id
      | none => kind self = .request ∨ kind self = .notification ⦄ := by
  sorry

end rmcp.model.JsonRpcMessage

namespace rmcp.model.NumberOrString

/-! ## M06, M07: request ids (`model.rs` lines 322–337) -/

/-- **Spec theorem for `rmcp::model::NumberOrString::numeric_string_value`** (M06)

`None` for a numeric id; for a string id, the integer its bytes denote under Rust's `i64::from_str`
grammar (`Defs.parseI64`: optional single `+`/`-`, at least one ASCII digit, nothing else, value
in `[-2^63, 2^63 - 1]`), `None` when the grammar rejects them (plan Section 16.1, M06; Section 17,
"M06"; `model.rs` lines 322–327: `Self::String(id) => id.parse().ok()`, `Self::Number(_) =>
None`). Stated as `result.map (·.val) = numericValue self`, which determines `result` because
`I64.val` is injective. No premise: `Arc` deref, `str::parse` and `Result::ok` never fail in
their models. The proof needs the S27 deferred law below. -/
@[step]
theorem numeric_string_value_spec (self : model.NumberOrString) :
    numeric_string_value self ⦃ (result : Option I64) =>
      result.map (·.val) = numericValue self ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::NumberOrString::matches_response_id`** (M07)

`true` exactly when the two ids are equal, or the request id `self` is a number `n` and the
response id is a string whose `Defs.parseI64` value is `n` (plan Section 16.1, M07; `model.rs`
lines 330–337: `self == response_id || matches!(self, Self::Number(request_id) if
response_id.numeric_string_value() == Some(*request_id))`).

Equality is Lean equality of `NumberOrString`, which is the derived `PartialEq` (line 304): equal
numbers, or string ids with equal bytes (the `Arc<str>` model compares contents, plan Section 17,
"M07"; a `Str` is determined by its bytes). The asymmetry is stated, not hidden (plan Section
17): `Number 1` matches `String "1"`, but `String "1"` does not match `Number 1` (the second
disjunct needs `self` to be a number). No premise. -/
@[step]
theorem matches_response_id_spec (self response_id : model.NumberOrString) :
    matches_response_id self response_id ⦃ (result : Bool) =>
      (result = true ↔
        self = response_id ∨
          ∃ n : I64, self = .Number n ∧ numericValue response_id = some n.val) ⦄ := by
  sorry

end rmcp.model.NumberOrString

namespace rmcp.model.task.TaskStatus

/-! ## M08: terminal task statuses (`task.rs` lines 36–40) -/

/-- **Spec theorem for `rmcp::model::task::TaskStatus::is_terminal`** (M08)

`true` exactly for `Completed`, `Failed` and `Cancelled`; `false` for `Working` and
`InputRequired` (plan Section 16.1, M08; `task.rs` lines 37–40, doc comment "Returns `true` for
terminal statuses (`completed`, `failed`, `cancelled`)" and `matches!(self, Self::Completed |
Self::Failed | Self::Cancelled)`). Restated as `Theorems.task.TaskStatus.is_terminal`. -/
@[step]
theorem is_terminal_spec (self : model.task.TaskStatus) :
    is_terminal self ⦃ (result : Bool) =>
      (result = true ↔ self = .Completed ∨ self = .Failed ∨ self = .Cancelled) ⦄ := by
  sorry

end rmcp.model.task.TaskStatus

namespace rmcp.model.SamplingContent

/-! ## M09–M12: sampling content (`model.rs` lines 2926–2963)

Generic in `T`, with no premise: a `Vec` holds at most `Usize.max` elements by construction, so
`len` cannot overflow. -/

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
  sorry

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
  sorry

/-- **Spec theorem for `rmcp::model::SamplingContent::len`** (M11)

`Single _` has 1 item; `Multiple v` has `v.length` items (plan Section 16.1, M11; `model.rs`
lines 2941–2947, `Single(_) => 1`, `Multiple(items) => items.len()`). -/
@[step]
theorem len_spec {T : Type} (self : model.SamplingContent T) :
    len self ⦃ (result : Usize) =>
      match self with
      | .Single _ => result.val = 1
      | .Multiple v => result.val = v.val.length ⦄ := by
  sorry

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
  sorry

end rmcp.model.SamplingContent

namespace rmcp.model.Reference

/-! ## M13, M14: completion references (`model.rs` lines 3741–3754)

`&prompt_ref.name` is a `String` deref (`Deref<Target = str>`), whose model fails with
`maximumSizeExceeded` for a Lean `String` of more than `Usize.max` bytes, which no Rust `String`
is (`trusted/Rmcp/FunsExternal.lean`; law `deref_spec`/`deref_fail` in `Specs/External.lean`).
The success statements take that size premise for the string they read (and only for it); the
`_fail` statements cover the remaining inputs. -/

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
  sorry

/-- M13, failing case: a prompt reference whose name has more than `Usize.max` bytes (a Lean
`String` that no Rust `String` is) gives `fail maximumSizeExceeded`, the failure of the `String`
deref model. With `as_prompt_name_spec` this covers every input. -/
theorem as_prompt_name_fail (p : model.PromptReference)
    (h_big : Usize.max < p.«name».utf8ByteSize) :
    as_prompt_name (.Prompt p) = fail .maximumSizeExceeded := by
  sorry

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
  sorry

/-- M14, failing case: a resource reference whose URI has more than `Usize.max` bytes gives
`fail maximumSizeExceeded`. With `as_resource_uri_spec` this covers every input. -/
theorem as_resource_uri_fail (r : model.ResourceTemplateReference)
    (h_big : Usize.max < r.uri.utf8ByteSize) :
    as_resource_uri (.Resource r) = fail .maximumSizeExceeded := by
  sorry

end rmcp.model.Reference

/-! ## Joint lemmas of plan Section 16.1

Stated with the targets because later phases use them as a set. Each is an equation between
translated computations (or a statement about a block of calls), so it also says that the calls
fail together or not at all; with the spec theorems above none of them fails. Names follow the
Mathlib naming guidelines (style guide, "Composition Theorems"); restated as
`Theorems.model.<Type>.<name>`. -/

namespace rmcp.model.SamplingContent

/-- Joint lemma M10 `= (M11 = 0)`: `is_empty` is `len = 0` (plan Section 16.1; `model.rs` lines
2934–2947). -/
theorem is_empty_eq_len_eq_zero {T : Type} (self : model.SamplingContent T) :
    is_empty self = (do let n ← len self; ok (decide (n.val = 0))) := by
  sorry

/-- Joint lemma M12 `= (M09).head?`: `first` is the first element of `into_vec` (plan Section
16.1; `model.rs` lines 2926–2931 and 2958–2963). In Rust `first` borrows and `into_vec`
consumes; the translation passes both the value. -/
theorem first_eq_head?_into_vec {T : Type} (self : model.SamplingContent T) :
    first self = (do let v ← into_vec self; ok v.val.head?) := by
  sorry

/-- Joint lemma M11 `= (M09).length`: `len` is the length of `into_vec` (plan Section 16.1;
`model.rs` lines 2926–2931 and 2942–2947). -/
theorem len_eq_len_into_vec {T : Type} (self : model.SamplingContent T) :
    len self = (do let v ← into_vec self; ok (alloc.vec.Vec.len v)) := by
  sorry

end rmcp.model.SamplingContent

namespace rmcp.model.JsonRpcMessage

/-- Joint lemma: exactly one of M01–M04 is `Some` for every message (plan Section 16.1;
`model.rs` lines 819–842). The four calls all succeed, and exactly one of the four results is
`some`. -/
theorem exactly_one_some {Req Resp Noti : Type} (self : model.JsonRpcMessage Req Resp Noti) :
    (do
      let a ← into_request self
      let b ← into_response self
      let c ← into_notification self
      let d ← into_error self
      ok [a.isSome, b.isSome, c.isSome, d.isSome])
      ⦃ (result : List Bool) => result.count true = 1 ⦄ := by
  sorry

end rmcp.model.JsonRpcMessage

namespace rmcp.model

/-! ## Composition theorem C03 (plan Section 16.4) -/

/-- **C03 `into_result_eq`**: `into_result` is `into_response` mapped to
`(Ok r, Some i)`, or else `into_error` mapped to `(Err e, i)` (plan Section 16.4, C03; uses M02,
M04, M05; `model.rs` lines 825–850). About the translated functions `into_result`,
`into_response` and `into_error`; an equation of computations, so it holds for every message,
including whether a call fails (none does, by M02, M04, M05). Routing code may use either form.
Restated as `Theorems.model.into_result_eq`; not tagged `@[step]`. -/
theorem into_result_eq {Req Resp Noti : Type}
    (m : model.JsonRpcMessage Req Resp Noti) :
    JsonRpcMessage.into_result m = (do
      let r ← JsonRpcMessage.into_response m
      let e ← JsonRpcMessage.into_error m
      ok ((r.map fun (x, i) => (core.result.Result.Ok x, some i)) <|>
        (e.map fun (x, i) => (core.result.Result.Err x, i)))) := by
  sorry

end rmcp.model

/-! ## S27 deferred law: the `i64::from_str` model agrees with `Defs.parseI64`

Deferred from plan step S27 until `Defs.parseI64` exists (plan Section 17, "M06"; Section 21,
S27: "the `parseI64` law after S24"; `formal/trusted/evidence/README.md`, integer parsing). It
belongs with the other integer-parsing laws in `Proofs/External/IntParse.lean`, restated as
`Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_eq_parseI64` in
`Specs/External.lean`. It is the step from the model (`ExtModel.i64FromAscii`, transcribed from
`core/src/num/mod.rs` lines 1626–1844 of the pinned toolchain) to the documented grammar; M06
uses it. -/

/-- **S27 deferred law.** `i64::from_str` (the model in `trusted/Rmcp/FunsExternal.lean`) never
fails, and it returns `Ok n` exactly when `Defs.parseI64` accepts the bytes of `src`, with
`n.val` the value `Defs.parseI64` gives; otherwise `Err _` (the error kind is not constrained:
M06 discards it). -/
theorem I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_eq_parseI64 (src : Str) :
    I64.Insts.CoreStrTraitsFromStrParseIntError.from_str src
      ⦃ (result : core.result.Result I64 core.num.error.ParseIntError) =>
        (match result with
         | .Ok n => some n.val
         | .Err _ => none) = Defs.parseI64 src.val ⦄ := by
  sorry
