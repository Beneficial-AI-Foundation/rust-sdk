/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Defs
public import Proofs.Model.JsonRpcMessage
public import Proofs.Model.SamplingContent
public import Proofs.Model.Reference

@[expose] public section

/-!
# Spec file for crates/rmcp/src/model.rs (Phase 2, public API: M01–M05, M09–M14, C03)

Summary (one row per theorem below; index of all guarantees: `formal/specs/README.md`). A row
about a call `f x ⦃ r => P r ⦄` says that the call does not panic and that its result satisfies
the guarantee; rows written "a = b" are equations between computations of the translated code.

| ID | Function | Guarantee | Assumptions |
|---|---|---|---|
| M01 | `JsonRpcMessage::into_request` | `Some((p, id))` iff it is request `p`, `id` | none |
| M02 | `JsonRpcMessage::into_response` | `Some((r, id))` iff it is response `r`, `id` | none |
| M03 | `JsonRpcMessage::into_notification` | `Some(n)` iff it is notification `n` | none |
| M04 | `JsonRpcMessage::into_error` | `Some((e, id))` iff it is error `e`, optional `id` | none |
| M05 | `JsonRpcMessage::into_result` | response: `(Ok, Some id)`; error: `(Err, id)`; (c) | none |
| M09 | `SamplingContent::into_vec` | `Single(x)` gives `[x]`, `Multiple(v)` gives `v` | none |
| M10 | `SamplingContent::is_empty` | `false` for `Single`; else `true` iff `v` empty | none |
| M11 | `SamplingContent::len` | 1 for `Single`; `v.len()` for `Multiple(v)` | none |
| M12 | `SamplingContent::first` | `Some(x)` for `Single(x)`; `Multiple(v)`: first of `v` | none |
| M13 | `Reference::as_prompt_name` | prompt: `Some` of its name's bytes; else `None` | (a) |
| M13 | `…::as_prompt_name` (`_fail`) | name over `usize::MAX` bytes: fails (Lean only) | (b) |
| M14 | `Reference::as_resource_uri` | resource: `Some` of its URI's bytes; else `None` | (a) |
| M14 | `…::as_resource_uri` (`_fail`) | URI over `usize::MAX` bytes: fails (Lean only) | (b) |
| joint | `is_empty`, `len` | `is_empty()` = `len() == 0` | none |
| joint | `first`, `into_vec` | `first()` = head of `into_vec()` | none |
| joint | `len`, `into_vec` | `len()` = `into_vec().len()` | none |
| joint | `into_request` … `into_error` | the four succeed; exactly one returns `Some` | none |
| C03 | `into_result` | = `into_response` as `(Ok, Some id)`, else `into_error` | none |

(a) the name or URI has at most `usize::MAX` UTF-8 bytes (always true of a Rust `String`; the
Lean `String` model needs it). (b) the name or URI has more than `usize::MAX` bytes; the `_fail`
rows describe the Lean model, not a Rust behaviour. "joint": a joint lemma of plan Section 16.1.
C03 in full: `into_result` is `into_response` mapped to `(Ok(r), Some(id))`, or else `into_error`
mapped to `(Err(e), id)`. (c) `None` exactly for a request or a notification.

This file holds only the public API of `model.rs` (functions `pub` in upstream rmcp; human
decision 2026-11-24). The `pub(crate)` functions M06 `NumberOrString::numeric_string_value` and
M07 `NumberOrString::matches_response_id` are in `formal/proofs/Proofs/Internal/Model.lean`.

Statements of the public Phase 2 targets of `model.rs` (plan Section 16.1), each restated as a
theorem `Theorems.model.<Type>.<function>` proved by the spec theorem in `Proofs/Model/<Type>.lean`
and followed by the assumptions its proof depends on, checked by `#print axioms` under
`#guard_msgs`. M08 (`model/task.rs`) is in `Specs/Model/Task.lean`. Signed off by the spec owner
on 2026-11-24 (S24/S25 spec cycle, `STATUS.md` at 9047c72); the signed-off text was in
`specs/Drafts/Model.lean`, removed at incorporation.

Translated configuration (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
`--no-default-features` with the features `request-state`, `server`, `client`, `client-side-sse`,
`transport-streamable-http-server`, `transport-streamable-http-client` and `auth` (widened for
Phase 2, plan Section 15), with `overflow-checks=true` and `debug-assertions=true` (plan
Section 1). Aeneas `nightly-2026.11.24-fb44cb4` (until 2026-11-24 `nightly-2026.08.20-5d08da4`).
Line numbers refer to upstream `7caec76`, unmodified (plan Section 13); the generated `Source:` lines of `model.rs` are two higher
(patch 01).

Definitions used: `Defs.JsonRpc` (`kind`, `MessageKind`, `request`, `response`, `notification`,
`error`) and `Defs.Bytes` (`Defs.utf8Bytes`).

External models used (`trusted/Rmcp/FunsExternal.lean`): M13/M14 use the `String` deref model
(line 706), which fails with `maximumSizeExceeded` for a Lean `String` of more than `Usize.max`
bytes (no Rust `String` is), hence their size premises and `_fail` companions; M10 uses
`Vec::is_empty` (`alloc.vec.Vec.is_empty`; until 2026-11-24 a project model, since the Aeneas
upgrade the Aeneas library's definition) and M12 `<[T]>::first` (`core.slice.Slice.first`,
line 799). No statement reaches a native-code assumption (`…_native.decide.ax_<n>`); none
exists since the Aeneas upgrade of 2026-11-24. 13 of the 18 `#print axioms` lists below changed
in that upgrade (standard axioms added), re-signed by the spec owner in the batch of 2026-11-24.

From the Aeneas library (`Aeneas/Std/Vec.lean`; definitions, not trusted models): M09 uses
`<[T]>::into_vec` (`alloc.slice.Slice.into_vec`), M11 `Vec::len` (`alloc.vec.Vec.len`) and M12
`Vec::deref` (`alloc.vec.Vec.deref`).

Statements here, in Rust source order: M01 (819), M02 (825), M03 (831), M04 (837), M05 (843),
M09 (2926), M10 (2934), M11 (2942), M12 (2958), M13 (3741, with `as_prompt_name_fail`), M14
(3749, with `as_resource_uri_fail`); then the joint lemmas of plan Section 16.1
(`SamplingContent.is_empty_eq_len_eq_zero`, `SamplingContent.first_eq_head?_into_vec`,
`SamplingContent.len_eq_len_into_vec`, `JsonRpcMessage.exactly_one_some`), and last the
composition theorem C03 `into_result_eq` (plan Section 16.4, proved in
`Proofs/Model/JsonRpcMessage.lean`).

Not translated (outside the Phase 2 scope, plan Section 13, "Not claimed"): every other item of
`model.rs`. Besides the thirteen `model.rs` targets (M06/M07 are in
`formal/proofs/Proofs/Internal/Model.lean`), the translation contains only the derived `PartialEq`
of `NumberOrString` (line 304), which M07 calls; no statement is about it.
-/

open Aeneas Aeneas.Std Result
open rmcp  -- for `model.…` in the statements; theorems named in full
open Defs.JsonRpc

/-- M01 `into_request`: `Some (request, id)` exactly for the request with that payload and id. -/
theorem Theorems.model.JsonRpcMessage.into_request
    {Req Resp Noti : Type} (self : model.JsonRpcMessage Req Resp Noti) :
    rmcp.model.JsonRpcMessage.into_request self ⦃
      (result : Option (Req × model.NumberOrString)) =>
      match result with
      | some (request, id) => self = Defs.JsonRpc.request request id
      | none => kind self ≠ .request ⦄ :=
  rmcp.model.JsonRpcMessage.into_request_spec self

/--
info: 'Theorems.model.JsonRpcMessage.into_request' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.JsonRpcMessage.into_request

/-- M02 `into_response`: `Some (result, id)` exactly for the response with that result and id. -/
theorem Theorems.model.JsonRpcMessage.into_response
    {Req Resp Noti : Type} (self : model.JsonRpcMessage Req Resp Noti) :
    rmcp.model.JsonRpcMessage.into_response self ⦃
      (result : Option (Resp × model.NumberOrString)) =>
      match result with
      | some (response, id) => self = Defs.JsonRpc.response response id
      | none => kind self ≠ .response ⦄ :=
  rmcp.model.JsonRpcMessage.into_response_spec self

/--
info: 'Theorems.model.JsonRpcMessage.into_response' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.JsonRpcMessage.into_response

/-- M03 `into_notification`: `Some notification` exactly for the notification with that payload. -/
theorem Theorems.model.JsonRpcMessage.into_notification {Req Resp Noti : Type}
    (self : model.JsonRpcMessage Req Resp Noti) :
    rmcp.model.JsonRpcMessage.into_notification self ⦃ (result : Option Noti) =>
      match result with
      | some notification => self = Defs.JsonRpc.notification notification
      | none => kind self ≠ .notification ⦄ :=
  rmcp.model.JsonRpcMessage.into_notification_spec self

/--
info: 'Theorems.model.JsonRpcMessage.into_notification' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.JsonRpcMessage.into_notification

/-- M04 `into_error`: `Some (error, id)` exactly for the error with that data and optional id. -/
theorem Theorems.model.JsonRpcMessage.into_error
    {Req Resp Noti : Type} (self : model.JsonRpcMessage Req Resp Noti) :
    rmcp.model.JsonRpcMessage.into_error self ⦃
      (result : Option (model.ErrorData × Option model.NumberOrString)) =>
      match result with
      | some (error, id) => self = Defs.JsonRpc.error error id
      | none => kind self ≠ .error ⦄ :=
  rmcp.model.JsonRpcMessage.into_error_spec self

/--
info: 'Theorems.model.JsonRpcMessage.into_error' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.JsonRpcMessage.into_error

/-- M05 `into_result`: `Some (Ok r, Some i)` for a response, `Some (Err e, i)` for an error, `None`
for a request or a notification. -/
theorem Theorems.model.JsonRpcMessage.into_result
    {Req Resp Noti : Type} (self : model.JsonRpcMessage Req Resp Noti) :
    rmcp.model.JsonRpcMessage.into_result self ⦃
      (result : Option (core.result.Result Resp model.ErrorData ×
        Option model.NumberOrString)) =>
      match result with
      | some (.Ok response, some id) => self = Defs.JsonRpc.response response id
      | some (.Ok _, none) => False
      | some (.Err error, id) => self = Defs.JsonRpc.error error id
      | none => kind self = .request ∨ kind self = .notification ⦄ :=
  rmcp.model.JsonRpcMessage.into_result_spec self

/--
info: 'Theorems.model.JsonRpcMessage.into_result' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.JsonRpcMessage.into_result

/-- M09 `into_vec`: `Single x` gives `[x]`, `Multiple v` gives `v`. -/
theorem Theorems.model.SamplingContent.into_vec {T : Type} (self : model.SamplingContent T) :
    rmcp.model.SamplingContent.into_vec self ⦃ (result : alloc.vec.Vec T) =>
      match self with
      | .Single x => result.val = [x]
      | .Multiple v => result = v ⦄ :=
  rmcp.model.SamplingContent.into_vec_spec self

/--
info: 'Theorems.model.SamplingContent.into_vec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.SamplingContent.into_vec

/-- M10 `is_empty`: `false` for `Single _`; for `Multiple v`, `true` iff `v` is empty. -/
theorem Theorems.model.SamplingContent.is_empty {T : Type} (self : model.SamplingContent T) :
    rmcp.model.SamplingContent.is_empty self ⦃ (result : Bool) =>
      match self with
      | .Single _ => result = false
      | .Multiple v => (result = true ↔ v.val = []) ⦄ :=
  rmcp.model.SamplingContent.is_empty_spec self

/--
info: 'Theorems.model.SamplingContent.is_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.SamplingContent.is_empty

/-- M11 `len`: 1 for `Single _`, `v.length` for `Multiple v`. -/
theorem Theorems.model.SamplingContent.len {T : Type} (self : model.SamplingContent T) :
    rmcp.model.SamplingContent.len self ⦃ (result : Usize) =>
      match self with
      | .Single _ => result.val = 1
      | .Multiple v => result.val = v.val.length ⦄ :=
  rmcp.model.SamplingContent.len_spec self

/--
info: 'Theorems.model.SamplingContent.len' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.SamplingContent.len

/-- M12 `first`: `some x` for `Single x`, the head of `v` for `Multiple v`. -/
theorem Theorems.model.SamplingContent.first {T : Type} (self : model.SamplingContent T) :
    rmcp.model.SamplingContent.first self ⦃ (result : Option T) =>
      match self with
      | .Single x => result = some x
      | .Multiple v => result = v.val.head? ⦄ :=
  rmcp.model.SamplingContent.first_spec self

/--
info: 'Theorems.model.SamplingContent.first' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.SamplingContent.first

/-- M13 `as_prompt_name`: for a prompt reference, `Some s` with the UTF-8 bytes of its name (name at
most `Usize.max` bytes); `None` for a resource reference. -/
theorem Theorems.model.Reference.as_prompt_name (self : model.Reference)
    (h_size : ∀ p, self = .Prompt p → p.«name».utf8ByteSize ≤ Usize.max) :
    rmcp.model.Reference.as_prompt_name self ⦃ (result : Option Str) =>
      match self with
      | .Prompt p => ∃ s, result = some s ∧ s.val = Defs.utf8Bytes p.«name»
      | .Resource _ => result = none ⦄ :=
  rmcp.model.Reference.as_prompt_name_spec self h_size

/--
info: 'Theorems.model.Reference.as_prompt_name' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.Reference.as_prompt_name

/-- M13, failing case: a prompt name of more than `Usize.max` bytes gives `fail
maximumSizeExceeded`. -/
theorem Theorems.model.Reference.as_prompt_name_fail (p : model.PromptReference)
    (h_big : Usize.max < p.«name».utf8ByteSize) :
    rmcp.model.Reference.as_prompt_name (.Prompt p) = fail .maximumSizeExceeded :=
  rmcp.model.Reference.as_prompt_name_fail p h_big

/--
info: 'Theorems.model.Reference.as_prompt_name_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.Reference.as_prompt_name_fail

/-- M14 `as_resource_uri`: for a resource reference, `Some s` with the UTF-8 bytes of its URI (URI
at most `Usize.max` bytes); `None` for a prompt reference. -/
theorem Theorems.model.Reference.as_resource_uri (self : model.Reference)
    (h_size : ∀ r, self = .Resource r → r.uri.utf8ByteSize ≤ Usize.max) :
    rmcp.model.Reference.as_resource_uri self ⦃ (result : Option Str) =>
      match self with
      | .Resource r => ∃ s, result = some s ∧ s.val = Defs.utf8Bytes r.uri
      | .Prompt _ => result = none ⦄ :=
  rmcp.model.Reference.as_resource_uri_spec self h_size

/--
info: 'Theorems.model.Reference.as_resource_uri' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.Reference.as_resource_uri

/-- M14, failing case: a resource URI of more than `Usize.max` bytes gives `fail
maximumSizeExceeded`. -/
theorem Theorems.model.Reference.as_resource_uri_fail (r : model.ResourceTemplateReference)
    (h_big : Usize.max < r.uri.utf8ByteSize) :
    rmcp.model.Reference.as_resource_uri (.Resource r) = fail .maximumSizeExceeded :=
  rmcp.model.Reference.as_resource_uri_fail r h_big

/--
info: 'Theorems.model.Reference.as_resource_uri_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.Reference.as_resource_uri_fail

/-- Joint lemma (plan Section 16.1) M10 `= (M11 = 0)`: `is_empty` is `len = 0`, as computations. -/
theorem Theorems.model.SamplingContent.is_empty_eq_len_eq_zero
    {T : Type} (self : model.SamplingContent T) :
    rmcp.model.SamplingContent.is_empty self =
      (do let n ← rmcp.model.SamplingContent.len self; ok (decide (n.val = 0))) :=
  rmcp.model.SamplingContent.is_empty_eq_len_eq_zero self

/--
info: 'Theorems.model.SamplingContent.is_empty_eq_len_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.SamplingContent.is_empty_eq_len_eq_zero

/-- Joint lemma (plan Section 16.1) M12 `= (M09).head?`: `first` is the head of `into_vec`, as
computations. -/
theorem Theorems.model.SamplingContent.first_eq_head?_into_vec
    {T : Type} (self : model.SamplingContent T) :
    rmcp.model.SamplingContent.first self =
      (do let v ← rmcp.model.SamplingContent.into_vec self; ok v.val.head?) :=
  rmcp.model.SamplingContent.first_eq_head?_into_vec self

/--
info: 'Theorems.model.SamplingContent.first_eq_head?_into_vec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.SamplingContent.first_eq_head?_into_vec

/-- Joint lemma (plan Section 16.1) M11 `= (M09).length`: `len` is the length of `into_vec`, as
computations. -/
theorem Theorems.model.SamplingContent.len_eq_len_into_vec
    {T : Type} (self : model.SamplingContent T) :
    rmcp.model.SamplingContent.len self =
      (do let v ← rmcp.model.SamplingContent.into_vec self; ok (alloc.vec.Vec.len v)) :=
  rmcp.model.SamplingContent.len_eq_len_into_vec self

/--
info: 'Theorems.model.SamplingContent.len_eq_len_into_vec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.SamplingContent.len_eq_len_into_vec

/-- Joint lemma (plan Section 16.1): the calls M01–M04 all succeed and exactly one of their
results is `some`. -/
theorem Theorems.model.JsonRpcMessage.exactly_one_some
    {Req Resp Noti : Type} (self : model.JsonRpcMessage Req Resp Noti) :
    (do
      let a ← rmcp.model.JsonRpcMessage.into_request self
      let b ← rmcp.model.JsonRpcMessage.into_response self
      let c ← rmcp.model.JsonRpcMessage.into_notification self
      let d ← rmcp.model.JsonRpcMessage.into_error self
      ok [a.isSome, b.isSome, c.isSome, d.isSome])
      ⦃ (result : List Bool) => result.count true = 1 ⦄ :=
  rmcp.model.JsonRpcMessage.exactly_one_some self

/--
info: 'Theorems.model.JsonRpcMessage.exactly_one_some' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.JsonRpcMessage.exactly_one_some

/-- C03 `into_result_eq` (plan Section 16.4; uses M02, M04, M05): `into_result` is `into_response`
mapped to `(Ok r, Some i)`, or else `into_error` mapped to `(Err e, i)`; an equation of computations
over the translated functions, for every message. -/
theorem Theorems.model.into_result_eq {Req Resp Noti : Type}
    (m : model.JsonRpcMessage Req Resp Noti) :
    rmcp.model.JsonRpcMessage.into_result m = (do
      let r ← rmcp.model.JsonRpcMessage.into_response m
      let e ← rmcp.model.JsonRpcMessage.into_error m
      ok ((r.map fun (x, i) => (core.result.Result.Ok x, some i)) <|>
        (e.map fun (x, i) => (core.result.Result.Err x, i)))) :=
  rmcp.model.into_result_eq m

/--
info: 'Theorems.model.into_result_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.into_result_eq
