/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Defs.JsonRpc

@[expose] public section

/-!
# Spec theorems for `JsonRpcMessage` (M01–M05, C03, joint lemma `exactly_one_some`)

The classifiers `into_request`, `into_response`, `into_notification`, `into_error` (M01–M04) and
`into_result` (M05) of `rmcp::model::JsonRpcMessage`, each a single `match` on the four variants;
the joint lemma that exactly one of M01–M04 is `Some` (plan Section 16.1), and C03
`into_result_eq`, the composition theorem of plan Section 16.4. Each proof splits on the variant
(a `match`: `cases` fails with a dependent elimination error on these generic goals) and
computes.

Source: "crates/rmcp/src/model.rs", lines 819–850 at `7caec76`
-/

open Aeneas Aeneas.Std Result
open Defs.JsonRpc

namespace rmcp.model.JsonRpcMessage

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
  match self with
  | .Request r => simp only [into_request, request, Request.injEq, WP.spec_ok]
  | .Response r =>
    simp only [into_request, kind, ne_eq, reduceCtorEq, not_false_eq_true, WP.spec_ok]
  | .Notification r =>
    simp only [into_request, kind, ne_eq, reduceCtorEq, not_false_eq_true, WP.spec_ok]
  | .Error r => simp only [into_request, kind, ne_eq, reduceCtorEq, not_false_eq_true, WP.spec_ok]

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
  match self with
  | .Request r =>
    simp only [into_response, kind, ne_eq, reduceCtorEq, not_false_eq_true, WP.spec_ok]
  | .Response r => simp only [into_response, response, Response.injEq, WP.spec_ok]
  | .Notification r =>
    simp only [into_response, kind, ne_eq, reduceCtorEq, not_false_eq_true, WP.spec_ok]
  | .Error r => simp only [into_response, kind, ne_eq, reduceCtorEq, not_false_eq_true, WP.spec_ok]

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
  match self with
  | .Request r =>
    simp only [into_notification, kind, ne_eq, reduceCtorEq, not_false_eq_true, WP.spec_ok]
  | .Response r =>
    simp only [into_notification, kind, ne_eq, reduceCtorEq, not_false_eq_true, WP.spec_ok]
  | .Notification r =>
    simp only [into_notification, notification, Notification.injEq, WP.spec_ok]
  | .Error r =>
    simp only [into_notification, kind, ne_eq, reduceCtorEq, not_false_eq_true, WP.spec_ok]

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
  match self with
  | .Request r => simp only [into_error, kind, ne_eq, reduceCtorEq, not_false_eq_true, WP.spec_ok]
  | .Response r => simp only [into_error, kind, ne_eq, reduceCtorEq, not_false_eq_true, WP.spec_ok]
  | .Notification r =>
    simp only [into_error, kind, ne_eq, reduceCtorEq, not_false_eq_true, WP.spec_ok]
  | .Error r => simp only [into_error, error, Error.injEq, WP.spec_ok]

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
  match self with
  | .Request r => simp only [into_result, kind, reduceCtorEq, or_false, WP.spec_ok]
  | .Response r => simp only [into_result, response, Response.injEq, WP.spec_ok]
  | .Notification r => simp only [into_result, kind, reduceCtorEq, or_true, WP.spec_ok]
  | .Error r => simp only [into_result, error, Error.injEq, WP.spec_ok]

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
  match self with
  | .Request _ =>
    simp only [into_request, into_response, into_notification, into_error, bind_ok, WP.spec_ok,
      Option.isSome_some, Option.isSome_none]
    decide
  | .Response _ =>
    simp only [into_request, into_response, into_notification, into_error, bind_ok, WP.spec_ok,
      Option.isSome_some, Option.isSome_none]
    decide
  | .Notification _ =>
    simp only [into_request, into_response, into_notification, into_error, bind_ok, WP.spec_ok,
      Option.isSome_some, Option.isSome_none]
    decide
  | .Error _ =>
    simp only [into_request, into_response, into_notification, into_error, bind_ok, WP.spec_ok,
      Option.isSome_some, Option.isSome_none]
    decide

end rmcp.model.JsonRpcMessage

namespace rmcp.model

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
  match m with
  | .Request _ =>
    simp only [JsonRpcMessage.into_result, JsonRpcMessage.into_response,
      JsonRpcMessage.into_error, bind_ok]
    rfl
  | .Response _ =>
    simp only [JsonRpcMessage.into_result, JsonRpcMessage.into_response,
      JsonRpcMessage.into_error, bind_ok]
    rfl
  | .Notification _ =>
    simp only [JsonRpcMessage.into_result, JsonRpcMessage.into_response,
      JsonRpcMessage.into_error, bind_ok]
    rfl
  | .Error _ =>
    simp only [JsonRpcMessage.into_result, JsonRpcMessage.into_response,
      JsonRpcMessage.into_error, bind_ok]
    rfl

end rmcp.model
