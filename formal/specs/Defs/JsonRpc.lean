/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Aeneas
public import Rmcp.Types
public import Rmcp.TypesExternal
public import Defs.IntParse

@[expose] public section

/-!
# Definitions for the JSON-RPC message model statements (M01–M07, C03)

Definitions that the statements of the message-model functions M01–M07 and the composition
theorem C03 (plan Sections 16.1 and 16.4) are written in: the four kinds of a JSON-RPC message,
the four messages built by the Rust constructors `JsonRpcMessage::{request, response, error,
notification}`, and the numeric value that a request id written as a string denotes (through
`Defs.parseI64`).

Rust source: `crates/rmcp/src/model.rs` at upstream `7caec76`, unmodified (plan Section 13);
line numbers below refer to it (the generated `Source:` lines are two higher, because the
committed translation was generated from the copy with patch 01). The definitions use the
generated types of `Rmcp.Types` (`rmcp.model.JsonRpcMessage`, `rmcp.model.NumberOrString`,
`rmcp.model.ErrorData`) and the model of `Arc` in `Rmcp.TypesExternal` (a structure holding its
value), but no translated or external function. Everything lives in the namespace
`Defs.JsonRpc`.
-/

namespace Defs.JsonRpc

open Aeneas.Std rmcp

/-! ## Message kinds -/

/-- The four kinds of a JSON-RPC message: the four variants of `pub enum JsonRpcMessage`
(`model.rs` lines 776–785: `Request`, `Response`, `Notification`, `Error`). -/
inductive MessageKind where
  /-- A request expecting a response (`JsonRpcMessage::Request`, line 778). -/
  | request
  /-- A response to a request (`JsonRpcMessage::Response`, line 780). -/
  | response
  /-- A one-way notification (`JsonRpcMessage::Notification`, line 782). -/
  | notification
  /-- An error response (`JsonRpcMessage::Error`, line 784). -/
  | error
  deriving DecidableEq, Repr

/-- The kind of a message: which of the four variants of `JsonRpcMessage` (lines 776–785) it
is. -/
def kind {Req Resp Noti : Type} : model.JsonRpcMessage Req Resp Noti → MessageKind
  | .Request _ => .request
  | .Response _ => .response
  | .Notification _ => .notification
  | .Error _ => .error

/-! ## The four message constructors -/

/-- The request message with payload `request` and id `id`: the value of the Rust constructor
`JsonRpcMessage::request(request, id)` (`model.rs` lines 789–795), whose `jsonrpc` field is the
unit struct `JsonRpcVersion2_0` (line 142; `Unit` in the translation). -/
def request {Req Resp Noti : Type} (request : Req) (id : model.NumberOrString) :
    model.JsonRpcMessage Req Resp Noti :=
  .Request { jsonrpc := (), id := id, request := request }

/-- The response message with result `response` and id `id`: the value of the Rust constructor
`JsonRpcMessage::response(response, id)` (`model.rs` lines 797–803). -/
def response {Req Resp Noti : Type} (response : Resp) (id : model.NumberOrString) :
    model.JsonRpcMessage Req Resp Noti :=
  .Response { jsonrpc := (), id := id, result := response }

/-- The error message with error data `error` and the optional id `id` (an error response may
have no id): the value of the Rust constructor `JsonRpcMessage::error(error, id)` (`model.rs`
lines 805–811). -/
def error {Req Resp Noti : Type} (error : model.ErrorData) (id : Option model.NumberOrString) :
    model.JsonRpcMessage Req Resp Noti :=
  .Error { jsonrpc := (), id := id, error := error }

/-- The notification message with payload `notification`: the value of the Rust constructor
`JsonRpcMessage::notification(notification)` (`model.rs` lines 813–818). -/
def notification {Req Resp Noti : Type} (notification : Noti) :
    model.JsonRpcMessage Req Resp Noti :=
  .Notification { jsonrpc := (), notification := notification }

/-! ## Request ids -/

/-- The integer that a request id written as a string denotes, if any: `none` for a numeric
id, and for a string id the value of its bytes under Rust's `i64::from_str` grammar
(`Defs.parseI64`). This is the meaning plan Section 16.1 gives M06
`NumberOrString::numeric_string_value` (`model.rs` lines 322–327: `Self::String(id) =>
id.parse().ok()`, `Self::Number(_) => None`). A string id is an `Arc<str>` (line 310), whose
model holds the string slice in its field `data` (`Rmcp.TypesExternal`); `.val` is its list of
UTF-8 bytes. -/
def numericValue : model.NumberOrString → Option Int
  | .Number _ => none
  | .String s => Defs.parseI64 s.data.val

end Defs.JsonRpc
