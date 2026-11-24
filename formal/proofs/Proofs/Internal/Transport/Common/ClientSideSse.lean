/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Defs
import Proofs.Transport.ClientSideSse

/-!
# Internal spec file for crates/rmcp/src/transport/common/client_side_sse.rs

These are guarantees about private functions (the methods of the private struct
`SseEventSizeLimiter`), kept out of `formal/specs/`, which holds only the public API (human
decision 2026-11-24). Index of all guarantees: `formal/specs/README.md`.

| ID | Function | Guarantee | Assumptions |
|---|---|---|---|
| T03 | `SseEventSizeLimiter::observe` | result and new state are those of (a) | none |
| T02 | `SseEventSizeLimiter::finish_line` | new state per `finishLine`; result: T01 on it | none |
| T01 | `SseEventSizeLimiter::check_limit` | `Err(())` iff `sat(retained + line) > max` | none |
| C01 | `observe` on `a ++ b` | = `observe` on `a`, then on `Ok` `observe` on `b` | none |
| C01 | `observe` on `a ++ b` (plan form) | = `observe` on `b` from the state after `a` | (b) |
| C02 | `observe` | bound `sat(retained + line) ≤ max` kept, `max` same | (c) |
| C02 | `observe` on prefix `a` (prefix form) | returns `Ok`, keeps `max` and the bound | (d) |

Rows about a call say that it does not panic and that its result satisfies the guarantee; "="
rows are equations between computations of the translated code. `sat` is addition saturating
at `usize::MAX`. (a) `Defs.Sse.observe`: a left fold of the limiter model `Defs.Sse.step` over
the chunk's bytes that stops at the first byte whose step fails the bound check (an LF completing
CR LF is not checked). (b) `observe` on `a` returned `Ok(())`.
(c) the bound holds before and this call returned `Ok(())`. (d) the bound holds before and
`observe` on `a ++ b` returned `Ok(())`. C01's general form also says that on `Err(())` the call
on `a ++ b` returns the same `Err(())` and state. The limit counts, per event, each completed
non-comment line's length + 1 and the current line's length; completed comment lines and the
blank line count 0 (`Defs.Sse`, "What is counted"; not the raw byte size). Used by:
`BoundedSseByteStream::poll_next` (through `bounded_sse_stream`), the event-size limit
(`max_sse_event_size`) of the reqwest streamable HTTP client
(`transport/common/reqwest/streamable_http_client.rs`, lines 205 and 482) and of the Unix-socket
one (`transport/common/unix_socket.rs`, lines 384 and 589); that wrapper is `async` and not
translated.

Statements of the SSE event-size limiter `SseEventSizeLimiter` (plan Section 16.2, T01–T03), in
Rust source order: T03 `observe` (line 48), T02 `finish_line` (line 75), T01 `check_limit`
(line 90), each restated as a theorem `Theorems.client_side_sse.SseEventSizeLimiter.<function>`
proved by the spec theorem in `Proofs/Transport/ClientSideSse.lean` and followed by the
assumptions its proof depends on, checked by `#print axioms` under `#guard_msgs`. Composition
theorems last (plan Section 16.4, proofs in the same file): C01
`SseEventSizeLimiter.observe_append` and its plan form
`SseEventSizeLimiter.observe_append_of_observe_eq_ok`; C02
`SseEventSizeLimiter.max_size_eq_and_satAdd_le_of_observe_eq_ok` and its prefix form
`SseEventSizeLimiter.exists_observe_eq_ok_and_max_size_eq_and_satAdd_le_of_observe_append_eq_ok`.

The statements were signed off by the spec owner Hoang Le Truong on 2026-11-24 after the S25
spec cycle ("S24/S25 spec cycle" in `formal/docs/STATUS.md`); their signed-off text was in
`specs/Drafts/ClientSideSse.lean`, removed at incorporation.

Translated configuration (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
`--no-default-features` with the features `request-state`, `server`, `client`, `client-side-sse`,
`transport-streamable-http-server`, `transport-streamable-http-client` and `auth` (the widened
feature list of plan Section 15, human decision H1), with `overflow-checks=true`
and `debug-assertions=true` (plan Section 1). Aeneas `nightly-2026.08.20-5d08da4`. Line numbers
refer to `client_side_sse.rs` at upstream `7caec76`, unmodified (the file is not touched by
patch 01). All arithmetic of these functions saturates (`usize::saturating_add`), so no
statement has a premise about overflow.

Definitions used: `Defs.Sse`, in module `Proofs.Defs.Sse` (`formal/proofs/Proofs/Defs/Sse.lean`;
the Lean names are unchanged): `ofLimiter`, `satAdd`, `withinLimit`, `toResult`, `finishLine`,
`observe`, and `step` only through `observe`; the regression-checked independent description
`historyOutcome` is not used by the statements. External models used: none beyond the Aeneas
library (`core.num` `saturating_add` and the slice iterator are part of it). Native-code
assumptions reached: none.

Not translated (plan Section 23: `async`/`Pin` is outside the Aeneas scope):
`SseEventSizeLimiter::new` (lines 38–46), `BoundedSseByteStream::poll_next` (lines 115–141)
and `bounded_sse_stream` (line 144); C01 and C02 are the contract a wrapper argument cites.
-/

open Aeneas Aeneas.Std Result
open rmcp.transport.common.client_side_sse  -- for `SseEventSizeLimiter`

/-! ## T03, T02, T01 (`client_side_sse.rs` lines 48–96), in Rust source order

The functions are named in full: inside a theorem `Theorems.client_side_sse.SseEventSizeLimiter.f`
a bare `observe` would refer to the restated theorem `Theorems.….observe`. -/

/-- T03 `observe`: the result and the final `self` are those of `Defs.Sse.observe`, the left
fold of `Defs.Sse.step` over the bytes of `chunk` that stops at the first failing byte. -/
theorem Theorems.client_side_sse.SseEventSizeLimiter.observe (self : SseEventSizeLimiter)
    (chunk : Slice U8) :
    rmcp.transport.common.client_side_sse.SseEventSizeLimiter.observe self chunk ⦃
      (result : core.result.Result Unit Unit × SseEventSizeLimiter) =>
      Defs.Sse.ofLimiter result.2 =
        (Defs.Sse.observe Usize.max (Defs.Sse.ofLimiter self) chunk.val).state ∧
      result.1 = Defs.Sse.toResult
        (Defs.Sse.observe Usize.max (Defs.Sse.ofLimiter self) chunk.val).ok ⦄ :=
  rmcp.transport.common.client_side_sse.SseEventSizeLimiter.observe_spec self chunk

/--
info: 'Theorems.client_side_sse.SseEventSizeLimiter.observe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.client_side_sse.SseEventSizeLimiter.observe

/-- T02 `finish_line`: the new `self` is `Defs.Sse.finishLine` of the old one, and the result is
T01's verdict on the new state. -/
theorem Theorems.client_side_sse.SseEventSizeLimiter.finish_line (self : SseEventSizeLimiter) :
    rmcp.transport.common.client_side_sse.SseEventSizeLimiter.finish_line self ⦃
      (result : core.result.Result Unit Unit × SseEventSizeLimiter) =>
      Defs.Sse.ofLimiter result.2 =
        (Defs.Sse.finishLine Usize.max (Defs.Sse.ofLimiter self)).state ∧
      result.1 =
        Defs.Sse.toResult (Defs.Sse.withinLimit Usize.max (Defs.Sse.ofLimiter result.2)) ⦄ :=
  rmcp.transport.common.client_side_sse.SseEventSizeLimiter.finish_line_spec self

/--
info: 'Theorems.client_side_sse.SseEventSizeLimiter.finish_line' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.client_side_sse.SseEventSizeLimiter.finish_line

/-- T01 `check_limit`: `Err(())` exactly when `sat(retained_size + line_size) > max_size`
(saturating at `usize::MAX`), `Ok(())` otherwise. -/
theorem Theorems.client_side_sse.SseEventSizeLimiter.check_limit (self : SseEventSizeLimiter) :
    rmcp.transport.common.client_side_sse.SseEventSizeLimiter.check_limit self ⦃
      (result : core.result.Result Unit Unit) =>
      result = Defs.Sse.toResult (Defs.Sse.withinLimit Usize.max (Defs.Sse.ofLimiter self)) ⦄ :=
  rmcp.transport.common.client_side_sse.SseEventSizeLimiter.check_limit_spec self

/--
info: 'Theorems.client_side_sse.SseEventSizeLimiter.check_limit' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.client_side_sse.SseEventSizeLimiter.check_limit

/-! ## Composition theorems C01, C02 (plan Section 16.4) -/

/-- **C01** (former plan name `sse_observe_append`), general form: `observe` on `a ++ b` is
`observe` on `a`, followed, on `Ok(())`, by `observe` on `b` from the state reached; on
`Err(())`, the call on `a ++ b` returns the same `Err(())` and state. No call is assumed to
succeed. -/
theorem Theorems.client_side_sse.SseEventSizeLimiter.observe_append (self : SseEventSizeLimiter)
    (a b ab : Slice U8)
    (h_ab : ab.val = a.val ++ b.val) :
    rmcp.transport.common.client_side_sse.SseEventSizeLimiter.observe self ab = (do
      let (r, s) ← rmcp.transport.common.client_side_sse.SseEventSizeLimiter.observe self a
      match r with
      | .Ok () => rmcp.transport.common.client_side_sse.SseEventSizeLimiter.observe s b
      | .Err () => ok (.Err (), s)) :=
  rmcp.transport.common.client_side_sse.SseEventSizeLimiter.observe_append self a b ab h_ab

/--
info: 'Theorems.client_side_sse.SseEventSizeLimiter.observe_append' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.client_side_sse.SseEventSizeLimiter.observe_append

/-- **C01** (former plan name `sse_observe_append`), plan form: if `observe` on `a` returns
`Ok(())` with state `self'`, then `observe` on `a ++ b` returns what `observe` on `b` from
`self'` returns. Covers only successful calls on `a`; it does not show that any call
succeeds. -/
theorem Theorems.client_side_sse.SseEventSizeLimiter.observe_append_of_observe_eq_ok
    (self self' : SseEventSizeLimiter) (a b ab : Slice U8)
    (h_ab : ab.val = a.val ++ b.val)
    (h_a : rmcp.transport.common.client_side_sse.SseEventSizeLimiter.observe self a =
      ok (.Ok (), self')) :
    rmcp.transport.common.client_side_sse.SseEventSizeLimiter.observe self ab =
      rmcp.transport.common.client_side_sse.SseEventSizeLimiter.observe self' b :=
  rmcp.transport.common.client_side_sse.SseEventSizeLimiter.observe_append_of_observe_eq_ok
    self self' a b ab h_ab h_a

/--
info: 'Theorems.client_side_sse.SseEventSizeLimiter.observe_append_of_observe_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.client_side_sse.SseEventSizeLimiter.observe_append_of_observe_eq_ok

/-- **C02** (former plan name `sse_observe_bound`): if the bound
`sat(retained_size + line_size) ≤ max_size` holds before an accepted chunk, it holds after it,
and `max_size` is unchanged. Covers only successful calls; it does not show that any call
succeeds. -/
theorem
    Theorems.client_side_sse.SseEventSizeLimiter.max_size_eq_and_satAdd_le_of_observe_eq_ok
    (self self' : SseEventSizeLimiter)
    (chunk : Slice U8)
    (h_bound :
      Defs.Sse.satAdd Usize.max self.retained_size.val self.line_size.val ≤ self.max_size.val)
    (h_ok : rmcp.transport.common.client_side_sse.SseEventSizeLimiter.observe self chunk =
      ok (.Ok (), self')) :
    self'.max_size = self.max_size ∧
    Defs.Sse.satAdd Usize.max self'.retained_size.val self'.line_size.val ≤
      self'.max_size.val :=
  rmcp.transport.common.client_side_sse.SseEventSizeLimiter.max_size_eq_and_satAdd_le_of_observe_eq_ok
    self self' chunk h_bound h_ok

/--
info: 'Theorems.client_side_sse.SseEventSizeLimiter.max_size_eq_and_satAdd_le_of_observe_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.client_side_sse.SseEventSizeLimiter.max_size_eq_and_satAdd_le_of_observe_eq_ok

/-- **C02, prefix form** (C02 and C01): if the bound holds for `self` and `observe` on `a ++ b`
returns `Ok(())`, then `observe` on the prefix `a` returns `Ok(())` with a state that keeps
`max_size` and the bound. Covers only successful calls on `a ++ b`. -/
theorem
    Theorems.client_side_sse.SseEventSizeLimiter.exists_observe_eq_ok_and_max_size_eq_and_satAdd_le_of_observe_append_eq_ok
    (self self'' : SseEventSizeLimiter) (a b ab : Slice U8)
    (h_ab : ab.val = a.val ++ b.val)
    (h_bound :
      Defs.Sse.satAdd Usize.max self.retained_size.val self.line_size.val ≤ self.max_size.val)
    (h_ok : rmcp.transport.common.client_side_sse.SseEventSizeLimiter.observe self ab =
      ok (.Ok (), self'')) :
    ∃ self', rmcp.transport.common.client_side_sse.SseEventSizeLimiter.observe self a =
        ok (.Ok (), self') ∧ self'.max_size = self.max_size ∧
      Defs.Sse.satAdd Usize.max self'.retained_size.val self'.line_size.val ≤
        self'.max_size.val :=
  rmcp.transport.common.client_side_sse.SseEventSizeLimiter.exists_observe_eq_ok_and_max_size_eq_and_satAdd_le_of_observe_append_eq_ok
    self self'' a b ab h_ab h_bound h_ok

/--
info: 'Theorems.client_side_sse.SseEventSizeLimiter.exists_observe_eq_ok_and_max_size_eq_and_satAdd_le_of_observe_append_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.client_side_sse.SseEventSizeLimiter.exists_observe_eq_ok_and_max_size_eq_and_satAdd_le_of_observe_append_eq_ok
