/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Defs
import Proofs.Transport.AsyncRw

/-!
# Spec file for crates/rmcp/src/transport/async_rw.rs

Statements of the line and method guards of the line codec (plan Section 16.2, T04–T06), in Rust
source order, each restated as a theorem `Theorems.async_rw.<function>` proved by the spec
theorem in `Proofs/Transport/AsyncRw.lean` and followed by the assumptions its proof depends on,
checked by `#print axioms` under `#guard_msgs`; the composition theorem C05 last (plan Section
16.4). The statements were signed off by the spec owner on 2026-11-24 (S24/S25 spec cycle,
`formal/docs/STATUS.md`); their signed-off text was in `specs/Drafts/Transport.lean`, removed at
incorporation.

Translated configuration (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
features `--no-default-features --features request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth`
(widened for Phase 2, plan Section 15, human decision H1), with `overflow-checks=true` and
`debug-assertions=true` (plan Section 1), so arithmetic overflow panics, which Aeneas models as
failure. Aeneas `nightly-2026.08.20-5d08da4`. `async_rw.rs` is upstream `7caec76`, unmodified
(not touched by patch 01); line numbers refer to it.

Definitions used: `Defs.Methods` (`standardRequests`, `standardNotifications`, `codeOmits`,
H6 and H7) and `Defs.utf8Bytes` (`Defs.Bytes`).

External models used (S26, `trusted/Rmcp/FunsExternal.lean`): T04 uses the models of
`core.slice.Slice.strip_suffix` (with `ExtModel.sliceEq`) and `core.option.Option.unwrap_or`;
T05, T06 and C05 use the model of `<str as PartialEq>::eq` (byte-list equality) and the bytes of
the Aeneas `toStr` literals (`ExtModel.utf8`).

Native-code assumptions: T04 reaches none. T05 reaches the ten `toStr` assumptions of the
notification literals of `is_standard_notification` (lines 423–432), T06 and C05 those and the
eighteen of the request literals of `is_standard_method` (lines 399–416), as the `#print axioms`
lists below show; they are the accepted class of plan Section 18 (human decision H2) and are
listed in `trusted/native-axioms.lock`.

Not translated (outside the Phase 2 scope, plan Section 13, "Not claimed"): every other item of
`async_rw.rs`, in particular the transport adapters, `AsyncRwTransport`,
`JsonRpcMessageCodec` and its `Decoder`/`Encoder` impls, `should_ignore_notification` and
`try_parse_with_compatibility`.

Statements here, in Rust source order: T04 (line 385), T06 (396), T05 (420); then C05.
-/

open Aeneas Aeneas.Std Result

/-- T04 `without_carriage_return`: drops exactly one trailing `\r` (byte `13`), if there is one;
otherwise returns the slice unchanged. -/
theorem Theorems.async_rw.without_carriage_return (s : Slice U8) :
    rmcp.transport.async_rw.without_carriage_return s ⦃ (result : Slice U8) =>
      result.val = if s.val.getLast? = some 13#u8 then s.val.dropLast else s.val ⦄ :=
  rmcp.transport.async_rw.without_carriage_return_spec s

/--
info: 'Theorems.async_rw.without_carriage_return' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.async_rw.without_carriage_return

/-- T06 `is_standard_method`: `true` exactly for the core-protocol request names and the
core-protocol notification names, other than those the code omits (`codeOmits`, H7). -/
theorem Theorems.async_rw.is_standard_method (method : Str) :
    rmcp.transport.async_rw.is_standard_method method ⦃ (result : Bool) =>
      (result = true ↔
        (∃ n ∈ Defs.Methods.standardRequests,
          n ∉ Defs.Methods.codeOmits ∧ method.val = Defs.utf8Bytes n) ∨
        (∃ n ∈ Defs.Methods.standardNotifications,
          n ∉ Defs.Methods.codeOmits ∧ method.val = Defs.utf8Bytes n)) ⦄ :=
  rmcp.transport.async_rw.is_standard_method_spec method

/--
info: 'Theorems.async_rw.is_standard_method' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_1,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_10,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_11,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_12,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_13,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_14,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_15,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_16,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_17,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_18,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_2,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_3,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_4,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_5,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_6,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_7,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_8,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_9,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_1,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_10,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_2,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_3,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_4,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_5,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_6,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_7,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_8,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_9]
-/
#guard_msgs in
#print axioms Theorems.async_rw.is_standard_method

/-- T05 `is_standard_notification`: `true` exactly for the core-protocol notification names
other than those the code omits (`codeOmits`, H7). -/
theorem Theorems.async_rw.is_standard_notification (method : Str) :
    rmcp.transport.async_rw.is_standard_notification method ⦃ (result : Bool) =>
      (result = true ↔
        ∃ n ∈ Defs.Methods.standardNotifications,
          n ∉ Defs.Methods.codeOmits ∧ method.val = Defs.utf8Bytes n) ⦄ :=
  rmcp.transport.async_rw.is_standard_notification_spec method

/--
info: 'Theorems.async_rw.is_standard_notification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_1,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_10,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_2,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_3,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_4,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_5,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_6,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_7,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_8,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_9]
-/
#guard_msgs in
#print axioms Theorems.async_rw.is_standard_notification

/-- C05 `is_standard_method_of_is_standard_notification`: a method that the translated
`is_standard_notification` accepts, the translated `is_standard_method` accepts too (line 417).
Covers only a successful call returning `true`; T05 shows that the call never fails. -/
theorem Theorems.async_rw.is_standard_method_of_is_standard_notification (method : Str)
    (h : rmcp.transport.async_rw.is_standard_notification method = ok true) :
    rmcp.transport.async_rw.is_standard_method method = ok true :=
  rmcp.transport.async_rw.is_standard_method_of_is_standard_notification method h

/--
info: 'Theorems.async_rw.is_standard_method_of_is_standard_notification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_1,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_10,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_11,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_12,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_13,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_14,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_15,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_16,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_17,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_18,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_2,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_3,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_4,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_5,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_6,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_7,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_8,
 rmcp.transport.async_rw.is_standard_method._native.decide.ax_9,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_1,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_10,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_2,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_3,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_4,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_5,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_6,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_7,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_8,
 rmcp.transport.async_rw.is_standard_notification._native.decide.ax_9]
-/
#guard_msgs in
#print axioms Theorems.async_rw.is_standard_method_of_is_standard_notification
