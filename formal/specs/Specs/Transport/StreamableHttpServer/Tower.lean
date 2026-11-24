/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Defs
import Proofs.Transport.Tower

/-!
# Spec file for crates/rmcp/src/transport/streamable_http_server/tower.rs

Statements of the origin-port policy of the DNS-rebinding protection (plan Section 16.2, T07,
T08), in Rust source order, each restated as a theorem `Theorems.tower.<function>` (with
`AllowedPort.` for the method) proved by the spec theorem in `Proofs/Transport/Tower.lean` and
followed by the assumptions its proof depends on, checked by `#print axioms` under
`#guard_msgs`. The statements were signed off by the spec owner on 2026-11-24 (S24/S25 spec
cycle, `formal/docs/STATUS.md`); their signed-off text was in `specs/Drafts/Transport.lean`,
removed at incorporation.

Translated configuration (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
features `--no-default-features --features request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth`
(widened for Phase 2, plan Section 15, human decision H1), with `overflow-checks=true` and
`debug-assertions=true` (plan Section 1), so arithmetic overflow panics, which Aeneas models as
failure. Aeneas `nightly-2026.08.20-5d08da4`. `tower.rs` is upstream `7caec76`, unmodified (not
touched by patch 01); line numbers refer to it.

Definitions used: `Defs.Tower` (`defaultPort`, `http`, `https`).

External models used (S26, `trusted/Rmcp/FunsExternal.lean`): the model of
`<str as PartialEq>::eq` (byte-list equality) and the bytes of the Aeneas `toStr` literals
(`ExtModel.utf8`); T08 also the models of `core.option.Option.or_else` and of `PartialEq` on
`Option<u16>`.

Native-code assumptions: T07 and T08 reach the two `toStr` assumptions of the scheme literals
`"http"` and `"https"` of `default_port` (lines 1148–1149), as the `#print axioms` lists below
show; they are the accepted class of plan Section 18 (human decision H2) and are listed in
`trusted/native-axioms.lock`.

Not translated (outside the Phase 2 scope, plan Section 13, "Not claimed"): every other item of
`tower.rs`, in particular `origin_is_allowed`, `host_is_allowed`, the parsing of allowed origins
and hosts, and the `StreamableHttpService` itself.

Statements here, in Rust source order: T07 (line 1146), T08 (1164).
-/

open Aeneas Aeneas.Std Result

/-- T07 `default_port`: `some 80` for exactly `"http"`, `some 443` for exactly `"https"`, `none`
otherwise, by exact, case-sensitive byte equality. -/
theorem Theorems.tower.default_port (scheme : Str) :
    rmcp.transport.streamable_http_server.tower.default_port scheme ⦃ (result : Option U16) =>
      result = Defs.Tower.defaultPort scheme.val ⦄ :=
  rmcp.transport.streamable_http_server.tower.default_port_spec scheme

/--
info: 'Theorems.tower.default_port' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rmcp.transport.streamable_http_server.tower.default_port._native.decide.ax_1,
 rmcp.transport.streamable_http_server.tower.default_port._native.decide.ax_2]
-/
#guard_msgs in
#print axioms Theorems.tower.default_port

/-- T08 `AllowedPort::matches`: `Any` and `Unspecified` match everything; `Exact p` matches
exactly when the explicit port, or else the scheme's default port, is `p`. -/
theorem Theorems.tower.AllowedPort.matches
    (self : rmcp.transport.streamable_http_server.tower.AllowedPort) (scheme : Str)
    (port : Option U16) :
    rmcp.transport.streamable_http_server.tower.AllowedPort.matches self scheme port ⦃
      (result : Bool) =>
      match self with
      | .Any => result = true
      | .Unspecified => result = true
      | .Exact allowed =>
        (result = true ↔ (port <|> Defs.Tower.defaultPort scheme.val) = some allowed) ⦄ :=
  rmcp.transport.streamable_http_server.tower.AllowedPort.matches_spec self scheme port

/--
info: 'Theorems.tower.AllowedPort.matches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rmcp.transport.streamable_http_server.tower.default_port._native.decide.ax_1,
 rmcp.transport.streamable_http_server.tower.default_port._native.decide.ax_2]
-/
#guard_msgs in
#print axioms Theorems.tower.AllowedPort.matches
