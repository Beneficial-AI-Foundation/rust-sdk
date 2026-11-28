/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Defs
public import Proofs.Transport.Tower

@[expose] public section

/-!
# Internal spec file for crates/rmcp/src/transport/streamable_http_server/tower.rs

These are guarantees about private functions (`default_port` and the method of the private enum
`AllowedPort`), kept out of `formal/specs/`, which holds only the public API (human decision
2026-11-24). Index of all guarantees: `formal/specs/README.md`.

| ID | Function | Guarantee | Assumptions |
|---|---|---|---|
| T07 | `default_port` | `"http"`: `Some(80)`; `"https"`: `Some(443)`; else `None` | none |
| T08 | `AllowedPort::matches` | `Any`, `Unspecified`: `true`; `Exact(p)`: (a) | none |

Each row says that the call does not panic and that its result satisfies the guarantee. Schemes
are compared byte for byte (case-sensitive). (a) `true` iff the explicit port, or else T07's
default port of the scheme, is `p`. Used by: `origin_is_allowed`, the `Origin` check of the
DNS-rebinding protection of `StreamableHttpService` (`allowed_origins` of
`StreamableHttpServerConfig`); the caller and the origin parsing are not translated.

Statements of the origin-port policy of the DNS-rebinding protection (plan Section 16.2, T07,
T08), in Rust source order, each restated as a theorem `Theorems.tower.<function>` (with
`AllowedPort.` for the method) proved by the spec theorem in `Proofs/Transport/Tower.lean` and
followed by the assumptions its proof depends on, checked by `#print axioms` under
`#guard_msgs`. The statements were signed off by the spec owner on 2026-11-24 (S24/S25 spec
cycle, `STATUS.md` at 9047c72); their signed-off statements are the ones in this project file.

Translated configuration (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
`--no-default-features` with the features `request-state`, `server`, `client`, `client-side-sse`,
`transport-streamable-http-server`, `transport-streamable-http-client` and `auth` (widened for
Phase 2, plan Section 15, human decision H1), with `overflow-checks=true` and
`debug-assertions=true` (plan Section 1), so arithmetic overflow panics, which Aeneas models as
failure. Aeneas `nightly-2026.11.24-fb44cb4` (until 2026-11-24 `nightly-2026.08.20-5d08da4`).
`tower.rs` is upstream `7caec76`, unmodified (not
touched by patch 01); line numbers refer to it.

Definitions used: `Defs.Tower`, in module `Proofs.Defs.Tower`
(`formal/proofs/Proofs/Defs/Tower.lean`; the Lean names are unchanged): `defaultPort`, `http`,
`https`.

External models used (S26, `trusted/Rmcp/FunsExternal.lean`): the model of
`<str as PartialEq>::eq` (byte-list equality) and the bytes of the Aeneas `toStr` literals
(`ExtModel.utf8`); T08 also the models of `core.option.Option.or_else` and of `PartialEq` on
`Option<u16>`.

Native-code assumptions: none since the Aeneas upgrade of 2026-11-24, whose `toStr` checks the
length of a literal in the kernel (`trusted/native-axioms.lock` is empty). Until then T07 and T08
reached the two `toStr` assumptions of the scheme literals `"http"` and `"https"` of
`default_port` (lines 1148–1149), the accepted class of plan Section 18 (human decision H2).
Both `#print axioms` lists below changed in that upgrade (native-code assumptions dropped),
re-signed by the spec owner in the batch of 2026-11-24.

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
info: 'Theorems.tower.default_port' depends on axioms: [propext, Classical.choice, Quot.sound]
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
info: 'Theorems.tower.AllowedPort.matches' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.tower.AllowedPort.matches
