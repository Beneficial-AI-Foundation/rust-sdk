/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Bytes
import Defs.Methods
import Defs.Tower

/-!
# Draft statements for the transport guards (T04–T08, C05)

Drafted by AI (Claude Code `mcp-spec`, model `claude-opus-5-5`) on 2026-11-24, plan step S24.
**spec: DRAFT.** Spec owner: Hoang Le Truong. None of these statements is signed off; each
needs at least two independent `mcp-review` runs and the spec owner's sign-off (plan Section 21).
The prover of a statement must not be its drafter (docs/WORKFLOW_AND_PR_GUIDE.md, "AI
contributions", rule 4).

Draft specification statements for the Phase 2 targets of
`crates/rmcp/src/transport/async_rw.rs` (T04 `without_carriage_return`, T05
`is_standard_notification`, T06 `is_standard_method`, and the composition theorem C05
`is_standard_method_of_is_standard_notification`) and of
`crates/rmcp/src/transport/streamable_http_server/tower.rs` (T07 `default_port`, T08
`AllowedPort::matches`). They are stated against the translated functions of `Rmcp.Funs`
(Aeneas `nightly-2026.08.20-5d08da4`; target `x86_64-unknown-linux-gnu`, `--no-default-features
--features <list>`, where `<list>` joins with commas the features `request-state`, `server`,
`client`, `client-side-sse`, `transport-streamable-http-server`,
`transport-streamable-http-client` and `auth`; plan Section 15) and use only `Defs.Methods`,
`Defs.Tower`, `Defs.utf8Bytes` (`Defs.Bytes`) and plain Lean. Line numbers refer to upstream
`7caec76`, unmodified (neither file is touched by patch 01).

**T05/T06 and the method lists (plan Section 21, H6 and H7, human decisions 2026-11-24).** The
independent lists are `Defs.Methods.standardRequests` and `Defs.Methods.standardNotifications`:
the core-protocol method names, the union of the method names of the five core MCP schemas the
SDK knows (H6). Names in no core schema (the Tasks-extension names `tasks/update` and
`notifications/tasks`, and `notifications/elicitation/response`, `model.rs` lines 3893–3900) are
out of scope by H6 and its amendment. The Rust lists lack six core-protocol names
(`Defs.Methods.codeOmits`: `tasks/get`, `tasks/result`, `tasks/cancel`, `tasks/list`,
`notifications/tasks/status`, `notifications/elicitation/complete`), so a statement
"`result = true ↔ name ∈ union`" is false on those six; the plan forbids bending a
specification to the code silently (Section 17, "T05/T06"). By H7 the statements below take the
code form "in the core list and not in `codeOmits`", with the six names listed one by one in
`Defs`, and the gap is recorded as a bug in `formal/docs/STATUS.md`, "Bugs found" (plan Section
22, "Bugs found"). Coverage claims for T05/T06 say "core protocol", never "full MCP" (H6).

Proof names follow plan Section 20: `<generated name>_spec`, restated later as
`Theorems.async_rw.<function>`, `Theorems.tower.default_port` and
`Theorems.tower.AllowedPort.matches`;
C05 is restated as `Theorems.async_rw.is_standard_method_of_is_standard_notification`.

This file is a draft: it lives in `formal/specs/Drafts/`, belongs to no library and is never
built by `lake build`. Each proof is a placeholder, allowed only here. A statement
`f x ⦃ (result : T) => P result ⦄` says that `f x` terminates without panicking and that its
result satisfies `P` (plan Section 3, "What a spec means"). Every postcondition determines the
result uniquely. No spec theorem (T04–T08) has a premise; the composition theorem C05 has one,
`h : is_standard_notification method = ok true`, which is the case it is about. The string
literals of T05–T08 compile to Aeneas `toStr` constants, whose native-code side conditions are
the accepted class (plan Section 18, H2); they appear in the `#print axioms` lists once proved,
not in the statements.
-/

open Aeneas Aeneas.Std Result

namespace rmcp.transport.async_rw

/-! ## T04: dropping one trailing carriage return (`async_rw.rs` lines 385–387) -/

/-- **Spec theorem for `rmcp::transport::async_rw::without_carriage_return`** (T04)

If the last byte of `s` is `\r` (`13`), the slice without that one byte; otherwise `s`
unchanged, including for the empty slice (plan Section 16.2, T04; `async_rw.rs` lines 385–387:
`s.strip_suffix(b"\r").unwrap_or(s)`). Only one `\r` is removed: `"a\r\r"` gives `"a\r"`
(plan Section 22). No premise. -/
@[step]
theorem without_carriage_return_spec (s : Slice U8) :
    without_carriage_return s ⦃ (result : Slice U8) =>
      result.val = if s.val.getLast? = some 13#u8 then s.val.dropLast else s.val ⦄ := by
  sorry

/-! ## T05, T06: MCP method allow-lists (`async_rw.rs` lines 392–433)

See the module docstring: the right-hand sides are the independent core-protocol lists of
`Defs.Methods` minus the names the code omits (`Defs.Methods.codeOmits`; code form by H7, the
gap recorded as a bug in `STATUS.md`, "Bugs found"; scope by H6 and its amendment). A name is
matched by exact, case-sensitive byte equality (`matches!` on `&str`, string equality
`PartialEq<str> for str`). -/

/-- **Spec theorem for `rmcp::transport::async_rw::is_standard_notification`** (T05)

`true` exactly when `method` is, byte for byte, one of the core-protocol MCP notification names
(the union of the five known core schemas, `Defs.Methods.standardNotifications`, H6) other than
those the code omits (`Defs.Methods.codeOmits`: `notifications/tasks/status`,
`notifications/elicitation/complete`; code form by H7, a recorded bug); `false` for every other
string, including a prefix or suffix of a name, a case variant, `notifications/unknown`, the
out-of-scope names `notifications/tasks` and `notifications/elicitation/response` (H6
amendment) and the empty string (plan Section 16.2, T05; Section 21, H6, H7; Section 22;
`async_rw.rs` lines 420–433, ten names). No premise. -/
@[step]
theorem is_standard_notification_spec (method : Str) :
    is_standard_notification method ⦃ (result : Bool) =>
      (result = true ↔
        ∃ n ∈ Defs.Methods.standardNotifications,
          n ∉ Defs.Methods.codeOmits ∧ method.val = Defs.utf8Bytes n) ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::transport::async_rw::is_standard_method`** (T06)

`true` exactly when `method` is, byte for byte, a core-protocol MCP request name (the union of
the five known core schemas, `Defs.Methods.standardRequests`, H6) other than those the code
omits (`tasks/get`, `tasks/result`, `tasks/cancel`, `tasks/list`; code form by H7, a recorded
bug), or a name T05 accepts; the out-of-scope name `tasks/update` (H6) gives `false` (plan
Section 16.2, T06: "`standardRequests` ∨ T05"; Section 21, H6, H7; `async_rw.rs` lines 392–417:
18 request names `|| is_standard_notification(method)`). No premise. -/
@[step]
theorem is_standard_method_spec (method : Str) :
    is_standard_method method ⦃ (result : Bool) =>
      (result = true ↔
        (∃ n ∈ Defs.Methods.standardRequests,
          n ∉ Defs.Methods.codeOmits ∧ method.val = Defs.utf8Bytes n) ∨
        (∃ n ∈ Defs.Methods.standardNotifications,
          n ∉ Defs.Methods.codeOmits ∧ method.val = Defs.utf8Bytes n)) ⦄ := by
  sorry

/-! ## Composition theorem C05 (plan Section 16.4) -/

/-- **C05 `is_standard_method_of_is_standard_notification`**: every method that
`is_standard_notification` accepts, `is_standard_method` accepts too; the allow-lists are
consistent (plan Section 16.4, C05; uses T05, T06; `async_rw.rs` line 417,
`|| is_standard_notification(method)`). About the translated functions
`is_standard_notification` and `is_standard_method`. It takes a successful call returning `true`
as its hypothesis, and covers only that case; T05 shows that the call never fails. Not tagged
`@[step]`. -/
theorem is_standard_method_of_is_standard_notification (method : Str)
    (h : is_standard_notification method = ok true) :
    is_standard_method method = ok true := by
  sorry

end rmcp.transport.async_rw

namespace rmcp.transport.streamable_http_server.tower

/-! ## T07, T08: origin ports (`tower.rs` lines 1146–1170) -/

/-- **Spec theorem for `rmcp::transport::streamable_http_server::tower::default_port`** (T07)

`some 80` for exactly `"http"`, `some 443` for exactly `"https"`, `none` for every other scheme,
by exact, case-sensitive byte equality, so `"HTTP"` and `"ftp"` give `none` (plan Section 16.2,
T07; Section 17, "T07/T08"; `Defs.Tower.defaultPort`; `tower.rs` lines 1145–1152: `"http" =>
Some(80)`, `"https" => Some(443)`, `_ => None`). Lowercasing the scheme is the callers'
obligation, not part of this theorem. No premise. -/
@[step]
theorem default_port_spec (scheme : Str) :
    default_port scheme ⦃ (result : Option U16) =>
      result = Defs.Tower.defaultPort scheme.val ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::transport::streamable_http_server::tower::AllowedPort::matches`**
(T08)

`Any` and `Unspecified` match every scheme and port. `Exact p` matches exactly when the
effective port is `p`: the explicit port if there is one (the scheme is then ignored), otherwise
the default port of the scheme (RFC 6454 §6.2 omits the default port when serializing an origin)
(plan Section 16.2, T08; Section 17, "T07/T08"; `tower.rs` lines 1164–1170:
`AllowedPort::Any | AllowedPort::Unspecified => true`, `AllowedPort::Exact(allowed) =>
port.or_else(|| default_port(scheme)) == Some(allowed)`). So `Exact 443` matches `https` with no
port, and `Exact 80` does not match `Some 8080` (plan Section 22). No premise. -/
@[step]
theorem AllowedPort.matches_spec (self : AllowedPort) (scheme : Str) (port : Option U16) :
    AllowedPort.matches self scheme port ⦃ (result : Bool) =>
      match self with
      | .Any => result = true
      | .Unspecified => result = true
      | .Exact allowed =>
        (result = true ↔ (port <|> Defs.Tower.defaultPort scheme.val) = some allowed) ⦄ := by
  sorry

end rmcp.transport.streamable_http_server.tower
