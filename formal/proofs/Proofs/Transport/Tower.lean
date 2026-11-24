/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Bytes
import Proofs.Defs.Tower
import Proofs.External.Option
import Proofs.External.String

/-!
# Spec theorems for the origin ports of `tower.rs` (T07, T08)

`default_port` maps the scheme `"http"` to `Some(80)`, `"https"` to `Some(443)` and every other
scheme to `None`, by exact byte equality. `AllowedPort::matches` accepts every port for `Any` and
`Unspecified`, and for `Exact(p)` compares `p` with the explicit port, or with the scheme's
default port when there is none.

Source: "crates/rmcp/src/transport/streamable_http_server/tower.rs", lines 1146 (T07) and 1164
(T08) at upstream `7caec76`.
-/

open Aeneas Aeneas.Std Result

namespace rmcp.transport.streamable_http_server.tower

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
  simp only [default_port, Str.Insts.CoreCmpPartialEqStr.eq_eq, Proofs.External.Utf8.toStr_val,
    Defs.Tower.defaultPort, Defs.Tower.http, Defs.Tower.https,
    Proofs.External.Utf8.utf8Bytes_eq_utf8, bind_tc_ok]
  have hne : ExtModel.utf8 "https" ≠ ExtModel.utf8 "http" := fun h =>
    absurd (Proofs.External.Utf8.utf8_injective h) (by decide)
  by_cases h₁ : scheme.val = ExtModel.utf8 "http"
  · simp only [h₁, decide_true, ↓reduceIte, WP.spec_ok]
  · by_cases h₂ : scheme.val = ExtModel.utf8 "https"
    · simp only [h₂, hne, decide_false, Bool.false_eq_true, ↓reduceIte, decide_true,
        WP.spec_ok]
    · simp only [h₁, decide_false, Bool.false_eq_true, ↓reduceIte, h₂, WP.spec_ok]

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
  match self with
  | .Any => simp only [AllowedPort.matches, WP.spec_ok]
  | .Unspecified => simp only [AllowedPort.matches, WP.spec_ok]
  | .Exact allowed =>
    have hor : core.option.Option.or_else
        AllowedPort.matches.closure.Insts.CoreOpsFunctionFnOnceTupleOptionU16 port scheme =
        ok (port <|> Defs.Tower.defaultPort scheme.val) := by
      cases port with
      | none =>
        obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (default_port_spec scheme)
        rw [core.option.Option.or_else_none]
        exact hr.trans (by rw [hp]; rfl)
      | some p => exact core.option.Option.or_else_some _ p scheme
    simp only [AllowedPort.matches, hor, bind_tc_ok]
    apply core.option.Option.Insts.CoreCmpPartialEqOption.eq_spec
    intro l r _ _
    simp only [liftFun2, core.cmp.impls.PartialEqU16.eq, WP.spec_ok, decide_eq_true_eq]

end rmcp.transport.streamable_http_server.tower
