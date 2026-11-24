/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Net

/-!
# Draft statements for the SSRF address guard (A01–A03, C04)

Drafted by AI (Claude Code `mcp-spec`, model `claude-opus-5-5`) on 2026-11-24, plan step S25.
**spec: DRAFT.** Spec owner: Hoang Le Truong. None of these statements is signed off; each
needs at least two independent `mcp-review` runs and the spec owner's sign-off (plan Section 21).
The prover of a statement must not be its drafter (docs/WORKFLOW_AND_PR_GUIDE.md, "AI
contributions", rule 4).

Draft specification statements for the Phase 2 targets of `crates/rmcp/src/transport/auth.rs`: A02
`AuthorizationManager::is_disallowed_metadata_ipv4`, A01 `AuthorizationManager::embedded_ipv4`, A03
`AuthorizationManager::is_disallowed_metadata_ipv6` (in Rust source order), and the composition
theorem C04 (plan Section 16.4), named after its statement
`AuthorizationManager.is_disallowed_metadata_ipv6_eq_of_embedded_ipv4_eq_ok_some` (former plan
name `ipv6_embedding_no_bypass`), with its corollary
`AuthorizationManager.is_disallowed_metadata_ipv6_of_ipv4Disallowed`. They are stated against the
translated functions of `Rmcp.Funs` (Aeneas `nightly-2026.08.20-5d08da4`; target
`x86_64-unknown-linux-gnu`, `--no-default-features --features <list>`, where `<list>` joins with
commas the features `request-state`, `server`, `client`, `client-side-sse`,
`transport-streamable-http-server`, `transport-streamable-http-client` and `auth`; plan Section 15)
and use only `Defs.Net` and plain Lean. Line numbers refer to upstream `7caec76`, unmodified (the
file is not touched by patch 01). The callers `AddressClass::of`,
`MetadataAddressResolver::is_allowed` and `is_allowed_metadata_url` are not translated (plan Section
16.5, blockers B16, B7, B2; Section 23); A01–A03 are their lemmas once they are.

**The independent definitions** are those of `Defs.Net` (plan Section 17, "A01–A03"): an
address is a number (the big-endian value of its octets or segments, `Defs.Net.ipv4Value`,
`Defs.Net.ipv6Value`), a range is a prefix tested by `Defs.Net.inPrefix` on its leading bits, and
each range is taken from its RFC, not from the `std` predicates the code calls. The statements
read the inputs through the fields of the trusted `core::net` models (`Ipv4Addr.addrOctets`,
`Ipv6Addr.addrSegments`, `Rmcp.TypesExternal`), so each theorem rests on those models matching
`core::net` at the pinned nightly (plan Section 17; Section 18 and its amendment; the laws are
`Theorems.External.core.net.ip_addr.*` in `Specs/External.lean`).

**The address lists** (plan Section 21, human decision H8, 2026-11-24; Section 22, "Bugs
found"). The statements follow the plan's lists, which match the code, and describe the code in
every case:
- `64:ff9b:1::/48` (RFC 8215, local-use NAT64) is blocked outright, so an address in it that
  carries a public IPv4 address is refused (A03; `auth.rs` lines 1356–1358 and 1382): intended
  conservative behaviour, not a bug (H8 (1));
- `240.0.0.0/4` (reserved, except `255.255.255.255`) is not blocked: recorded as a bug in
  `formal/docs/STATUS.md`, "Bugs found" (H8 (2)); A02 states the code's behaviour;
- other special-purpose or deprecated ranges outside the plan's lists are neither blocked nor
  decoded: a scope note (H8 (3)); the examples are in the module docstring of `Defs.Net`,
  pinned by its checks.

Proof names follow plan Section 20: `<generated name>_spec`, restated later as
`Theorems.auth.AuthorizationManager.<function>`. The C04 theorems follow the Mathlib naming
convention (project rule, 2026-11-24): their names describe the statement, and the plan ID
is in the docstring.

This file is a draft: it lives in `formal/specs/Drafts/`, belongs to no library and is never
built by `lake build`. Each proof is a placeholder, allowed only here. A statement
`f x ⦃ (result : T) => P result ⦄` says that `f x` terminates without panicking and that its
result satisfies `P` (plan Section 3, "What a spec means"). Every postcondition determines the
result uniquely (A01 through the injectivity of `Defs.Net.ipv4Value` on four octets). No spec
theorem has a premise; the C04 theorem has one, the successful call it is about, and its
corollary has the form of the address as premises.
-/

open Aeneas Aeneas.Std Result

namespace rmcp.transport.auth.AuthorizationManager

/-! ## A02, A01, A03 (`auth.rs` lines 1343–1383), in Rust source order -/

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::is_disallowed_metadata_ipv4`**
(A02)

The call never fails. `true` exactly when the address is in one of `10/8`, `172.16/12`,
`192.168/16` (RFC 1918), `127/8`, `169.254/16` (RFC 3927), `255.255.255.255`, `0.0.0.0`,
`224/4`, `0/8`, `100.64/10` (RFC 6598) or `198.18/15` (RFC 2544), as prefixes of the 32-bit
value of its octets (`Defs.Net.ipv4Disallowed`, `Defs.Net.inPrefix`), not as the `std`
predicates (plan Section 16.3, A02; Section 17; `auth.rs` lines 1343–1354: `is_private`,
`is_loopback`, `is_link_local`, `is_broadcast`, `is_unspecified`, `is_multicast`,
`octets[0] == 0`, `100` with `64..=127`, `198` with `18 | 19`). `240.0.0.0/4` other than
`255.255.255.255` gives `false`, the code's behaviour (human decision H8: a recorded bug). No
premise. -/
@[step]
theorem is_disallowed_metadata_ipv4_spec (addr : core.net.ip_addr.Ipv4Addr) :
    is_disallowed_metadata_ipv4 addr ⦃ (result : Bool) =>
      result = Defs.Net.ipv4Disallowed (Defs.Net.ipv4Value addr.addrOctets.val) ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::embedded_ipv4`** (A01)

The call never fails. The value of the returned address is `Defs.Net.embeddedIpv4` of the value
of `addr`: over the segments `[a, b, c, d, e, f, g, h]`, IPv4-mapped `::ffff:0:0/96` (RFC 4291
§2.5.5.2) or NAT64 `64:ff9b::/96` (RFC 6052) give `some (g·2^16 + h)`; IPv4-compatible `::/96`
(RFC 4291 §2.5.5.1) except `::` and `::1` gives `some (g·2^16 + h)`; 6to4 `2002::/16` (RFC 3056)
gives `some (b·2^16 + c)`; everything else, including Teredo `2001::/32` and the local-use
NAT64 prefix `64:ff9b:1::/48`, gives `none` (plan Section 16.3, A01; Section 17; Section 22;
`auth.rs` lines 1356–1368). An `Ipv4Addr` is determined by the value of its four octets, so this
fixes the result. No premise. -/
@[step]
theorem embedded_ipv4_spec (addr : core.net.ip_addr.Ipv6Addr) :
    embedded_ipv4 addr ⦃ (result : Option core.net.ip_addr.Ipv4Addr) =>
      result.map (fun v4 => Defs.Net.ipv4Value v4.addrOctets.val) =
        Defs.Net.embeddedIpv4 (Defs.Net.ipv6Value addr.addrSegments.val) ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::is_disallowed_metadata_ipv6`**
(A03)

The call never fails. If `addr` carries an IPv4 address (A01, `Defs.Net.embeddedIpv4`), the
result is A02 on that address; otherwise `true` exactly when `addr` is `::1`, `::`, or in
`ff00::/8`, `fe80::/10`, `fc00::/7` (RFC 4193), `2001::/32` (Teredo, RFC 4380) or
`64:ff9b:1::/48` (RFC 8215; as a whole, human decision H8) (`Defs.Net.ipv6Disallowed`; plan
Section 16.3, A03; `auth.rs` lines
1370–1383: the early return of lines 1371–1373, then `is_loopback`, `is_unspecified`,
`is_multicast`, the masks `0xffc0`/`0xfe80` and `0xfe00`/`0xfc00`, `segments[..2] == [0x2001,
0]` and `segments[..3] == [0x64, 0xff9b, 1]`). No premise. -/
@[step]
theorem is_disallowed_metadata_ipv6_spec (addr : core.net.ip_addr.Ipv6Addr) :
    is_disallowed_metadata_ipv6 addr ⦃ (result : Bool) =>
      result = Defs.Net.ipv6Disallowed (Defs.Net.ipv6Value addr.addrSegments.val) ⦄ := by
  sorry

end rmcp.transport.auth.AuthorizationManager

namespace rmcp.transport.auth.AuthorizationManager

/-! ## Composition theorem C04 (plan Section 16.4) -/

/-- **C04** (former plan name `ipv6_embedding_no_bypass`): an IPv6 address that carries an IPv4
address `v` is blocked exactly when `v` is, so a blocked IPv4 address cannot pass the guard in
IPv4-mapped, IPv4-compatible, NAT64 or 6to4 form (plan Section 16.4, C04; uses A01–A03;
`auth.rs` lines 1371–1373, the early return). The plan-prescribed shape, which restates the
code's early return; `is_disallowed_metadata_ipv6_of_ipv4Disallowed` below states the guarantee
in terms of `Defs.Net`. About the translated functions `embedded_ipv4`,
`is_disallowed_metadata_ipv6` and `is_disallowed_metadata_ipv4`. It takes a successful call of
`embedded_ipv4` returning `some v` as its hypothesis and covers only that case (A01 shows that
the call never fails and when it returns `some`). Not tagged `@[step]`. -/
theorem is_disallowed_metadata_ipv6_eq_of_embedded_ipv4_eq_ok_some
    (addr : core.net.ip_addr.Ipv6Addr) (v : core.net.ip_addr.Ipv4Addr)
    (h : embedded_ipv4 addr = ok (some v)) :
    is_disallowed_metadata_ipv6 addr = is_disallowed_metadata_ipv4 v := by
  sorry

/-- **C04, corollary in `Defs.Net` terms**: no SSRF bypass through an embedded address. Let
`w` be a 32-bit address blocked by A02 (`Defs.Net.ipv4Disallowed w = true`, which implies
`w < 2^32`). Every IPv6 address that writes `w` in one of the four embedding forms is blocked:
IPv4-mapped `::ffff:w` (RFC 4291 §2.5.5.2), NAT64 `64:ff9b::w` (RFC 6052 §2.2), IPv4-compatible
`::w` (RFC 4291 §2.5.5.1), and 6to4 `2002:w::/48` with any value of the remaining 80 bits
(RFC 3056 §2, `w` in bits 16–47). The compatible form needs no `1 < w` premise: `::` and `::1`
carry no address (A01) but are blocked as unspecified and loopback (A03), and `0.0.0.0`,
`0.0.0.1` are blocked by `0/8` (A02). Plan Section 16.4, C04 ("No SSRF bypass by writing a
blocked IPv4 address in IPv4-mapped, compatible, NAT64 or 6to4 form"); uses A01–A03; `auth.rs`
lines 1343–1383. About the translated function `is_disallowed_metadata_ipv6`. No call is
assumed to succeed: the conclusion includes that the call terminates without panicking. Not
tagged `@[step]`. -/
theorem is_disallowed_metadata_ipv6_of_ipv4Disallowed (addr : core.net.ip_addr.Ipv6Addr)
    (w : Nat) (h_dis : Defs.Net.ipv4Disallowed w = true)
    (h_form :
      Defs.Net.ipv6Value addr.addrSegments.val = Defs.Net.ipv4Mapped.base + w ∨
      Defs.Net.ipv6Value addr.addrSegments.val = Defs.Net.nat64WellKnown.base + w ∨
      Defs.Net.ipv6Value addr.addrSegments.val = w ∨
      ∃ low < 2 ^ 80,
        Defs.Net.ipv6Value addr.addrSegments.val = Defs.Net.sixToFour.base + w * 2 ^ 80 + low) :
    is_disallowed_metadata_ipv6 addr ⦃ (result : Bool) => result = true ⦄ := by
  sorry

end rmcp.transport.auth.AuthorizationManager
