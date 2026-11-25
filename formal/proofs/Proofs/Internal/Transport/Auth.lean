/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Defs
public import Proofs.Transport.Auth

@[expose] public section

/-!
# Internal spec file for crates/rmcp/src/transport/auth.rs (Phase 2: A01–A03, C04)

These are guarantees about private functions (associated functions of `AuthorizationManager`
without `pub`), kept out of `formal/specs/`, which holds only the public API (human decision
2026-11-24). Index of all guarantees: `formal/specs/README.md`.

| ID | Function | Guarantee | Assumptions |
|---|---|---|---|
| A02 | `is_disallowed_metadata_ipv4` | `true` iff in a blocked IPv4 range (a) | none |
| A01 | `embedded_ipv4` | `Some` of the IPv4 address carried in a form (b), else `None` | none |
| A03 | `is_disallowed_metadata_ipv6` | A02 on a carried IPv4 address, else (c) | none |
| C04 | A01, A03, A02 | A01 gives `Some(v)` ⇒ A03 on the address = A02 on `v` | (d) |
| C04 | A03 (corollary) | a blocked IPv4 address in form (b) is blocked | (e) |

Rows A01–A03 and the corollary say that the call does not panic and that its result satisfies
the guarantee; the C04 row is an equation between computations of the translated code. The
functions are methods of `AuthorizationManager`. (a) `10/8`, `172.16/12`, `192.168/16`,
`127/8`, `169.254/16`, `255.255.255.255`, `0.0.0.0`, `224/4`, `0/8`, `100.64/10`, `198.18/15`
(`Defs.Net.ipv4Disallowed`); `240.0.0.0/4` is not blocked (recorded bug, human decision H8;
`formal/docs/STATUS.md`, "Bugs found"). (b) IPv4-mapped `::ffff:0:0/96`, NAT64 `64:ff9b::/96`,
IPv4-compatible `::/96` except `::` and `::1`, or 6to4 `2002::/16` (`Defs.Net.embeddedIpv4`).
(c) `true` iff `::1`, `::`, `ff00::/8`, `fe80::/10`, `fc00::/7`, `2001::/32` or `64:ff9b:1::/48`
(`Defs.Net.ipv6Disallowed`). (d) the call of `embedded_ipv4` returned `Some(v)`. (e) the address
writes an IPv4 address that `Defs.Net.ipv4Disallowed` blocks in one of the forms (b). Used by:
`is_allowed_metadata_url` (through `is_disallowed_metadata_host`), the SSRF check of the OAuth
metadata URLs during `AuthorizationManager` discovery, and `AddressClass::of` in
`auth/metadata_resolver.rs`, the filter of resolved addresses; these callers are not translated.

The statements of the SSRF address guard of `AuthorizationManager` (plan Section 16.3), in Rust
source order, each restated as a theorem `Theorems.auth.AuthorizationManager.<function>` proved
by the spec theorem in `Proofs/Transport/Auth.lean` and followed by the assumptions its proof
depends on, checked by `#print axioms` under `#guard_msgs`; then the composition theorem C04
(plan Section 16.4) and its corollary. Signed off by the spec owner on 2026-11-24 (S24/S25 spec
cycle, `formal/docs/STATUS.md`); the signed-off text was in `specs/Drafts/Auth.lean`, removed at
incorporation.

Translated configuration (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
`--no-default-features` with the features `request-state`, `server`, `client`, `client-side-sse`,
`transport-streamable-http-server`, `transport-streamable-http-client` and `auth` (widened for
Phase 2, plan Section 15), with `overflow-checks=true` and `debug-assertions=true` (plan
Section 1). Aeneas `nightly-2026.11.24-fb44cb4` (until 2026-11-24 `nightly-2026.08.20-5d08da4`).
Line numbers refer to upstream `7caec76` (the file is not touched by patch 01).

Definitions used: `Defs.Net`, in module `Proofs.Defs.Net` (`formal/proofs/Proofs/Defs/Net.lean`;
the Lean names are unchanged): `ipv4Value`, `ipv6Value`, `ipv4Disallowed`, `embeddedIpv4`,
`ipv6Disallowed`, `ipv4Mapped`, `nat64WellKnown`, `sixToFour`; the ranges are RFC prefixes tested
by `inPrefix`, not the `std` predicates the code calls.

External models used (S26/S27, `trusted/Rmcp/{Types,Funs}External.lean`, sections "Phase 2"):
`core.net.ip_addr.Ipv4Addr` (`addrOctets`, `octets`, `is_private`, `is_loopback`,
`is_link_local`, `is_broadcast`, `is_unspecified`, `is_multicast`, `From<u32>`),
`core.net.ip_addr.Ipv6Addr` (`addrSegments`, `segments`, `is_loopback`, `is_unspecified`,
`is_multicast`), `RangeInclusive::contains` on `u8`, and, for A03 (`segments[..2] == [0x2001,
0]`, `segments[..3] == [0x64, 0xff9b, 1]`), `<[T] as PartialEq<[U; N]>>::eq`
(`Slice.Insts.CoreCmpPartialEqArray.eq`, `FunsExternal.lean` line 861, on
`ExtModel.sliceEqSameLength`); their laws are `Theorems.External.core.net.ip_addr.*`,
`Theorems.External.core.ops.range.RangeInclusive.*` and
`Theorems.External.Slice.Insts.CoreCmpPartialEqArray.eq_spec` and `eq_u16_spec` in
`Proofs/Internal/External.lean`. Each statement rests on these models matching `core::net` and
`core` at the pinned nightly (plan Section 17; Section 18). From the Aeneas library (definitions,
not trusted models): `core::convert::From<u16> for u32` (`core.convert.num.FromU32U16.from`,
`Aeneas/Std/Scalar/CoreConvertNum.lean` line 74) and `RangeInclusive::new`.
Native-code assumptions reached: none.

Statements here, in Rust source order: A02 `is_disallowed_metadata_ipv4` (line 1343), A01
`embedded_ipv4` (line 1359), A03 `is_disallowed_metadata_ipv6` (line 1370); then C04
`is_disallowed_metadata_ipv6_eq_of_embedded_ipv4_eq_ok_some` and its corollary
`is_disallowed_metadata_ipv6_of_ipv4Disallowed`. A02 states the code's behaviour on
`240.0.0.0/4`, a recorded bug (human decision H8; `formal/docs/STATUS.md`, "Bugs found"). The
other items of `auth.rs` are not Phase 2 targets; the callers `AddressClass::of`,
`MetadataAddressResolver::is_allowed` and `is_allowed_metadata_url` are not translated (plan
Section 16.5, blockers B16, B7, B2).
-/

open Aeneas Aeneas.Std Result

/-- A02 `is_disallowed_metadata_ipv4`: never fails; `true` exactly when the address is in one of
the blocked IPv4 ranges of `Defs.Net.ipv4Disallowed` (the code's behaviour: `240.0.0.0/4` is not
blocked). -/
theorem Theorems.auth.AuthorizationManager.is_disallowed_metadata_ipv4
    (addr : core.net.ip_addr.Ipv4Addr) :
    rmcp.transport.auth.AuthorizationManager.is_disallowed_metadata_ipv4 addr
      ⦃ (result : Bool) =>
      result = Defs.Net.ipv4Disallowed (Defs.Net.ipv4Value addr.addrOctets.val) ⦄ :=
  rmcp.transport.auth.AuthorizationManager.is_disallowed_metadata_ipv4_spec addr

/--
info: 'Theorems.auth.AuthorizationManager.is_disallowed_metadata_ipv4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_disallowed_metadata_ipv4

/-- A01 `embedded_ipv4`: never fails; the value of the returned address is
`Defs.Net.embeddedIpv4` of the value of `addr` (mapped, NAT64, compatible or 6to4 form). -/
theorem Theorems.auth.AuthorizationManager.embedded_ipv4 (addr : core.net.ip_addr.Ipv6Addr) :
    rmcp.transport.auth.AuthorizationManager.embedded_ipv4 addr
      ⦃ (result : Option core.net.ip_addr.Ipv4Addr) =>
      result.map (fun v4 => Defs.Net.ipv4Value v4.addrOctets.val) =
        Defs.Net.embeddedIpv4 (Defs.Net.ipv6Value addr.addrSegments.val) ⦄ :=
  rmcp.transport.auth.AuthorizationManager.embedded_ipv4_spec addr

/--
info: 'Theorems.auth.AuthorizationManager.embedded_ipv4' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.embedded_ipv4

/-- A03 `is_disallowed_metadata_ipv6`: never fails; the result is `Defs.Net.ipv6Disallowed` of
the value of `addr` (A02 on a carried IPv4 address, otherwise the IPv6 ranges). -/
theorem Theorems.auth.AuthorizationManager.is_disallowed_metadata_ipv6
    (addr : core.net.ip_addr.Ipv6Addr) :
    rmcp.transport.auth.AuthorizationManager.is_disallowed_metadata_ipv6 addr
      ⦃ (result : Bool) =>
      result = Defs.Net.ipv6Disallowed (Defs.Net.ipv6Value addr.addrSegments.val) ⦄ :=
  rmcp.transport.auth.AuthorizationManager.is_disallowed_metadata_ipv6_spec addr

/--
info: 'Theorems.auth.AuthorizationManager.is_disallowed_metadata_ipv6' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_disallowed_metadata_ipv6

/-! ## Composition theorem C04 (plan Section 16.4) -/

/-- C04 (former plan name `ipv6_embedding_no_bypass`): if `embedded_ipv4 addr` returns `some v`,
then `is_disallowed_metadata_ipv6 addr` is `is_disallowed_metadata_ipv4 v`. Covers only a
successful call of `embedded_ipv4` returning `some v`; does not show that any call succeeds. -/
theorem Theorems.auth.AuthorizationManager.is_disallowed_metadata_ipv6_eq_of_embedded_ipv4_eq_ok_some
    (addr : core.net.ip_addr.Ipv6Addr) (v : core.net.ip_addr.Ipv4Addr)
    (h : rmcp.transport.auth.AuthorizationManager.embedded_ipv4 addr = ok (some v)) :
    rmcp.transport.auth.AuthorizationManager.is_disallowed_metadata_ipv6 addr =
      rmcp.transport.auth.AuthorizationManager.is_disallowed_metadata_ipv4 v :=
  rmcp.transport.auth.AuthorizationManager.is_disallowed_metadata_ipv6_eq_of_embedded_ipv4_eq_ok_some
    addr v h

/--
info: 'Theorems.auth.AuthorizationManager.is_disallowed_metadata_ipv6_eq_of_embedded_ipv4_eq_ok_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_disallowed_metadata_ipv6_eq_of_embedded_ipv4_eq_ok_some

/-- C04, corollary in `Defs.Net` terms: an IPv6 address writing a blocked IPv4 address `w` in
IPv4-mapped, NAT64, IPv4-compatible or 6to4 form is blocked; the call terminates without
panicking. -/
theorem Theorems.auth.AuthorizationManager.is_disallowed_metadata_ipv6_of_ipv4Disallowed
    (addr : core.net.ip_addr.Ipv6Addr) (w : Nat) (h_dis : Defs.Net.ipv4Disallowed w = true)
    (h_form :
      Defs.Net.ipv6Value addr.addrSegments.val = Defs.Net.ipv4Mapped.base + w ∨
      Defs.Net.ipv6Value addr.addrSegments.val = Defs.Net.nat64WellKnown.base + w ∨
      Defs.Net.ipv6Value addr.addrSegments.val = w ∨
      ∃ low < 2 ^ 80,
        Defs.Net.ipv6Value addr.addrSegments.val = Defs.Net.sixToFour.base + w * 2 ^ 80 + low) :
    rmcp.transport.auth.AuthorizationManager.is_disallowed_metadata_ipv6 addr
      ⦃ (result : Bool) => result = true ⦄ :=
  rmcp.transport.auth.AuthorizationManager.is_disallowed_metadata_ipv6_of_ipv4Disallowed addr w
    h_dis h_form

/--
info: 'Theorems.auth.AuthorizationManager.is_disallowed_metadata_ipv6_of_ipv4Disallowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_disallowed_metadata_ipv6_of_ipv4Disallowed
