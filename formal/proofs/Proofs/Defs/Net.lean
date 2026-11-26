/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Aeneas
public import Rmcp.Types

@[expose] public section

/-!
# Definitions for the SSRF address-guard statements (A01–A03, C04)

IP addresses as numbers, address prefixes, and the address classes of the plan's A01–A03
specifications (Section 16.3; Section 17, "A01–A03 (addresses)"), written from the RFCs that
define each range and not from the `std` predicates or the translated code.

**Addresses and prefixes.** An IPv4 address is the 32-bit number whose big-endian base-256
digits are its four octets (RFC 791; RFC 4632 §3.1 for the dotted prefix notation); an
IPv6 address is the 128-bit number whose big-endian base-65536 digits are its eight 16-bit
pieces, the segments of the text form `x:x:x:x:x:x:x:x` (RFC 4291 §2.2). A prefix `base/len`
of a `width`-bit address space contains an address exactly when the leading `len` bits of the
address equal those of `base` (RFC 4291 §2.3; RFC 4632 §3.1), that is when both have the same
quotient by `2^(width - len)`.

**Ranges** (plan Section 16.3). IPv4 (A02): `10/8`, `172.16/12`, `192.168/16` (RFC 1918 §3),
`127/8` (RFC 1122 §3.2.1.3 (g)), `169.254/16` (RFC 3927 §1, §2.1), `255.255.255.255`
(RFC 919; RFC 1122 §3.2.1.3 (c)), `0.0.0.0` (RFC 1122 §3.2.1.3 (a)), `224/4` (RFC 1112 §4;
RFC 5771), `0/8` (RFC 1122 §3.2.1.3 (a), (b); RFC 6890 §2.2.2), `100.64/10` (RFC 6598 §7),
`198.18/15` (RFC 2544 Appendix C.2.2; RFC 6890 §2.2.2). IPv6 (A01, A03): `::1` (RFC 4291
§2.5.3), `::` (§2.5.2), `ff00::/8` (§2.7), `fe80::/10` (§2.5.6), `fc00::/7` (RFC 4193 §3.1),
`2001::/32` (Teredo, RFC 4380 §2.6), `64:ff9b:1::/48` (local-use NAT64, RFC 8215), and the
four forms that carry an IPv4 address: IPv4-mapped `::ffff:0:0/96` (RFC 4291 §2.5.5.2), NAT64
well-known prefix `64:ff9b::/96` (RFC 6052 §2.1, address in the last 32 bits for a /96
prefix, §2.2), IPv4-compatible `::/96` (RFC 4291 §2.5.5.1, deprecated), 6to4 `2002::/16`
(RFC 3056 §2: the prefix `2002:V4ADDR::/48`, the IPv4 address in bits 16–47).

**What the lists leave out** (plan Section 21, human decision H8, 2026-11-24; Section 22,
"Bugs found"). The plan's lists, which these definitions follow, are the scope; they are not
the IANA special-purpose address registries (RFC 6890 and its updates; registry versions read
on 2026-11-24). Under H8:
- `64:ff9b:1::/48` (RFC 8215) is blocked outright, whatever IPv4 address it carries, including
  a public one: intended conservative behaviour, not a bug (plan Section 16.3, A03).
- `240.0.0.0/4` other than `255.255.255.255` (reserved, RFC 1112 §4; RFC 6890 §2.2.2) is not in
  the plan's A02 list and not blocked by the code: recorded as a bug (`formal/docs/STATUS.md`,
  "Bugs found"). `ipv4Disallowed` follows the plan and the code here.
- Other special-purpose or deprecated ranges outside the lists are a scope note. Not blocked by
  `ipv4Disallowed`, for example: `192.0.0.0/24` (IETF protocol assignments, RFC 6890 §2.2.2),
  `192.0.2.0/24`, `198.51.100.0/24`, `203.0.113.0/24` (documentation, RFC 5737 §3),
  `192.88.99.0/24` (6to4 relay anycast, deprecated by RFC 7526), `192.31.196.0/24` (AS112-v4,
  RFC 7535), `192.52.193.0/24` (AMT, RFC 7450), `192.175.48.0/24` (direct delegation AS112
  service, RFC 7534). Not blocked by `ipv6Disallowed` and carrying no embedded address, for
  example: `::ffff:0:0:0/96` (IPv4-translated, RFC 2765 §2.1, obsoleted by RFC 6145; not in
  the IANA registry), `100::/64` (discard-only, RFC 6666), `2001:1::1/128`, `2001:1::2/128`,
  `2001:1::3/128` (anycast addresses, RFC 7723, RFC 8155, RFC 9665), `2001:2::/48`
  (benchmarking, RFC 5180), `2001:3::/32` (AMT, RFC 7450), `2001:4:112::/48` (AS112-v6,
  RFC 7535), `2001:10::/28` and `2001:20::/28` (ORCHID, RFC 4843, RFC 7343), `2001:db8::/32`
  (documentation, RFC 3849), `2620:4f:8000::/48` (direct delegation AS112 service, RFC 7534),
  `3fff::/20` (documentation, RFC 9637), `5f00::/16` (SRv6 SIDs, RFC 9602), `fec0::/10`
  (site-local, deprecated by RFC 3879).
The regression checks at the end of the file pin these facts, so a change of the lists is
visible.

Rust source of the code these definitions are compared with: `crates/rmcp/src/transport/auth.rs`
at upstream `7caec76`, unmodified (plan Section 13): `is_disallowed_metadata_ipv4` lines
1343–1354, `embedded_ipv4` 1356–1368, `is_disallowed_metadata_ipv6` 1370–1383. Everything lives
in the namespace `Defs.Net`. Not imported from the `Defs` root until sign-off.

**Equality of addresses.** The section "Decidable equality of addresses" gives the decidable
equality of the translated types `Ipv4Addr`, `Ipv6Addr` and `IpAddr` (the derived `PartialEq` of
`ip_addr.rs`), shared by every statement that compares IP addresses; it is decided on the octet
and segment lists, so the kernel evaluates it on literals (`decide +kernel`). That section
(added 2026-11-26 in spec round 2 of `metadata_resolver.rs`, accepted by the spec owner of
A01–A03) is the only reason this file imports `Rmcp.Types`: it uses the translated types only to
state the instances; the other definitions are still written from the RFCs alone.
-/

namespace Defs.Net

open Aeneas.Std

/-- The number whose big-endian digits in base `radix` are `ds`, most significant first. -/
def ofBigEndianDigits (radix : Nat) (ds : List Nat) : Nat :=
  ds.foldl (fun acc d => acc * radix + d) 0

/-- **The 32-bit value of an IPv4 address** given by its octets, most significant first
(RFC 791; for four octets it is below `2^32`). -/
def ipv4Value (octets : List U8) : Nat :=
  ofBigEndianDigits 256 (octets.map (fun o => o.val))

/-- **The 128-bit value of an IPv6 address** given by its eight 16-bit segments, most
significant first (RFC 4291 §2.2; for eight segments it is below `2^128`). -/
def ipv6Value (segments : List U16) : Nat :=
  ofBigEndianDigits 65536 (segments.map (fun s => s.val))

/-- **An address prefix** `base/len` in a `width`-bit address space (RFC 4291 §2.3; RFC 4632
§3.1). Only the leading `len` bits of `base` matter. -/
structure Prefix where
  width : Nat
  base : Nat
  len : Nat
  deriving DecidableEq, Repr

/-- **Prefix membership**: the leading `p.len` bits of the `p.width`-bit address `v` equal those
of `p.base`, i.e. both have the same quotient by `2^(width - len)` (RFC 4291 §2.3; RFC 4632
§3.1). -/
def inPrefix (p : Prefix) (v : Nat) : Bool :=
  v / 2 ^ (p.width - p.len) == p.base / 2 ^ (p.width - p.len)

/-- The IPv4 prefix `a.b.c.d/len` (dotted notation, RFC 4632 §3.1). -/
def ipv4Prefix (a b c d len : Nat) : Prefix :=
  ⟨32, ofBigEndianDigits 256 [a, b, c, d], len⟩

/-- The IPv6 prefix `s₀:s₁:…::/len`, given its leading segments; the omitted trailing segments
are `0` (the `::` of RFC 4291 §2.2 (2) at the end). -/
def ipv6Prefix (segs : List Nat) (len : Nat) : Prefix :=
  ⟨128, ofBigEndianDigits 65536 (segs ++ List.replicate (8 - segs.length) 0), len⟩

/-! ## Decidable equality of addresses -/

/-- Decidable equality of IPv4 addresses, by their octets (the derived `PartialEq` of
`Ipv4Addr`, `ip_addr.rs` lines 71–76, as in the model of `<IpAddr as PartialEq>::eq`). Decided
on the octet lists so that the kernel evaluates it on literals. -/
instance : DecidableEq core.net.ip_addr.Ipv4Addr := fun a b =>
  decidable_of_iff (a.addrOctets.val = b.addrOctets.val) (by
    cases a; cases b; simp [Array.eq_iff])

/-- Decidable equality of IPv6 addresses, by their segments (equal segments exactly when equal
octets, `Rmcp.TypesExternal`; the derived `PartialEq` of `Ipv6Addr`, `ip_addr.rs` lines
165–170). Decided on the segment lists so that the kernel evaluates it on
literals. -/
instance : DecidableEq core.net.ip_addr.Ipv6Addr := fun a b =>
  decidable_of_iff (a.addrSegments.val = b.addrSegments.val) (by
    cases a; cases b; simp [Array.eq_iff])

-- Decidable equality of IP addresses (same variant, equal address; the derived `PartialEq` of
-- `IpAddr`, `ip_addr.rs` lines 29–37), the equality of the model of
-- `<IpAddr as PartialEq>::eq` (`Rmcp.FunsExternal`).
deriving instance DecidableEq for rmcp.core.net.ip_addr.IpAddr

/-! ## IPv4 (A02) -/

/-- **The blocked IPv4 ranges** of plan Section 16.3, A02, in the plan's order: `10/8`,
`172.16/12`, `192.168/16` (private, RFC 1918 §3), `127/8` (loopback, RFC 1122 §3.2.1.3 (g)),
`169.254/16` (link-local, RFC 3927 §1, §2.1), `255.255.255.255/32` (limited broadcast,
RFC 919), `0.0.0.0/32` (this host, RFC 1122 §3.2.1.3 (a)), `224/4` (multicast, RFC 1112 §4),
`0/8` (this network, RFC 1122 §3.2.1.3 (b); RFC 6890 §2.2.2), `100.64/10` (shared address
space, RFC 6598 §7), `198.18/15` (benchmarking, RFC 2544 Appendix C.2.2; RFC 6890 §2.2.2). The
code tests them at `auth.rs` lines 1345–1353. `240.0.0.0/4` is not in the list (human decision
H8: recorded as a bug, see the module docstring). -/
def ipv4DisallowedPrefixes : List Prefix :=
  [ipv4Prefix 10 0 0 0 8, ipv4Prefix 172 16 0 0 12, ipv4Prefix 192 168 0 0 16,
   ipv4Prefix 127 0 0 0 8, ipv4Prefix 169 254 0 0 16, ipv4Prefix 255 255 255 255 32,
   ipv4Prefix 0 0 0 0 32, ipv4Prefix 224 0 0 0 4, ipv4Prefix 0 0 0 0 8,
   ipv4Prefix 100 64 0 0 10, ipv4Prefix 198 18 0 0 15]

/-- **A blocked IPv4 address**: the 32-bit address `v` is in one of `ipv4DisallowedPrefixes`
(plan Section 16.3, A02). Every prefix of the list lies below `2^32`, so a blocked `v` is below
`2^32`. -/
def ipv4Disallowed (v : Nat) : Bool :=
  ipv4DisallowedPrefixes.any (fun p => inPrefix p v)

/-! ## IPv6 (A01, A03) -/

/-- `::1`, the loopback address (RFC 4291 §2.5.3). -/
def ipv6Loopback : Prefix := ipv6Prefix [0, 0, 0, 0, 0, 0, 0, 1] 128
/-- `::`, the unspecified address (RFC 4291 §2.5.2). -/
def ipv6Unspecified : Prefix := ipv6Prefix [] 128
/-- `::ffff:0:0/96`, IPv4-mapped addresses (RFC 4291 §2.5.5.2). -/
def ipv4Mapped : Prefix := ipv6Prefix [0, 0, 0, 0, 0, 0xffff] 96
/-- `64:ff9b::/96`, the NAT64 well-known prefix (RFC 6052 §2.1). -/
def nat64WellKnown : Prefix := ipv6Prefix [0x64, 0xff9b] 96
/-- `::/96`, IPv4-compatible addresses (RFC 4291 §2.5.5.1, deprecated). -/
def ipv4Compatible : Prefix := ipv6Prefix [] 96
/-- `2002::/16`, 6to4 (RFC 3056 §2). -/
def sixToFour : Prefix := ipv6Prefix [0x2002] 16
/-- `ff00::/8`, multicast (RFC 4291 §2.7). -/
def ipv6Multicast : Prefix := ipv6Prefix [0xff00] 8
/-- `fe80::/10`, link-local unicast (RFC 4291 §2.5.6). -/
def ipv6LinkLocal : Prefix := ipv6Prefix [0xfe80] 10
/-- `fc00::/7`, unique local addresses (RFC 4193 §3.1). -/
def ipv6UniqueLocal : Prefix := ipv6Prefix [0xfc00] 7
/-- `2001::/32`, Teredo (RFC 4380 §2.6). -/
def teredo : Prefix := ipv6Prefix [0x2001, 0] 32
/-- `64:ff9b:1::/48`, the local-use NAT64 prefix (RFC 8215). -/
def nat64LocalUse : Prefix := ipv6Prefix [0x64, 0xff9b, 1] 48

/-- **The IPv4 address an IPv6 address carries** (plan Section 16.3, A01), as a 32-bit value:
- IPv4-mapped `::ffff:0:0/96` (RFC 4291 §2.5.5.2) or NAT64 `64:ff9b::/96` (RFC 6052 §2.2, a
  /96 prefix puts the IPv4 address in bits 96–127): the last 32 bits;
- IPv4-compatible `::/96` (RFC 4291 §2.5.5.1), except `::` and `::1` (plan Section 17; they are
  the unspecified and loopback addresses): the last 32 bits;
- 6to4 `2002::/16` (RFC 3056 §2, `2002:V4ADDR::/48`): bits 16–47, i.e. segments 1 and 2;
- otherwise none. The prefixes of the first two cases do not overlap the others, and `::/96`
  does not overlap `2002::/16`, so the order of the cases does not matter.
On segments `[a, b, c, d, e, f, g, h]` the value is `g·2^16 + h`, respectively `b·2^16 + c`,
the plan's wording. The code is `auth.rs` lines 1359–1368. -/
def embeddedIpv4 (v : Nat) : Option Nat :=
  if inPrefix ipv4Mapped v || inPrefix nat64WellKnown v then some (v % 2 ^ 32)
  else if inPrefix ipv4Compatible v && v != 0 && v != 1 then some (v % 2 ^ 32)
  else if inPrefix sixToFour v then some (v / 2 ^ 80 % 2 ^ 32)
  else none

/-- **The IPv6 ranges blocked outright** when no IPv4 address is embedded (plan Section 16.3,
A03, in the plan's order): `::1`, `::`, `ff00::/8`, `fe80::/10`, `fc00::/7`, `2001::/32`,
`64:ff9b:1::/48` (the last one as a whole, human decision H8). The code tests them at `auth.rs`
lines 1376–1382. -/
def ipv6DisallowedPrefixes : List Prefix :=
  [ipv6Loopback, ipv6Unspecified, ipv6Multicast, ipv6LinkLocal, ipv6UniqueLocal, teredo,
   nat64LocalUse]

/-- **A blocked IPv6 address** (plan Section 16.3, A03): if it carries an IPv4 address
(`embeddedIpv4`), exactly when that address is blocked (`ipv4Disallowed`); otherwise exactly
when it is in one of `ipv6DisallowedPrefixes`. -/
def ipv6Disallowed (v : Nat) : Bool :=
  match embeddedIpv4 v with
  | some w => ipv4Disallowed w
  | none => ipv6DisallowedPrefixes.any (fun p => inPrefix p v)

/-! ## Regression checks

Kernel-checked evaluations on the boundary cases of plan Section 22 (rows A01, A02, A03/C04) and
on the ranges the lists leave out (module docstring). `ipv4` and `ipv6` build addresses from
their octets and segments. -/

/-- The 32-bit value of `a.b.c.d` (used only by the checks). -/
private def ipv4 (a b c d : Nat) : Nat := ofBigEndianDigits 256 [a, b, c, d]

/-- The 128-bit value of the eight segments `s` (used only by the checks). -/
private def ipv6 (s : List Nat) : Nat := ofBigEndianDigits 65536 s

-- A01 (plan Section 22).
example : embeddedIpv4 (ipv6 [0, 0, 0, 0, 0, 0xffff, 0x0a00, 0x0001]) = some (ipv4 10 0 0 1) :=
  by decide
example : embeddedIpv4 (ipv6 [0x64, 0xff9b, 0, 0, 0, 0, 0xc0a8, 0x0101]) =
    some (ipv4 192 168 1 1) := by
  decide
example : embeddedIpv4 (ipv6 [0, 0, 0, 0, 0, 0, 0x0808, 0x0808]) = some (ipv4 8 8 8 8) := by
  decide
example : embeddedIpv4 (ipv6 [0, 0, 0, 0, 0, 0, 0, 0]) = none := by decide
example : embeddedIpv4 (ipv6 [0, 0, 0, 0, 0, 0, 0, 1]) = none := by decide
example : embeddedIpv4 (ipv6 [0, 0, 0, 0, 0, 0, 0, 2]) = some (ipv4 0 0 0 2) := by decide
example : embeddedIpv4 (ipv6 [0x2002, 0xabcd, 0xef01, 0, 0, 0, 0, 0]) =
    some (ipv4 171 205 239 1) := by
  decide
example : embeddedIpv4 (ipv6 [0x64, 0xff9b, 1, 0, 0, 0, 0, 1]) = none := by decide
example : embeddedIpv4 (ipv6 [0, 0, 0, 0, 0xffff, 0, 0x0a00, 0x0001]) = none := by decide
example : embeddedIpv4 (ipv6 [0x2001, 0, 0x4136, 0xe378, 0x8000, 0x63bf, 0x3fff, 0xfdd2]) =
    none := by
  decide

-- A02: the first and last address of each range, and the addresses just outside it.
example : [ipv4 10 0 0 0, ipv4 10 255 255 255, ipv4 172 16 0 0, ipv4 172 31 255 255,
    ipv4 192 168 0 0, ipv4 192 168 255 255, ipv4 127 0 0 0, ipv4 127 255 255 255,
    ipv4 169 254 0 0, ipv4 169 254 255 255, ipv4 255 255 255 255, ipv4 0 0 0 0, ipv4 224 0 0 0,
    ipv4 239 255 255 255, ipv4 0 255 255 255, ipv4 100 64 0 0, ipv4 100 127 255 255,
    ipv4 198 18 0 0, ipv4 198 19 255 255].all ipv4Disallowed = true := by
  decide
example : [ipv4 9 255 255 255, ipv4 11 0 0 0, ipv4 172 15 255 255, ipv4 172 32 0 0,
    ipv4 192 167 255 255, ipv4 192 169 0 0, ipv4 126 255 255 255, ipv4 128 0 0 0,
    ipv4 169 253 255 255, ipv4 169 255 0 0, ipv4 255 255 255 254, ipv4 1 0 0 0,
    ipv4 223 255 255 255, ipv4 240 0 0 0, ipv4 100 63 255 255, ipv4 100 128 0 0,
    ipv4 198 17 255 255, ipv4 198 20 0 0, ipv4 8 8 8 8].all (fun v => !ipv4Disallowed v) =
    true := by
  decide
-- A02: special-purpose IPv4 ranges outside the plan's list are not blocked (`240.0.0.0/4`:
-- the bug recorded under H8; the others: the H8 scope note).
example : [ipv4 192 0 0 1, ipv4 192 0 2 1, ipv4 198 51 100 1, ipv4 203 0 113 1,
    ipv4 192 88 99 1, ipv4 192 31 196 1, ipv4 192 52 193 1, ipv4 192 175 48 1, ipv4 240 0 0 1,
    ipv4 255 255 255 254].all (fun v => !ipv4Disallowed v) = true := by
  decide

-- A03/C04: each prefix boundary.
example : [ipv6 [0, 0, 0, 0, 0, 0, 0, 1], ipv6 [0, 0, 0, 0, 0, 0, 0, 0],
    ipv6 [0xff00, 0, 0, 0, 0, 0, 0, 0],
    ipv6 [0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff],
    ipv6 [0xfe80, 0, 0, 0, 0, 0, 0, 0],
    ipv6 [0xfebf, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff],
    ipv6 [0xfc00, 0, 0, 0, 0, 0, 0, 0],
    ipv6 [0xfdff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff],
    ipv6 [0x2001, 0, 0, 0, 0, 0, 0, 0],
    ipv6 [0x2001, 0, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff],
    ipv6 [0x64, 0xff9b, 1, 0, 0, 0, 0, 0],
    ipv6 [0x64, 0xff9b, 1, 0xffff, 0xffff, 0xffff, 0x0808, 0x0808]].all ipv6Disallowed =
    true := by
  decide
example : [ipv6 [0xfeff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff],
    ipv6 [0xfe7f, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff],
    ipv6 [0xfec0, 0, 0, 0, 0, 0, 0, 0],
    ipv6 [0xfbff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff],
    ipv6 [0xfe00, 0, 0, 0, 0, 0, 0, 0], ipv6 [0x2001, 1, 0, 0, 0, 0, 0, 0],
    ipv6 [0x2000, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff],
    ipv6 [0x64, 0xff9b, 0, 0, 0, 1, 0, 0], ipv6 [0x64, 0xff9b, 2, 0, 0, 0, 0, 0],
    ipv6 [0x64, 0xff9b, 0, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff],
    ipv6 [0x2606, 0x4700, 0, 0, 0, 0, 0, 0x1111]].all (fun v => !ipv6Disallowed v) = true := by
  decide
-- A03/C04: a blocked IPv4 address in each of the four forms, and the same forms with a public
-- one.
example : [ipv6 [0, 0, 0, 0, 0, 0xffff, 0xa9fe, 0xa9fe],
    ipv6 [0x64, 0xff9b, 0, 0, 0, 0, 0x7f00, 1], ipv6 [0, 0, 0, 0, 0, 0, 0x0a00, 1],
    ipv6 [0x2002, 0xc0a8, 0x0001, 0, 0, 0, 0, 1],
    ipv6 [0, 0, 0, 0, 0, 0, 0, 2]].all ipv6Disallowed = true := by
  decide
example : [ipv6 [0, 0, 0, 0, 0, 0xffff, 0x0808, 0x0808],
    ipv6 [0x64, 0xff9b, 0, 0, 0, 0, 0x0808, 0x0808],
    ipv6 [0, 0, 0, 0, 0, 0, 0x0808, 0x0808], ipv6 [0x2002, 0x0808, 0x0808, 0, 0, 0, 0, 1]].all
    (fun v => !ipv6Disallowed v) = true := by
  decide
-- A01, A03/C04: addresses next to the outer edges of the 6to4 (`2002::/16`), IPv4-mapped
-- (`::ffff:0:0/96`), IPv4-compatible (`::/96`) and NAT64 (`64:ff9b::/96`) prefixes, but outside
-- them, carry no IPv4 address: the code matches the full leading segments `[0x2002, ..]`,
-- `[0, 0, 0, 0, 0, 0xffff]`, `[0, 0, 0, 0, 0, 0]` and `[0x64, 0xff9b, 0, 0, 0, 0]` (`auth.rs`
-- lines 1359–1368 at `7caec76`; plan Section 22, rows A01, A03/C04). Each of the wrong prefixes
-- `2002::/15`, `::ffff:0:0/95`, `::/95` and `::/80` makes this check fail.
example : [ipv6 [0x2003, 0xc0a8, 1, 0, 0, 0, 0, 0], ipv6 [0x2001, 0xffff, 0xffff, 0, 0, 0, 0, 0],
    ipv6 [0, 0, 0, 0, 0, 0xfffe, 0x0a00, 1], ipv6 [0, 0, 0, 0, 0, 1, 0x0a00, 1],
    ipv6 [0x64, 0xff9b, 0, 0, 1, 0, 0x0a00, 1]].all (fun v => embeddedIpv4 v == none) = true := by
  decide
-- A03: special-purpose IPv6 ranges outside the plan's list are not blocked (the H8 scope
-- note).
example : [ipv6 [0, 0, 0, 0, 0xffff, 0, 0x0a00, 1], ipv6 [0x100, 0, 0, 0, 0, 0, 0, 1],
    ipv6 [0x2001, 1, 0, 0, 0, 0, 0, 1], ipv6 [0x2001, 1, 0, 0, 0, 0, 0, 2],
    ipv6 [0x2001, 1, 0, 0, 0, 0, 0, 3], ipv6 [0x2001, 2, 0, 0, 0, 0, 0, 1],
    ipv6 [0x2001, 3, 0, 0, 0, 0, 0, 1], ipv6 [0x2001, 4, 0x112, 0, 0, 0, 0, 1],
    ipv6 [0x2001, 0x10, 0, 0, 0, 0, 0, 1], ipv6 [0x2001, 0x20, 0, 0, 0, 0, 0, 1],
    ipv6 [0x2001, 0xdb8, 0, 0, 0, 0, 0, 1], ipv6 [0x2620, 0x4f, 0x8000, 0, 0, 0, 0, 1],
    ipv6 [0x3fff, 0, 0, 0, 0, 0, 0, 1], ipv6 [0x5f00, 0, 0, 0, 0, 0, 0, 1],
    ipv6 [0xfec0, 0, 0, 0, 0, 0, 0, 1]].all (fun v => !ipv6Disallowed v) = true := by
  decide

end Defs.Net
