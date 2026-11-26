/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Aeneas
public import Mathlib.Data.List.DropRight
public import Rmcp.Types
public import Rmcp.FunsExternal
public import Defs.Bytes
public import Proofs.Defs.Net

@[expose] public section

/-!
# Definitions for the OAuth metadata address-policy statements (N01, N03–N11)

**Signed off by the human spec owner 2026-11-26; proved 2026-11-26
(Proofs/Transport/MetadataResolver.lean; restated in
Proofs/Internal/Transport/Auth/MetadataResolver.lean); accepted by the human owner 2026-11-26**
(written by AI, Claude Code `claude-opus-5-5`; five review rounds, two independent reviews each).
Built as part of the `Proofs` root (precedent `Proofs.Defs.Net`). The vocabulary of the
statements about
`crates/rmcp/src/transport/auth/metadata_resolver.rs`: the class of an IP address
(`addressClass`), the policy check (`isAllowed`), the classes a base URL grants
(`baseClasses`), the policy for an IP-literal target (`allowsHost`), host normalization
(`normalizeHost`), the host of a proxy value (`proxyHost`), the address filter
(`allowedAddresses`), the premises of `proxy_host` (`ProxyFits`, `ProxyHostUtf8`), and the
predicates of the invariants (`HostsNormalized`, `AllAllowed`, `AllPublic`,
`AllPublicOrPrivate`).
The targets are `pub(super)` or private, so these definitions live in `Proofs/Defs/` (human
decision 2026-11-24); module `Proofs.Defs.MetadataResolver`, Lean namespace
`Defs.MetadataResolver`.

**The policy** (module docstring of `metadata_resolver.rs`, lines 1–11 at upstream `7caec76`):
public addresses are always allowed; a loopback or private address only when the base URL names
one (a loopback or private IP literal, or `localhost`); link-local, unspecified, broadcast,
multicast and reserved addresses ("blocked") never; configured proxy hosts are not filtered.

**What the code treats as `Public`** (upstream lines 52–53 and 63–64: every address that the
A02/A03 guards `is_disallowed_metadata_ipv4`/`_ipv6` do not block): every address outside the
lists `Defs.Net.ipv4DisallowedPrefixes` and `Defs.Net.ipv6DisallowedPrefixes`, in particular
- `192.0.0.0/24` (IETF protocol assignments, RFC 6890 §2.2.2);
- the documentation ranges `192.0.2.0/24`, `198.51.100.0/24`, `203.0.113.0/24` (RFC 5737 §3)
  and `2001:db8::/32` (RFC 3849 §4);
- the deprecated site-local range `fec0::/10` (RFC 3879 §4);
- IPv4-mapped, NAT64, IPv4-compatible and 6to4 embeddings of a public IPv4 address (A01: the
  embedded address decides, upstream line 45);
- H8: `240.0.0.0/4` except `255.255.255.255` (reserved, RFC 1112 §4; not in the A02 list), also
  embedded in IPv6 (a recorded bug, `formal/docs/STATUS.md`, "Bugs found"; human decision
  2026-11-24: the statements describe the code).
Kernel-checked examples of each are at the end of the file. This is the only copy of the list:
the docstrings of `AllPublic` and of the statements point here.

**Addresses** are read through the numbers and prefixes of `Defs.Net` (A01–A03): the class of
an address is defined from the RFC ranges, in the order "loopback, private, otherwise blocked
if A02/A03 block it, otherwise public", not in the code's order (which tests the A02/A03 guard
first). The two agree because `127/8`, the private prefixes, `::1` and `fc00::/7` lie inside the
blocked lists. Below, this is kernel-checked only at the two end points of each range; for every
address the agreement is what N01's spec theorem `AddressClass.of_spec` states.

**Strings.** A Rust `&str` or `String` is described by its UTF-8 bytes (`Defs.utf8Bytes`).
Host normalization is defined on bytes (`List.rdropWhile` of the byte `.`, then ASCII
lowercase byte by byte), written from `str::trim_end_matches` and `u8::to_ascii_lowercase`,
not from the trusted models `ExtModel.dropTrailingDots` and `ExtModel.asciiLowercase`.

**URLs.** `url::Url` is abstract; its host enters only as the unopened opaque values
`ExtModel.urlHost u` and `ExtModel.urlHostStr u`, and URL parsing as `ExtModel.urlParse`
(human decision 2026-11-25). No definition states a law about them.

**Line citations.** "upstream" is `metadata_resolver.rs` at `7caec76` (unmodified in the
repository); "patched" is the copy with translation patches 01–05, from which the translation is
made (the `Source:` lines of `Rmcp.Funs`). `auth.rs` lines are upstream (patch 05 changes the
body of `is_loopback_metadata_host`, lines 1401–1410, without moving it).
-/

namespace Defs.MetadataResolver

open Aeneas.Std Defs.Net
open rmcp
-- `AddressClass` is the translated enum of `metadata_resolver.rs` (upstream lines 33–39).
open rmcp.transport.auth.metadata_resolver (AddressClass)

-- Decidable equality of address classes (the derived `PartialEq`/`Eq` of upstream line 33).
deriving instance DecidableEq for rmcp.transport.auth.metadata_resolver.AddressClass

-- The decidable equality of `Ipv4Addr`, `Ipv6Addr` and `IpAddr` used by `allowsHost` is in
-- `Proofs.Defs.Net` (shared IP vocabulary).

/-! ## Address classes (N01) -/

/-- `127.0.0.0/8`, IPv4 loopback (RFC 1122 §3.2.1.3 (g); `Ipv4Addr::is_loopback`). -/
def ipv4LoopbackPrefix : Prefix := ipv4Prefix 127 0 0 0 8

/-- **The IPv4 ranges the policy calls private**: `10/8`, `172.16/12`, `192.168/16` (RFC 1918
§3; `Ipv4Addr::is_private`) and `100.64/10` (shared address space, RFC 6598 §7; upstream line
56: `octets[0] == 100 && (64..=127).contains(&octets[1])`). -/
def ipv4PrivatePrefixes : List Prefix :=
  [ipv4Prefix 10 0 0 0 8, ipv4Prefix 172 16 0 0 12, ipv4Prefix 192 168 0 0 16,
   ipv4Prefix 100 64 0 0 10]

/-- **The class of the IPv4 address with 32-bit value `v`**: `Loopback` in `127/8`, `Private`
in `ipv4PrivatePrefixes`, otherwise `Blocked` if A02 blocks it (`ipv4Disallowed`), otherwise
`Public` (upstream lines 50–61). By H8, `240.0.0.0/4` except `255.255.255.255` is `Public`. -/
def ipv4Class (v : Nat) : AddressClass :=
  if inPrefix ipv4LoopbackPrefix v then .Loopback
  else if ipv4PrivatePrefixes.any (fun p => inPrefix p v) then .Private
  else if ipv4Disallowed v then .Blocked
  else .Public

/-- **The class of the IPv6 address with 128-bit value `v`**: if it carries an IPv4 address
`w` (A01, `embeddedIpv4`), the class of `w` (upstream lines 43–48: the address is replaced by
its embedded IPv4 address); otherwise `Loopback` for `::1`, `Private` in `fc00::/7` (unique
local, RFC 4193 §3.1; upstream line 67: `segments()[0] & 0xfe00 == 0xfc00`), otherwise
`Blocked` if A03 blocks it (`ipv6Disallowed`), otherwise `Public` (upstream lines 62–72). -/
def ipv6Class (v : Nat) : AddressClass :=
  match embeddedIpv4 v with
  | some w => ipv4Class w
  | none =>
    if inPrefix ipv6Loopback v then .Loopback
    else if inPrefix ipv6UniqueLocal v then .Private
    else if ipv6Disallowed v then .Blocked
    else .Public

/-- **The class of an IP address** (N01 `AddressClass::of`, upstream lines 42–74), read through
the value of its octets or segments (`ipv4Value`, `ipv6Value`). -/
def addressClass : core.net.ip_addr.IpAddr → AddressClass
  | .V4 a => ipv4Class (ipv4Value a.addrOctets.val)
  | .V6 a => ipv6Class (ipv6Value a.addrSegments.val)

/-! ## The policy check (N08) -/

/-- **Whether the policy allows an address of class `c`**, given the classes `baseClasses`
granted by the base URL (N08 `is_allowed`, upstream lines 180–186): `Public` always, `Loopback`
and `Private` only if granted, `Blocked` never. -/
def isAllowed (c : AddressClass) (baseClasses : List AddressClass) : Bool :=
  match c with
  | .Public => true
  | .Loopback => decide (AddressClass.Loopback ∈ baseClasses)
  | .Private => decide (AddressClass.Private ∈ baseClasses)
  | .Blocked => false

/-- **The classes after `allowing_private_addresses`** (N06, upstream lines 150–160): `Private`
appended unless already present. -/
def withPrivate (baseClasses : List AddressClass) : List AddressClass :=
  if AddressClass.Private ∈ baseClasses then baseClasses else baseClasses ++ [.Private]

/-! ## Hosts and URLs (N04, N07, N10, N11) -/

/-- The byte `.` (46). -/
def dotByte : U8 := 46#u8

/-- **`str::trim_end_matches('.')` on bytes**: the bytes without their trailing `.` bytes (the
byte 46 occurs in UTF-8 only as the character `.`). -/
def trimTrailingDots (host : List U8) : List U8 :=
  host.rdropWhile (fun b => decide (b = dotByte))

/-- **`u8::to_ascii_lowercase`**: `A`–`Z` (65–90) to `a`–`z` (97–122), every other byte
unchanged. -/
def asciiToLower (b : U8) : U8 :=
  if 65 ≤ b.val ∧ b.val ≤ 90 then ⟨BitVec.ofNat 8 (b.val + 32)⟩ else b

/-- **A normalized host name** (N11 `normalize_host`, upstream lines 223–225:
`host.trim_end_matches('.').to_ascii_lowercase()`): trailing dots removed, then ASCII letters
lowercased; other bytes, including non-ASCII ones and the brackets of an IPv6 literal, are
kept. -/
def normalizeHost (host : List U8) : List U8 :=
  (trimTrailingDots host).map asciiToLower

/-- **A `localhost` name** (`AuthorizationManager::is_loopback_metadata_host`, `auth.rs` lines
1403–1406, on a domain): after normalization, `localhost` or a name ending in `.localhost`
(RFC 6761 §6.3). -/
def isLocalhostName (domain : List U8) : Bool :=
  decide (normalizeHost domain = utf8Bytes "localhost") ||
    decide (utf8Bytes ".localhost" <:+ normalizeHost domain)

/-- **A loopback host** (`AuthorizationManager::is_loopback_metadata_host`, `auth.rs` lines
1401–1410): a `localhost` name, an IPv4 address in `127/8` (`Ipv4Addr::is_loopback`) or the IPv6
address `::1` (`Ipv6Addr::is_loopback`). -/
def isLoopbackHost : url.host.Host Str → Bool
  | .Domain d => isLocalhostName d.val
  | .Ipv4 a => inPrefix ipv4LoopbackPrefix (ipv4Value a.addrOctets.val)
  | .Ipv6 a => inPrefix ipv6Loopback (ipv6Value a.addrSegments.val)

/-- **The IP address of a host**, if it is an IP literal (`literal_ip`, upstream lines
215–221, on the host): `none` for a domain. -/
def hostIp : url.host.Host Str → Option core.net.ip_addr.IpAddr
  | .Domain _ => none
  | .Ipv4 a => some (.V4 a)
  | .Ipv6 a => some (.V6 a)

/-- **The IP literal of a URL with host `host`** (N10 `literal_ip`, upstream lines 215–221):
`none` without a host or for a domain host. Applied to `ExtModel.urlHost u` in the
statements. -/
def literalIp (host : Option (url.host.Host Str)) : Option core.net.ip_addr.IpAddr :=
  host.bind hostIp

/-- **The classes a base URL with host `host` grants** (N04 `with_lookup`, upstream lines
111–120): the class of an IP literal, `[Loopback]` for a `localhost` name, nothing for another
domain or no host. -/
def baseClasses : Option (url.host.Host Str) → List AddressClass
  | some (.Ipv4 a) => [addressClass (.V4 a)]
  | some (.Ipv6 a) => [addressClass (.V6 a)]
  | some (.Domain d) => if isLocalhostName d.val then [.Loopback] else []
  | none => []

/-- **Whether the policy allows a target URL with host `host`** (N07 `allows_url`, upstream
lines 164–172), given the base URL's literal `baseIp` and granted classes: a target without an
IP literal is allowed (line 170: reqwest resolves its name, and `resolve` filters the
addresses); an IP literal is allowed if it is the base URL's own literal (line 167) or its class
is allowed (line 168). -/
def allowsHost (baseIp : Option core.net.ip_addr.IpAddr) (baseClasses : List AddressClass)
    (host : Option (url.host.Host Str)) : Bool :=
  match literalIp host with
  | none => true
  | some ip => decide (baseIp = some ip) || isAllowed (addressClass ip) baseClasses

/-! ## Proxy hosts (N05) -/

/-- **The URL text read for a proxy value** (upstream lines 133–137, patched `proxy_host` lines
234–240): the value itself if it contains `://`, otherwise `http://` followed by it. -/
def proxyUrl (proxy : List U8) : List U8 :=
  if utf8Bytes "://" <:+: proxy then proxy else utf8Bytes "http://" ++ proxy

/-- **The unfiltered host of a proxy value** (upstream line 138, patched `proxy_host` lines
233–245): the normalized host string of the parsed `proxyUrl`, or `none` if it does not parse
or has no host. Parsing and the host string are the opaque `ExtModel.urlParse` and
`ExtModel.urlHostStr`. -/
def proxyHost (proxy : List U8) : Option (List U8) :=
  match ExtModel.urlParse (proxyUrl proxy) with
  | .Ok u => (ExtModel.urlHostStr u).map (fun h => normalizeHost h.val)
  | .Err _ => none

/-- **A proxy value fits the string models** (size premise of N05): its bytes fit in a slice
(the model of `String::deref`), and, without `://`, `http://` followed by it fits in a `String`
(the model of `String::push_str`, `ExtModel.maxStringBytes = isize::MAX`). The exact condition
under which `proxy_host` reaches no size failure; every Rust `String` meets the first part, and
the second fails in Rust too (the capacity panic of `format!`, upstream line 136). "Exact" is
meant for the Lean models (memory convention, `Rmcp.FunsExternal` module docstring: allocation
failure is not modelled): `proxy_host` fails with `maximumSizeExceeded` when the first part
fails and with `panic` when only the second fails (`proxy_host_fail`). -/
def ProxyFits (proxy : String) : Prop :=
  proxy.utf8ByteSize ≤ Usize.max ∧
    (¬ utf8Bytes "://" <:+: utf8Bytes proxy →
      (utf8Bytes "http://" ++ utf8Bytes proxy).length ≤ ExtModel.maxStringBytes)

/-- **The host string of a proxy value's URL is UTF-8** (UTF-8 premise of N05, rule (ii)(b) of
`Rmcp.FunsExternal`): if `proxyUrl proxy` parses to `u` and `u` has a host string `h`, the bytes
of `h` are UTF-8. Every Rust `&str` that `Url::host_str` returns is; the Lean model of
`host_str` is opaque (`ExtModel.urlHostStr`), so the premise is needed, and without it
`normalize_host` (patched line 244) fails with `undef` (`proxy_host_fail_undef`). -/
def ProxyHostUtf8 (proxy : String) : Prop :=
  ∀ u h, ExtModel.urlParse (proxyUrl (utf8Bytes proxy)) = .Ok u →
    ExtModel.urlHostStr u = some h → ExtModel.IsUtf8 h.val

/-- **Every host of the list is normalized**: `normalizeHost` leaves its UTF-8 bytes unchanged
(the invariant of `unfiltered_hosts`, whose new entries are `normalize_host` results, upstream
line 138; `resolve` compares them with the normalized name, line 193). -/
def HostsNormalized (hosts : List String) : Prop :=
  ∀ host ∈ hosts, normalizeHost (utf8Bytes host) = utf8Bytes host

/-! ## The address filter (N09) -/

/-- The IP address of a socket address (`SocketAddr::ip`). -/
def socketIp : core.net.socket_addr.SocketAddr → core.net.ip_addr.IpAddr
  | .V4 a => .V4 a.addrIp
  | .V6 a => .V6 a.addrIp

/-- **The addresses `resolve` returns for `host`** (N09, upstream lines 195–210; patched
`allowed_addresses`, lines 210–229): all resolved addresses for an unfiltered host (even none);
otherwise the resolved addresses whose class is allowed, in order, or `none` if there is no
such address. -/
def allowedAddresses (unfilteredHosts : List String) (baseClasses : List AddressClass)
    (host : String) (resolved : List core.net.socket_addr.SocketAddr) :
    Option (List core.net.socket_addr.SocketAddr) :=
  if host ∈ unfilteredHosts then some resolved
  else
    match resolved.filter (fun a => isAllowed (addressClass (socketIp a)) baseClasses) with
    | [] => none
    | allowed => some allowed

/-- **Every address of the list is allowed by the classes `baseClasses`** (`isAllowed` of its
class, N01 and N08; the check of upstream line 201). -/
def AllAllowed (baseClasses : List AddressClass) (addrs : List core.net.socket_addr.SocketAddr) :
    Prop :=
  ∀ a ∈ addrs, isAllowed (addressClass (socketIp a)) baseClasses = true

/-- **Every address of the list is `Public`** (`addressClass`): not loopback or private, and not
blocked by the A02/A03 guards. Which addresses that includes (H8 among them): "What the code
treats as `Public`" in the module docstring. -/
def AllPublic (addrs : List core.net.socket_addr.SocketAddr) : Prop :=
  ∀ a ∈ addrs, addressClass (socketIp a) = .Public

/-- **Every address of the list is `Public` or `Private`** (`addressClass`; for `Public` see
`AllPublic`): no loopback and no blocked address. -/
def AllPublicOrPrivate (addrs : List core.net.socket_addr.SocketAddr) : Prop :=
  ∀ a ∈ addrs, addressClass (socketIp a) = .Public ∨ addressClass (socketIp a) = .Private

instance (hosts : List String) : Decidable (HostsNormalized hosts) :=
  inferInstanceAs (Decidable (∀ host ∈ hosts, _))

instance (baseClasses : List AddressClass) (addrs : List core.net.socket_addr.SocketAddr) :
    Decidable (AllAllowed baseClasses addrs) :=
  inferInstanceAs (Decidable (∀ a ∈ addrs, _))

instance (addrs : List core.net.socket_addr.SocketAddr) : Decidable (AllPublic addrs) :=
  inferInstanceAs (Decidable (∀ a ∈ addrs, _))

instance (addrs : List core.net.socket_addr.SocketAddr) : Decidable (AllPublicOrPrivate addrs) :=
  inferInstanceAs (Decidable (∀ a ∈ addrs, _))

/-! ## Regression checks

Kernel-checked evaluations of the model on boundary cases (plan Section 22 style). -/

/-- The 32-bit value of `a.b.c.d` (used only by the checks). -/
private def ipv4 (a b c d : Nat) : Nat := ofBigEndianDigits 256 [a, b, c, d]

/-- The 128-bit value of the eight segments `s` (used only by the checks). -/
private def ipv6 (s : List Nat) : Nat := ofBigEndianDigits 65536 s

/-- The IPv4 literal host `a.b.c.d` (used only by the checks). -/
private def v4Host (a b c d : Nat) : url.host.Host Str :=
  .Ipv4 ⟨Array.make 4#usize ([a, b, c, d].map (fun n => ⟨BitVec.ofNat 8 n⟩))⟩

/-- The IPv6 literal host with segments `s` (used only by the checks). -/
private def v6Host (s₀ s₁ s₂ s₃ s₄ s₅ s₆ s₇ : Nat) : url.host.Host Str :=
  .Ipv6 ⟨Array.make 8#usize ([s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇].map (fun n => ⟨BitVec.ofNat 16 n⟩))⟩

/-- The domain host `mcp.example.com` (used only by the checks). -/
private def publicDomainHost : url.host.Host Str := .Domain (toStr "mcp.example.com")

-- The end points of the loopback and private ranges lie inside the blocked lists, so at them
-- the order of the tests in `ipv4Class`/`ipv6Class` agrees with the code's (guard first).
-- IPv4: `127/8`, `10/8`, `172.16/12`, `192.168/16`, `100.64/10`.
example : [ipv4 127 0 0 0, ipv4 127 255 255 255, ipv4 10 0 0 0, ipv4 10 255 255 255,
    ipv4 172 16 0 0, ipv4 172 31 255 255, ipv4 192 168 0 0, ipv4 192 168 255 255,
    ipv4 100 64 0 0, ipv4 100 127 255 255].all ipv4Disallowed = true := by
  decide

-- IPv6: `::1` and the end points `fc00::`, `fdff:ffff:…:ffff` of `fc00::/7`; none of them
-- carries an IPv4 address (A01 excludes `::1` from the IPv4-compatible form).
example : [ipv6 [0, 0, 0, 0, 0, 0, 0, 1], ipv6 [0xfc00, 0, 0, 0, 0, 0, 0, 0],
    ipv6 [0xfdff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff]].all
      (fun v => ipv6Disallowed v && (embeddedIpv4 v).isNone) = true := by
  decide

-- N01, IPv4 (`classifies_addresses`, upstream lines 294–317, and range edges).
example : [ipv4Class (ipv4 93 184 216 34), ipv4Class (ipv4 127 0 0 1),
    ipv4Class (ipv4 10 0 0 9), ipv4Class (ipv4 192 168 1 1), ipv4Class (ipv4 100 64 0 1),
    ipv4Class (ipv4 169 254 169 254), ipv4Class (ipv4 0 0 0 0),
    ipv4Class (ipv4 255 255 255 255), ipv4Class (ipv4 224 0 0 1),
    ipv4Class (ipv4 100 128 0 0), ipv4Class (ipv4 198 18 0 1), ipv4Class (ipv4 0 1 2 3)] =
    [.Public, .Loopback, .Private, .Private, .Private, .Blocked, .Blocked, .Blocked, .Blocked,
     .Public, .Blocked, .Blocked] := by
  decide

-- N01, H8: `240.0.0.0/4` other than the broadcast address is public (the code's behaviour).
example : [ipv4Class (ipv4 240 0 0 1), ipv4Class (ipv4 255 255 255 254)] = [.Public, .Public] :=
  by decide

-- N01, IPv6 (`classifies_addresses`): `2606:4700::1111`, `::1`, `::ffff:127.0.0.1`, `fd00::1`,
-- `::ffff:169.254.169.254`, `fe80::1`, `64:ff9b::a9fe:a9fe`, `2002:a9fe:a9fe::`,
-- `::169.254.169.254`, `2002:7f00:1::`, `64:ff9b::a00:9`, `64:ff9b::5db8:d822`,
-- `2001:0:4136:e378::1`, `64:ff9b:1::a9fe:a9fe`, `::` (unspecified), `ff02::1` (multicast).
example : [ipv6Class (ipv6 [0x2606, 0x4700, 0, 0, 0, 0, 0, 0x1111]),
    ipv6Class (ipv6 [0, 0, 0, 0, 0, 0, 0, 1]),
    ipv6Class (ipv6 [0, 0, 0, 0, 0, 0xffff, 0x7f00, 1]),
    ipv6Class (ipv6 [0xfd00, 0, 0, 0, 0, 0, 0, 1]),
    ipv6Class (ipv6 [0, 0, 0, 0, 0, 0xffff, 0xa9fe, 0xa9fe]),
    ipv6Class (ipv6 [0xfe80, 0, 0, 0, 0, 0, 0, 1]),
    ipv6Class (ipv6 [0x64, 0xff9b, 0, 0, 0, 0, 0xa9fe, 0xa9fe]),
    ipv6Class (ipv6 [0x2002, 0xa9fe, 0xa9fe, 0, 0, 0, 0, 0]),
    ipv6Class (ipv6 [0, 0, 0, 0, 0, 0, 0xa9fe, 0xa9fe]),
    ipv6Class (ipv6 [0x2002, 0x7f00, 1, 0, 0, 0, 0, 0]),
    ipv6Class (ipv6 [0x64, 0xff9b, 0, 0, 0, 0, 0x0a00, 9]),
    ipv6Class (ipv6 [0x64, 0xff9b, 0, 0, 0, 0, 0x5db8, 0xd822]),
    ipv6Class (ipv6 [0x2001, 0, 0x4136, 0xe378, 0, 0, 0, 1]),
    ipv6Class (ipv6 [0x64, 0xff9b, 1, 0, 0, 0, 0xa9fe, 0xa9fe]),
    ipv6Class (ipv6 [0, 0, 0, 0, 0, 0, 0, 0]),
    ipv6Class (ipv6 [0xff02, 0, 0, 0, 0, 0, 0, 1])] =
    [.Public, .Loopback, .Loopback, .Private, .Blocked, .Blocked, .Blocked, .Blocked, .Blocked,
     .Loopback, .Private, .Public, .Blocked, .Blocked, .Blocked, .Blocked] := by
  decide

-- N01, H8 through an embedding: `::ffff:240.0.0.1` is public.
example : ipv6Class (ipv6 [0, 0, 0, 0, 0, 0xffff, 0xf000, 1]) = .Public := by decide

-- N01, what the code treats as `Public` (module docstring): `192.0.0.8` (`192.0.0.0/24`), the
-- documentation addresses `192.0.2.1`, `198.51.100.1`, `203.0.113.1`, and (H8) `240.0.0.1`.
example : [ipv4Class (ipv4 192 0 0 8), ipv4Class (ipv4 192 0 2 1),
    ipv4Class (ipv4 198 51 100 1), ipv4Class (ipv4 203 0 113 1),
    ipv4Class (ipv4 240 0 0 1)] = [.Public, .Public, .Public, .Public, .Public] := by
  decide

-- N01, IPv6 public cases: `2001:db8::1` (documentation), `fec0::1` (site-local),
-- `::93.184.216.34` (IPv4-compatible) and `2002:5db8:d822::` (6to4) of a public address.
example : [ipv6Class (ipv6 [0x2001, 0xdb8, 0, 0, 0, 0, 0, 1]),
    ipv6Class (ipv6 [0xfec0, 0, 0, 0, 0, 0, 0, 1]),
    ipv6Class (ipv6 [0, 0, 0, 0, 0, 0, 0x5db8, 0xd822]),
    ipv6Class (ipv6 [0x2002, 0x5db8, 0xd822, 0, 0, 0, 0, 0])] =
    [.Public, .Public, .Public, .Public] := by
  decide

-- N04: the classes granted by `mcp.example.com`, `localhost`, `127.0.0.1`, `10.0.0.4`,
-- `169.254.169.254`, `[::1]` and no host.
example : [baseClasses (some publicDomainHost),
    baseClasses (some (.Domain (toStr "localhost"))), baseClasses (some (v4Host 127 0 0 1)),
    baseClasses (some (v4Host 10 0 0 4)), baseClasses (some (v4Host 169 254 169 254)),
    baseClasses (some (v6Host 0 0 0 0 0 0 0 1)), baseClasses none] =
    [[], [.Loopback], [.Loopback], [.Private], [.Blocked], [.Loopback], []] := by
  decide +kernel

-- N07 (`ip_literal_urls_follow_the_policy`, upstream lines 377–412): from the base
-- `mcp.example.com`, the literals `127.0.0.1`, `[::1]`, `10.0.0.1`, `169.254.169.254` are
-- refused, `93.184.216.35` and a name are allowed; from `127.0.0.1`, `127.0.0.2` is allowed;
-- from `0.0.0.0`, its own literal is allowed and `169.254.169.254` refused.
example :
    let pub := some publicDomainHost
    let lo := some (v4Host 127 0 0 1)
    let any := some (v4Host 0 0 0 0)
    [allowsHost (literalIp pub) (baseClasses pub) (some (v4Host 127 0 0 1)),
     allowsHost (literalIp pub) (baseClasses pub) (some (v6Host 0 0 0 0 0 0 0 1)),
     allowsHost (literalIp pub) (baseClasses pub) (some (v4Host 10 0 0 1)),
     allowsHost (literalIp pub) (baseClasses pub) (some (v4Host 169 254 169 254)),
     allowsHost (literalIp pub) (baseClasses pub) (some (v4Host 93 184 216 35)),
     allowsHost (literalIp pub) (baseClasses pub) (some (.Domain (toStr "auth.example.com"))),
     allowsHost (literalIp lo) (baseClasses lo) (some (v4Host 127 0 0 2)),
     allowsHost (literalIp any) (baseClasses any) (some (v4Host 0 0 0 0)),
     allowsHost (literalIp any) (baseClasses any) (some (v4Host 169 254 169 254))] =
    [false, false, false, false, true, true, true, true, false] := by
  decide +kernel

-- N07, H8: from the public base `mcp.example.com`, the literal targets `240.0.0.1` and
-- `[::ffff:240.0.0.1]` are allowed (the code's behaviour, a recorded bug).
example :
    let pub := some publicDomainHost
    allowsHost (literalIp pub) (baseClasses pub) (some (v4Host 240 0 0 1)) = true ∧
      allowsHost (literalIp pub) (baseClasses pub)
        (some (v6Host 0 0 0 0 0 0xffff 0xf000 1)) = true := by
  decide +kernel

-- N08: public always, blocked never, loopback and private only when granted.
example : isAllowed .Public [] = true ∧ isAllowed .Blocked [.Blocked, .Loopback] = false ∧
    isAllowed .Loopback [.Loopback] = true ∧ isAllowed .Loopback [.Private] = false ∧
    isAllowed .Private [.Private] = true ∧ isAllowed .Private [] = false := by
  decide

-- N06: `Private` is appended once.
example : withPrivate [.Loopback] = [.Loopback, .Private] ∧
    withPrivate [.Private, .Loopback] = [.Private, .Loopback] ∧ withPrivate [] = [.Private] := by
  decide

-- N11: trailing dots, upper case, IPv6 brackets, the empty host, non-ASCII bytes.
example : normalizeHost (utf8Bytes "Auth.Example.COM..") = utf8Bytes "auth.example.com" ∧
    normalizeHost (utf8Bytes "[::1]") = utf8Bytes "[::1]" ∧
    normalizeHost (utf8Bytes "[FE80::1]") = utf8Bytes "[fe80::1]" ∧
    normalizeHost [] = [] ∧ normalizeHost (utf8Bytes "...") = [] ∧
    normalizeHost (utf8Bytes "É.") = utf8Bytes "É" := by
  decide +kernel

-- `localhost` names: case and trailing dots are ignored; a name ending in `.localhost`
-- counts; `localhost.example` and `notlocalhost` do not.
example : isLocalhostName (utf8Bytes "LOCALHOST.") = true ∧
    isLocalhostName (utf8Bytes "app.localhost") = true ∧
    isLocalhostName (utf8Bytes ".localhost") = true ∧
    isLocalhostName (utf8Bytes "localhost.example") = false ∧
    isLocalhostName (utf8Bytes "notlocalhost") = false ∧ isLocalhostName [] = false := by
  decide +kernel

/-- The socket address `a.b.c.d:443` (used only by the checks). -/
private def v4Sock (a b c d : Nat) : core.net.socket_addr.SocketAddr :=
  .V4 ⟨⟨Array.make 4#usize ([a, b, c, d].map (fun n => ⟨BitVec.ofNat 8 n⟩))⟩, 443#u16⟩

-- N09 and the predicates: from a public base (no class granted), `allowedAddresses` keeps
-- `93.184.216.34` and drops `10.0.0.9`, `127.0.0.1` and `169.254.169.254`; the result is
-- `AllPublic`. With `Private` granted (`withPrivate []`), `10.0.0.9` is kept as well and the
-- result is `AllPublicOrPrivate` but not `AllPublic`. An unfiltered host gets every address; a
-- filtered host with no allowed address gets `none`. Results are compared through their IP
-- addresses (`socketIp`).
example :
    let addrs := [v4Sock 93 184 216 34, v4Sock 10 0 0 9, v4Sock 127 0 0 1,
      v4Sock 169 254 169 254]
    let ips (r : Option (List core.net.socket_addr.SocketAddr)) := r.map (List.map socketIp)
    ips (allowedAddresses [] [] "auth.example.com" addrs) =
        some [socketIp (v4Sock 93 184 216 34)] ∧
      AllPublic [v4Sock 93 184 216 34] ∧
      ips (allowedAddresses [] (withPrivate []) "auth.example.com" addrs) =
        some [socketIp (v4Sock 93 184 216 34), socketIp (v4Sock 10 0 0 9)] ∧
      AllAllowed (withPrivate []) [v4Sock 93 184 216 34, v4Sock 10 0 0 9] ∧
      AllPublicOrPrivate [v4Sock 93 184 216 34, v4Sock 10 0 0 9] ∧
      ¬ AllPublic [v4Sock 93 184 216 34, v4Sock 10 0 0 9] ∧
      ¬ AllPublicOrPrivate addrs ∧
      ips (allowedAddresses ["proxy"] [] "proxy" addrs) = some (addrs.map socketIp) ∧
      (allowedAddresses [] [] "auth.example.com" [v4Sock 10 0 0 9]).isNone := by
  decide +kernel

-- `HostsNormalized`: normalized hosts pass, a trailing dot or an upper-case letter does not.
example : HostsNormalized ["proxy.corp", "[::1]", ""] ∧ ¬ HostsNormalized ["proxy.corp."] ∧
    ¬ HostsNormalized ["Proxy"] := by
  decide +kernel

-- N05: the scheme is added only without `://`.
example : proxyUrl (utf8Bytes "proxy:3128") = utf8Bytes "http://proxy:3128" ∧
    proxyUrl (utf8Bytes "socks5://p") = utf8Bytes "socks5://p" := by
  decide +kernel

end Defs.MetadataResolver
