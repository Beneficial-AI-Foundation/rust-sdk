/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Defs
public import Proofs.Transport.MetadataResolver

@[expose] public section

/-!
# Internal spec file for crates/rmcp/src/transport/auth/metadata_resolver.rs (N01, N03–N11)

These are guarantees about `pub(super)` and private items of `metadata_resolver.rs` (and of the
private `AuthorizationManager::is_loopback_metadata_host` of `auth.rs`, a callee of N04), kept out
of `formal/specs/`, which holds only the public API (human decision 2026-11-24; path: lead
decision ND5). Index of all guarantees: `formal/specs/README.md`.

One row per theorem below; the theorem is `Theorems.metadata_resolver.<Theorem>` (rows marked
`auth.` are `Theorems.auth.AuthorizationManager.<Theorem>`). `law` is a statement about the
definitions of `Defs.MetadataResolver` only, with no Rust call; a composition is labelled by the
targets it combines. The keys of the last column are explained below the table.

| ID | Function | Theorem | Guarantee | Assumptions |
|---|---|---|---|---|
| N01 | `AddressClass::of` | `AddressClass.of` | never fails; `addressClass addr` | none |
| N03 | `MetadataAddressResolver::new` | `MetadataAddressResolver.new_eq` | `new = with_proxy_hosts ∘ with_base_url` (with the system lookup and the proxy values read) | none (E) |
| N03 | same | `MetadataAddressResolver.new_fields_of_eq_ok` | on success: `base_ip`, `base_classes`, `lookup` of the base URL | (E) |
| N03 | same | `MetadataAddressResolver.new_unfiltered_hosts_of_eq_ok` | on success: the unfiltered hosts are the `proxyHost`s of the proxy values | (E) |
| N04 | `is_loopback_metadata_host` | `auth.is_loopback_metadata_host` | never fails; `isLoopbackHost host` | (U) |
| N04 | same | `auth.is_loopback_metadata_host_fail` | a domain that is not UTF-8 fails with `undef` | none |
| N04 | `with_base_url` | `MetadataAddressResolver.with_base_url` | never fails; `literalIp`, no unfiltered host, `baseClasses`, the lookup | (U) |
| N04 | same | `MetadataAddressResolver.with_base_url_fail` | a base domain that is not UTF-8 fails with `undef` | none |
| N05 | `proxy_host` | `proxy_host` | never fails; `proxyHost` of the value | (F), (P) |
| N05 | same | `proxy_host_fail` | without (F): `maximumSizeExceeded` or `panic` | none |
| N05 | same | `proxy_host_fail_undef` | with (F), without (P): `undef` | (F) |
| N05 | `with_proxy_hosts` | `MetadataAddressResolver.with_proxy_hosts` | never fails; old hosts followed by the `proxyHost`s; other fields unchanged | (F), (P), (L) |
| N05 | same | `MetadataAddressResolver.with_proxy_hosts_of_eq_ok` | on success: as the spec theorem | none |
| N05 | same | `MetadataAddressResolver.proxyFits_and_proxyHostUtf8_of_with_proxy_hosts_eq_ok` | on success: (F) and (P) held for every value | none |
| N06 | `allowing_private_addresses` | `MetadataAddressResolver.allowing_private_addresses` | never fails; `withPrivate` of the classes; other fields unchanged | (R) |
| N06 | same | `MetadataAddressResolver.allowing_private_addresses_fail` | without (R): `maximumSizeExceeded` | none |
| N07 | `allows_url` | `MetadataAddressResolver.allows_url` | never fails; `allowsHost` of the target's host | none |
| N08 | `is_allowed` | `MetadataAddressResolver.is_allowed` | never fails; `isAllowed` | none |
| N09 | `allowed_addresses` | `MetadataAddressResolver.allowed_addresses` | never fails; `allowedAddresses` | none |
| N10 | `literal_ip` | `literal_ip` | never fails; `literalIp (urlHost target)` | none |
| N11 | `normalize_host` | `normalize_host` | never fails; `normalizeHost` of the bytes | (U) |
| N11 | same | `normalize_host_fail` | bytes that are not UTF-8 fail with `undef` | none |
| law | | `utf8Bytes_injective` | `Defs.utf8Bytes` is injective | none |
| law | | `utf8Bytes_mem_map_iff` | a string is in a list iff its bytes are in the mapped list | none |
| law | N08 | `isAllowed_public` | `Public` is always allowed | none |
| law | N08 | `isAllowed_blocked` | `Blocked` is never allowed | none |
| law | N08 | `isAllowed_mono` | more granted classes never refuse more | none |
| law | N08 | `eq_public_of_isAllowed` | without `Loopback` and `Private` granted, only `Public` is allowed | none |
| law | N07 | `allowsHost_literalIp_self` | the base URL's own host is allowed | none |
| law | N04 | `loopback_mem_baseClasses_iff` | `Loopback` is granted iff a loopback literal or a `localhost` name | none |
| law | N04 | `private_mem_baseClasses_iff` | `Private` is granted iff a private literal | none |
| law | N04 | `length_baseClasses_le_one` | at most one class is granted | none |
| law | N09 | `allowedAddresses_sublist` | the result is a sublist of the resolved addresses | none |
| law | N09 | `allowedAddresses_eq_some_of_mem` | an unfiltered host gets every address | none |
| law | N09 | `allowedAddresses_eq_none_iff` | a filtered host gets `none` iff no address is allowed | none |
| law | N09 | `allAllowed_of_allowedAddresses_eq_some` | a filtered host gets only allowed addresses | none |
| law | N09 | `addressClass_ne_blocked_of_mem_allowedAddresses` | a filtered host gets no blocked address | none |
| law | N11 | `normalizeHost_idem` | normalization is idempotent | none |
| law | N11 | `normalizeHost_append_dot` | a trailing `.` is ignored | none |
| law | N11 | `normalizeHost_map_asciiToLower` | ASCII case is ignored | none |
| law | N11 | `isLocalhostName_normalizeHost` | `localhost` names are invariant under normalization | none |
| N01+A01 | `AddressClass::of`, `embedded_ipv4` | `AddressClass.of_v6_eq_of_embedded_ipv4_eq_ok_some` | an embedded IPv4 address has its own class | none |
| N05 | `with_proxy_hosts` | `MetadataAddressResolver.hostsNormalized_of_with_proxy_hosts_eq_ok` | on success: the unfiltered hosts stay normalized | none |
| N03 | `new` | `MetadataAddressResolver.hostsNormalized_of_new_eq_ok` | on success: the unfiltered hosts are normalized | (E) |
| N03 | `new` | `MetadataAddressResolver.mem_unfiltered_hosts_iff_of_new_eq_ok` | on success: a host is unfiltered iff its bytes are a `proxyHost` | (E) |
| N06+N08 | `allowing_private_addresses`, `is_allowed` | `MetadataAddressResolver.is_allowed_of_allowing_private_addresses_eq_ok` | allowed after iff allowed before or `Private` | none |
| N06 | `allowing_private_addresses` | `MetadataAddressResolver.allowing_private_addresses_idem` | twice is once (failure included) | none |
| N03+N06 | `new`, `allowing_private_addresses` | `MetadataAddressResolver.exists_allowing_private_addresses_eq_ok_of_new_eq_ok` | if `new` succeeds, so does `allowing_private_addresses` | (E) |
| N04+N07 | `with_base_url`, `allows_url` | `MetadataAddressResolver.allows_url_self_of_with_base_url_eq_ok` | the base URL itself is allowed | none |
| N03+N07 | `new`, `allows_url` | `MetadataAddressResolver.allows_url_self_of_new_eq_ok` | the base URL itself is allowed | (E) |
| N04+N07 | `with_base_url`, `allows_url` | `MetadataAddressResolver.allows_url_iff_public_of_with_base_url_eq_ok` | public base name: only names and `Public` literals | (D) |
| N03+N07 | `new`, `allows_url` | `MetadataAddressResolver.allows_url_of_new_eq_ok` | `allowsHost` with the base URL's literal and classes | (E) |
| N03+N07 | `new`, `allows_url` | `MetadataAddressResolver.allows_url_iff_public_of_new_eq_ok` | public base name: only names and `Public` literals | (D), (E) |
| N03+N06+N07 | `new`, `allowing_private_addresses`, `allows_url` | `MetadataAddressResolver.allows_url_of_new_allowing_private_addresses_eq_ok` | `allowsHost` with `withPrivate` of the classes | (E) |
| N03+N06+N07 | same | `MetadataAddressResolver.allows_url_iff_public_or_private_of_new_allowing_private_addresses_eq_ok` | public base name: only names, `Public` and `Private` literals | (D), (E) |
| N07 | `allows_url` | `MetadataAddressResolver.allows_url_eq_false_of_blocked` | a blocked literal other than the base's is refused | none |
| N09 | `allowed_addresses` | `MetadataAddressResolver.is_allowed_of_mem_of_allowed_addresses_eq_ok` | every returned address of a filtered host passes `is_allowed` | none |
| N04+N09 | `with_base_url`, `allowed_addresses` | `MetadataAddressResolver.allPublic_of_with_base_url_eq_ok` | public base name: only `Public` addresses | (D) |
| N03+N09 | `new`, `allowed_addresses` | `MetadataAddressResolver.allAllowed_of_new_eq_ok` | filtered hosts: only addresses allowed by `baseClasses` | (E) |
| N03+N09 | `new`, `allowed_addresses` | `MetadataAddressResolver.allPublic_of_new_eq_ok` | public base name, filtered hosts: only `Public` addresses | (D), (E) |
| N03+N06+N09 | `new`, `allowing_private_addresses`, `allowed_addresses` | `MetadataAddressResolver.allAllowed_of_new_allowing_private_addresses_eq_ok` | filtered hosts: only addresses allowed by `withPrivate` | (E) |
| N03+N06+N09 | same | `MetadataAddressResolver.allPublicOrPrivate_of_new_allowing_private_addresses_eq_ok` | public base name, filtered hosts: only `Public` or `Private` | (D), (E) |
| N03+N09 | `new`, `allowed_addresses` | `MetadataAddressResolver.allowed_addresses_eq_ok_some_of_new_eq_ok_of_mem_proxyHosts` | a proxy host gets every resolved address | (E) |
| N11 | `normalize_host` | `normalize_host_idem` | normalizing twice is once (failure included) | none |

Rows with "never fails" say that the call does not panic and that its result satisfies the
guarantee; "on success" rows and the compositions cover only successful calls (`… = ok r`) and do
not show that a call succeeds. Keys: (U) the domain or `&str` argument is UTF-8
(`ExtModel.IsUtf8`; rule (ii) of `formal/trusted/Rmcp/FunsExternal.lean`), the weakest premise
(the `_fail` rows); (F) `ProxyFits` of each proxy value (sizes, exact for the Lean models); (P)
`ProxyHostUtf8` of each proxy value (the host string of its parsed URL is UTF-8); (L) the
unfiltered hosts with the new ones fit in a `Vec` (`Usize.max`); (R) `Private` is already
granted or there is room for one more class; (D) the base URL's host is a domain other than a
`localhost` name; (E) for every value of the opaque environment reading
`ExtModel.proxyEnvValues`, with no premise on it (review rule at `ExtModel.proxyEnvValues`; human
decision T4, 2026-11-26): `new` gets an equation and facts about its successful calls, and no
success spec, because its Lean model fails on inputs no Rust call produces (a proxy value of more
than `Usize.max` bytes, or one for which `http://` followed by it exceeds `isize::MAX` bytes; a
base or proxy host whose bytes are not UTF-8). No statement about a successful call has a UTF-8
premise: success implies it.

**`Public`** (H8, human decision 2026-11-24: the statements describe the code): every statement
that concludes `Public` (also through `AllPublic` or `AllPublicOrPrivate`) means the class
`addressClass` gives, not "globally routable"; which addresses that includes (H8, `240.0.0.0/4`
except `255.255.255.255`, among them) is listed in "What the code treats as `Public`" in the
module docstring of `Proofs.Defs.MetadataResolver`, the only copy of that list. "The header" in
the docstrings below refers to this paragraph.

**Strings.** Hosts are `String`s where the code compares them (`allowed_addresses`, the membership
test of upstream line 195) and bytes (`Defs.utf8Bytes`) where they are computed (`proxyHost`,
`normalizeHost`); `utf8Bytes_injective` and `utf8Bytes_mem_map_iff` bridge the two.

**Namespaces.** The newtype `Lookup` of patch 05 is declared by `Rmcp.TypesExternal` in the root
namespace `transport.auth.metadata_resolver`, not under `rmcp`; it is opened by its root name
below, and the translated functions are written with their full names.

**Unverified glue** (patch 05 header): the async shells of `resolve` (`normalize_host` of the name,
the lookup, `warn!`, the error message, the `Some`/`None` to `Ok`/`Err` mapping) and of
`with_lookup` (`Self::with_base_url(base_url, Lookup(lookup))`), the bodies of
`prim::system_lookup` and `prim::proxy_env_values`, the derived `Clone` impls and URL parsing
(`ExtModel.urlHost`, `ExtModel.urlHostStr`, `ExtModel.urlParse` are opaque and appear unopened;
no statement assumes a law about them).

Each statement is restated as a theorem proved by the theorem of the same name (with `_spec`
for the spec theorems) in `Proofs/Transport/MetadataResolver.lean` (namespaces
`rmcp.transport.auth.metadata_resolver`, `rmcp.transport.auth.AuthorizationManager` and, for the
laws, `Defs.MetadataResolver`), and followed by the assumptions its proof depends on, checked by
`#print axioms` under `#guard_msgs`. Signed off by the spec owner on 2026-11-26 (five spec-cycle
rounds); the signed-off text is in `specs/Drafts/MetadataResolver.lean`, to be removed at
incorporation. N02 is dropped (human decision 2026-11-25).

Translated configuration (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
`--no-default-features` with the features of Phase 2 (plan Section 15), with
`overflow-checks=true` and `debug-assertions=true` (plan Section 1), through translation patch 05
(`formal/trusted/patches/05-metadata-resolver.patch`). Aeneas `nightly-2026.11.24-fb44cb4`.
"upstream" line numbers refer to `metadata_resolver.rs` at `7caec76` (unmodified in the
repository); "patched" to the copy with translation patches 01–05; `auth.rs` lines are upstream.

Definitions used: `Defs.MetadataResolver`, in module `Proofs.Defs.MetadataResolver`
(`formal/proofs/Proofs/Defs/MetadataResolver.lean`), on top of `Defs.Net` (A01–A03) and
`Defs.utf8Bytes`. External models used (`trusted/Rmcp/{Types,Funs}External.lean`, section
"`metadata_resolver.rs` address policy", and the `core::net`, string, `Vec` and slice models):
their laws are in `Proofs/External/MetadataResolver.lean`, `Proofs/External/Net.lean`,
`Proofs/External/Std.lean` and `Proofs/External/String.lean`. Native-code assumptions reached:
none.
-/

open Aeneas Aeneas.Std Result
open rmcp
open Defs.MetadataResolver
-- The newtype `Lookup` of patch 05 hunk H1 (patched line 102), declared at the root by
-- `Rmcp.TypesExternal`.
open transport.auth.metadata_resolver (Lookup)
open rmcp.transport.auth.metadata_resolver (AddressClass MetadataAddressResolver)

/-! ## N01 `AddressClass::of` (upstream lines 42–74) -/

/-- **Spec theorem for `rmcp::transport::auth::metadata_resolver::AddressClass::of`** (N01)

Never fails. The class of the address (`Defs.MetadataResolver.addressClass`): an IPv6 address
that carries an IPv4 address (A01: IPv4-mapped, NAT64 `64:ff9b::/96`, IPv4-compatible, 6to4) is
classified as that IPv4 address (lines 43–48); an IPv4 address is `Loopback` in `127/8`,
`Private` in `10/8`, `172.16/12`, `192.168/16`, `100.64/10`, otherwise `Blocked` if A02 blocks
it, otherwise `Public` (lines 50–61); another IPv6 address is `Loopback` for `::1`, `Private` in
`fc00::/7`, otherwise `Blocked` if A03 blocks it, otherwise `Public` (lines 62–72). For
`Public` (H8 among it), see the header. No premise. -/
theorem Theorems.metadata_resolver.AddressClass.of (addr : core.net.ip_addr.IpAddr) :
    rmcp.transport.auth.metadata_resolver.AddressClass.of addr ⦃ (result : AddressClass) =>
      result = addressClass addr ⦄ :=
  @rmcp.transport.auth.metadata_resolver.AddressClass.of_spec addr

/--
info: 'Theorems.metadata_resolver.AddressClass.of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.AddressClass.of

/-! ## N03 `MetadataAddressResolver::new` (upstream lines 101–107; patched 105–108) -/

/-- **N03 `new` is `with_proxy_hosts ∘ with_base_url`** (patched lines 105–108, hunk H3):
`new base_url` builds the resolver of `base_url` with the operating-system resolver
`ExtModel.systemLookup` and then exempts the hosts of the proxy values read from the
environment. Names `ExtModel.proxyEnvValues` only to say that the reading is passed to
`with_proxy_hosts` (review rule at `ExtModel.proxyEnvValues`); an equation between
computations, failure included. Not tagged `@[step]`. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.new_eq (base_url : url.Url) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new base_url =
      (do
        let r ← rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.with_base_url base_url
          ExtModel.systemLookup
        rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.with_proxy_hosts
          (core.iter.traits.collect.IntoIteratorVec String) r ExtModel.proxyEnvValues) :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new_eq base_url

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.new_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.new_eq

/-- **N03, the fields not set from the environment** (human decision T4, 2026-11-26): if
`new base_url` returns `r`, then `r` has the base literal, the granted classes and the lookup
of `with_base_url base_url ExtModel.systemLookup` (N04): `base_ip` is the IP literal of the
base URL, `base_classes` is `baseClasses (urlHost base_url)` and `lookup` is the
operating-system resolver; this holds for every value of `ExtModel.proxyEnvValues`. Covers only
successful calls and does not show that the call succeeds (see the module docstring). No
premise. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.new_fields_of_eq_ok (base_url : url.Url)
    (r : MetadataAddressResolver)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new base_url = ok r) :
    r.base_ip = literalIp (ExtModel.urlHost base_url) ∧
      r.base_classes.data.val = baseClasses (ExtModel.urlHost base_url) ∧
      r.lookup = ExtModel.systemLookup :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new_fields_of_eq_ok base_url r h

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.new_fields_of_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.new_fields_of_eq_ok

/-- **N03, the unfiltered hosts** (human decision 2026-11-26, extension of T4): if
`new base_url` returns `r`, its unfiltered hosts are, in order, the normalized hosts
(`proxyHost`) of the proxy values that `new` reads from the environment
(`ExtModel.proxyEnvValues`, upstream lines 102–106) and passes to `with_proxy_hosts` (N05),
skipping the values without one; `with_base_url` starts with none (line 123). Names
`ExtModel.proxyEnvValues` only as the values `new` passes on, with no premise on them. Covers
only successful calls and does not show that the call succeeds. No premise. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.new_unfiltered_hosts_of_eq_ok
    (base_url : url.Url) (r : MetadataAddressResolver)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new base_url = ok r) :
    r.unfiltered_hosts.data.val.map Defs.utf8Bytes =
      ExtModel.proxyEnvValues.val.filterMap (fun p => proxyHost (Defs.utf8Bytes p)) :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new_unfiltered_hosts_of_eq_ok
    base_url r h

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.new_unfiltered_hosts_of_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.new_unfiltered_hosts_of_eq_ok

/-! ## N04 `with_lookup` (upstream lines 109–127), through `with_base_url` (patched 114–136) -/

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::is_loopback_metadata_host`**
(helper of N04; `auth.rs` lines 1401–1410, patch 05 hunk H9)

For a host whose domain, if any, is UTF-8 (rule (ii)(a): the `&str` carried by the argument
`Host<&str>`), never fails: `true` exactly for a `localhost` name (after removing trailing dots
and lowercasing ASCII letters, `localhost` or a name ending in `.localhost`), an IPv4 address
in `127/8` or the IPv6 address `::1` (`Defs.MetadataResolver.isLoopbackHost`). The premise is
the weakest (`is_loopback_metadata_host_fail`). -/
theorem Theorems.auth.AuthorizationManager.is_loopback_metadata_host (host : url.host.Host Str)
    (h_utf8 : ∀ d, host = url.host.Host.Domain d → ExtModel.IsUtf8 d.val) :
    rmcp.transport.auth.AuthorizationManager.is_loopback_metadata_host host ⦃ (result : Bool) =>
      result = isLoopbackHost host ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.is_loopback_metadata_host_spec host h_utf8

/--
info: 'Theorems.auth.AuthorizationManager.is_loopback_metadata_host' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_loopback_metadata_host

/-- **`is_loopback_metadata_host`, the UTF-8 premise is the weakest**: for a domain whose
bytes are not UTF-8 (no Rust `&str`), `to_ascii_lowercase` (`auth.rs` line 1404:
`domain.trim_end_matches('.').to_ascii_lowercase()`) fails, so the call fails with `undef`.
The proof needs the converse UTF-8 lemmas named at `normalize_host_fail`. -/
theorem Theorems.auth.AuthorizationManager.is_loopback_metadata_host_fail (d : Str)
    (h : ¬ ExtModel.IsUtf8 d.val) :
    rmcp.transport.auth.AuthorizationManager.is_loopback_metadata_host (url.host.Host.Domain d) =
      fail .undef :=
  @rmcp.transport.auth.AuthorizationManager.is_loopback_metadata_host_fail d h

/--
info: 'Theorems.auth.AuthorizationManager.is_loopback_metadata_host_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_loopback_metadata_host_fail

/-- **Spec theorem for
`rmcp::transport::auth::metadata_resolver::MetadataAddressResolver::with_base_url`** (N04; the
body of `with_lookup`, upstream lines 109–127, moved by patch 05 hunk H2 to patched lines
114–136)

If the domain of the base URL, if any, is UTF-8 (rule (ii)(b), the host `urlHost` returns),
never fails, and the resolver has: `base_ip` the IP literal of the base URL (line 110,
`literal_ip`); no unfiltered host (line 123); `base_classes` the classes the base URL grants
(lines 111–120, `Defs.MetadataResolver.baseClasses`): the class of an IP literal, `[Loopback]`
for a `localhost` name, `[]` for another domain or no host; and the given `lookup` (line 125).
The policy is therefore fixed by the base URL's own host, never by what its name resolves to.
The premise is the weakest (`with_base_url_fail`). -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.with_base_url (base_url : url.Url)
    (lookup : Lookup)
    (h_utf8 : ∀ d, ExtModel.urlHost base_url = some (url.host.Host.Domain d) → ExtModel.IsUtf8
      d.val) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.with_base_url base_url lookup
      ⦃ (result : MetadataAddressResolver) =>
      result.base_ip = literalIp (ExtModel.urlHost base_url) ∧
      result.unfiltered_hosts.data.val = [] ∧
      result.base_classes.data.val = baseClasses (ExtModel.urlHost base_url) ∧
      result.lookup = lookup ⦄ :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.with_base_url_spec
    base_url lookup h_utf8

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.with_base_url' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.with_base_url

/-- **`with_base_url`, the UTF-8 premise is the weakest**: for a base URL whose domain is not
UTF-8, the call of `is_loopback_metadata_host` (patched line 121; upstream line 115) fails, so
`with_base_url` fails with `undef` (`is_loopback_metadata_host_fail`). -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.with_base_url_fail (base_url : url.Url)
    (lookup : Lookup) (d : Str) (h_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (h : ¬ ExtModel.IsUtf8 d.val) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.with_base_url base_url lookup =
      fail .undef :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.with_base_url_fail
    base_url lookup d h_host h

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.with_base_url_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.with_base_url_fail

/-! ## N05 `with_proxy_hosts` (upstream lines 131–147; patched 140–149, `proxy_host` 233–245)
-/

/-- **Spec theorem for `rmcp::transport::auth::metadata_resolver::proxy_host`** (helper of N05;
upstream lines 132–139, the `filter_map` closure; patched lines 233–245, hunk H4)

For a proxy value that fits the string models (`ProxyFits`) and whose parsed URL's host
string, if any, is UTF-8 (`ProxyHostUtf8`, rule (ii)(b)), never fails: the normalized host of
the URL `proxyUrl proxy` (the value, with `http://` in front if it has no `://`), or `none` if
that does not parse or has no host (`Defs.MetadataResolver.proxyHost`, as bytes). Both premises are
the weakest (`proxy_host_fail`, `proxy_host_fail_undef`). -/
theorem Theorems.metadata_resolver.proxy_host (proxy : String) (h_fits : ProxyFits proxy)
    (h_utf8 : ProxyHostUtf8 proxy) :
    rmcp.transport.auth.metadata_resolver.proxy_host proxy ⦃ (result : Option String) =>
      result.map Defs.utf8Bytes = proxyHost (Defs.utf8Bytes proxy) ⦄ :=
  @rmcp.transport.auth.metadata_resolver.proxy_host_spec proxy h_fits h_utf8

/--
info: 'Theorems.metadata_resolver.proxy_host' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.proxy_host

/-- **`proxy_host`, the size premise is exact for the Lean models** (memory convention): for a
value that does not fit (`¬ ProxyFits proxy`), the call fails: with `maximumSizeExceeded` if
its bytes do not fit in a slice (the model of `String::deref`, patched line 234), otherwise
with `panic` (the value has no `://` and `http://` followed by it exceeds `isize::MAX` bytes:
the capacity panic of `String::push_str`, patched line 238; upstream line 136, `format!`). -/
theorem Theorems.metadata_resolver.proxy_host_fail (proxy : String) (h : ¬ ProxyFits proxy) :
    rmcp.transport.auth.metadata_resolver.proxy_host proxy =
      fail (if proxy.utf8ByteSize ≤ Usize.max then .panic else .maximumSizeExceeded) :=
  @rmcp.transport.auth.metadata_resolver.proxy_host_fail proxy h

/--
info: 'Theorems.metadata_resolver.proxy_host_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.proxy_host_fail

/-- **`proxy_host`, the UTF-8 premise is the weakest**: for a value that fits but violates
`ProxyHostUtf8` (its URL `proxyUrl proxy` parses to some `u` with a host string `h` that is not
UTF-8), the call of `normalize_host` on `h` (patched line 244) fails, so `proxy_host` fails with
`undef` (`normalize_host_fail`). -/
theorem Theorems.metadata_resolver.proxy_host_fail_undef (proxy : String) (h_fits : ProxyFits proxy)
    (h : ¬ ProxyHostUtf8 proxy) :
    rmcp.transport.auth.metadata_resolver.proxy_host proxy = fail .undef :=
  @rmcp.transport.auth.metadata_resolver.proxy_host_fail_undef proxy h_fits h

/--
info: 'Theorems.metadata_resolver.proxy_host_fail_undef' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.proxy_host_fail_undef

/-- **Spec theorem for
`rmcp::transport::auth::metadata_resolver::MetadataAddressResolver::with_proxy_hosts`** (N05;
upstream lines 131–147, patched lines 140–149), for `proxies : Vec<String>` (the instance
`new` uses; the function is generic over `IntoIterator<Item = String>`)

If every proxy value fits the string models (`ProxyFits`), the host string of every parsed
proxy URL is UTF-8 (`ProxyHostUtf8`, rule (ii)(b)), and the unfiltered hosts with the new ones
fit in a `Vec` (`Usize.max`), never fails: the unfiltered hosts are the old ones followed, in
order, by the normalized host of each proxy value that has one (`proxyHost`; values that do not
parse or have no host are skipped, line 138); `base_ip`, `base_classes` and `lookup` are
unchanged. The premises are sufficient and each is necessary
(`proxyFits_and_proxyHostUtf8_of_with_proxy_hosts_eq_ok`, module docstring). -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.with_proxy_hosts
    (self : MetadataAddressResolver) (proxies : alloc.vec.Vec String)
    (h_fits : ∀ p ∈ proxies.val, ProxyFits p) (h_utf8 : ∀ p ∈ proxies.val, ProxyHostUtf8 p)
    (h_len : self.unfiltered_hosts.data.val.length +
      (proxies.val.filterMap (fun p => proxyHost (Defs.utf8Bytes p))).length ≤ Usize.max) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.with_proxy_hosts
      (core.iter.traits.collect.IntoIteratorVec String)
      self proxies ⦃ (result : MetadataAddressResolver) =>
      result.unfiltered_hosts.data.val.map Defs.utf8Bytes =
        self.unfiltered_hosts.data.val.map Defs.utf8Bytes ++
          proxies.val.filterMap (fun p => proxyHost (Defs.utf8Bytes p)) ∧
      result.base_ip = self.base_ip ∧
      result.base_classes = self.base_classes ∧
      result.lookup = self.lookup ⦄ :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.with_proxy_hosts_spec
    self proxies h_fits h_utf8 h_len

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.with_proxy_hosts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.with_proxy_hosts

/-- **N05, what a successful call returns** (human decision 2026-11-26, extension of T4): if
`with_proxy_hosts self proxies` returns `r`, then `r` is described as in
`with_proxy_hosts_spec`: the unfiltered hosts are the old ones followed, in order, by the
normalized host (`proxyHost`) of each proxy value that has one, and `base_ip`, `base_classes`,
`lookup` are unchanged. No premise: a successful call has passed every `deref`, `push_str`,
`normalize_host` and `push` of the loop (patched lines 140–149, 233–245), so each value fitted
and each host string was UTF-8. Covers only successful calls and does not show that the call
succeeds. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.with_proxy_hosts_of_eq_ok
    (self r : MetadataAddressResolver) (proxies : alloc.vec.Vec String)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.with_proxy_hosts
      (core.iter.traits.collect.IntoIteratorVec String) self proxies = ok r) :
    r.unfiltered_hosts.data.val.map Defs.utf8Bytes =
        self.unfiltered_hosts.data.val.map Defs.utf8Bytes ++
          proxies.val.filterMap (fun p => proxyHost (Defs.utf8Bytes p)) ∧
      r.base_ip = self.base_ip ∧ r.base_classes = self.base_classes ∧
      r.lookup = self.lookup :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.with_proxy_hosts_of_eq_ok
    self r proxies h

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.with_proxy_hosts_of_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.with_proxy_hosts_of_eq_ok

/-- **N05, the premises of `with_proxy_hosts_spec` are necessary** (finding Q2 of spec round 2):
if `with_proxy_hosts self proxies` returns `r`, every proxy value fits the string models
(`ProxyFits`) and the host string of its parsed URL, if any, is UTF-8 (`ProxyHostUtf8`). The
loop (patched lines 142–146) calls `proxy_host` on every value, in order, and a failing call
fails the loop; `proxy_host` fails exactly when one of the two is violated (`proxy_host_fail`,
`proxy_host_fail_undef`). With `with_proxy_hosts_spec`, the premises are exact at this level;
the third premise, the length bound, is necessary because the hosts of `r`
(`with_proxy_hosts_of_eq_ok`) are a `Slice`. No premise. -/
theorem
    Theorems.metadata_resolver.MetadataAddressResolver.proxyFits_and_proxyHostUtf8_of_with_proxy_hosts_eq_ok
    (self r : MetadataAddressResolver) (proxies : alloc.vec.Vec String)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.with_proxy_hosts
      (core.iter.traits.collect.IntoIteratorVec String) self proxies = ok r) :
    ∀ p ∈ proxies.val, ProxyFits p ∧ ProxyHostUtf8 p :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.proxyFits_and_proxyHostUtf8_of_with_proxy_hosts_eq_ok
    self r proxies h

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.proxyFits_and_proxyHostUtf8_of_with_proxy_hosts_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.proxyFits_and_proxyHostUtf8_of_with_proxy_hosts_eq_ok

/-! ## N06 `allowing_private_addresses` (upstream lines 150–160; patched 152–159) -/

/-- **Spec theorem for
`rmcp::transport::auth::metadata_resolver::MetadataAddressResolver::allowing_private_addresses`**
(N06)

If `Private` is already granted or there is room for one more class (`Vec::push`, patch 05 hunk
H5), never fails: `Private` is appended to the granted classes unless already present
(`withPrivate`); `base_ip`, `unfiltered_hosts` and `lookup` are unchanged. The premise is exact
for the Lean models (`allowing_private_addresses_fail`). -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.allowing_private_addresses
    (self : MetadataAddressResolver)
    (h_room : AddressClass.Private ∈ self.base_classes.data.val ∨
      self.base_classes.data.val.length < Usize.max) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowing_private_addresses self
      ⦃ (result : MetadataAddressResolver) =>
      result.base_classes.data.val = withPrivate self.base_classes.data.val ∧
      result.base_ip = self.base_ip ∧
      result.unfiltered_hosts = self.unfiltered_hosts ∧
      result.lookup = self.lookup ⦄ :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowing_private_addresses_spec
    self h_room

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allowing_private_addresses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allowing_private_addresses

/-- **`allowing_private_addresses`, the premise is exact for the Lean models** (memory
convention): without `Private` and with `Usize.max` classes already, the `push` of patched
line 155 fails with `maximumSizeExceeded` (no such slice fits in memory in Rust). -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.allowing_private_addresses_fail
    (self : MetadataAddressResolver)
    (h : ¬ (AddressClass.Private ∈ self.base_classes.data.val ∨
      self.base_classes.data.val.length < Usize.max)) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowing_private_addresses self =
      fail .maximumSizeExceeded :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowing_private_addresses_fail
    self h

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allowing_private_addresses_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allowing_private_addresses_fail

/-! ## N07 `allows_url` (upstream lines 164–172; patched 163–171) -/

/-- **Spec theorem for
`rmcp::transport::auth::metadata_resolver::MetadataAddressResolver::allows_url`** (N07)

Never fails. The policy for the target's host (`Defs.MetadataResolver.allowsHost`): `true` when
the host is not an IP literal (line 170: names are left to `resolve`); for an IP literal, `true`
exactly when it is the base URL's own literal (line 167) or its class is allowed by the granted
classes (line 168, N01 and N08). No premise. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.allows_url
    (self : MetadataAddressResolver) (target : url.Url) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allows_url self target
      ⦃ (result : Bool) =>
      result =
        allowsHost self.base_ip self.base_classes.data.val (ExtModel.urlHost target) ⦄ :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allows_url_spec self target

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allows_url' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allows_url

/-! ## N08 `is_allowed` (upstream lines 180–186) -/

/-- **Spec theorem for
`rmcp::transport::auth::metadata_resolver::MetadataAddressResolver::is_allowed`** (N08)

Never fails. `Public`: `true`; `Loopback`, `Private`: `true` exactly when the class is in
`base_classes`; `Blocked`: `false` (`Defs.MetadataResolver.isAllowed`). No premise. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.is_allowed («class» : AddressClass)
    (base_classes : Slice AddressClass) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.is_allowed «class» base_classes
      ⦃ (result : Bool) =>
      result = isAllowed «class» base_classes.val ⦄ :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.is_allowed_spec
    «class» base_classes

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.is_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.is_allowed

/-! ## N09 `resolve` (upstream lines 190–212), through `allowed_addresses` (patched 210–229) -/

/-- **Spec theorem for
`rmcp::transport::auth::metadata_resolver::MetadataAddressResolver::allowed_addresses`** (N09;
the pure part of `resolve`, upstream lines 195–210, moved by patch 05 hunk H6)

Never fails. For a host in `unfiltered_hosts` (line 195): `some` of all resolved addresses
(also none). Otherwise: the resolved addresses whose class (N01) is allowed by
`base_classes` (N08), in order (lines 199–202), or `none` if there is none (lines 203–209,
where the async shell returns the error) (`Defs.MetadataResolver.allowedAddresses`). No
premise. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.allowed_addresses
    (self : MetadataAddressResolver) (host : String)
    (resolved : alloc.vec.Vec core.net.socket_addr.SocketAddr) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowed_addresses self host
      resolved
      ⦃ (result : Option (alloc.vec.Vec core.net.socket_addr.SocketAddr)) =>
      result.map (fun v => v.val) =
        allowedAddresses self.unfiltered_hosts.data.val self.base_classes.data.val host
          resolved.val ⦄ :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowed_addresses_spec
    self host resolved

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allowed_addresses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allowed_addresses

/-! ## N10 `literal_ip` (upstream lines 215–221; patched 247–253) -/

/-- **Spec theorem for `rmcp::transport::auth::metadata_resolver::literal_ip`** (N10)

Never fails. The IP address of the URL's host if it is an IPv4 or IPv6 literal, `none` for a
domain or no host (`Defs.MetadataResolver.literalIp` of `ExtModel.urlHost target`). No
premise. -/
theorem Theorems.metadata_resolver.literal_ip (target : url.Url) :
    rmcp.transport.auth.metadata_resolver.literal_ip target
      ⦃ (result : Option core.net.ip_addr.IpAddr) =>
      result = literalIp (ExtModel.urlHost target) ⦄ :=
  @rmcp.transport.auth.metadata_resolver.literal_ip_spec target

/--
info: 'Theorems.metadata_resolver.literal_ip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.literal_ip

/-! ## N11 `normalize_host` (upstream lines 223–225; patched 255–257) -/

/-- **Spec theorem for `rmcp::transport::auth::metadata_resolver::normalize_host`** (N11)

For a UTF-8 `host` (rule (ii)(a), the `&str` argument), never fails: the string whose bytes are
those of `host` without trailing `.` bytes, with ASCII letters lowercased
(`Defs.MetadataResolver.normalizeHost`). The premise is the weakest (`normalize_host_fail`). -/
theorem Theorems.metadata_resolver.normalize_host (host : Str) (h_utf8 : ExtModel.IsUtf8 host.val) :
    rmcp.transport.auth.metadata_resolver.normalize_host host ⦃ (result : String) =>
      Defs.utf8Bytes result = normalizeHost host.val ⦄ :=
  @rmcp.transport.auth.metadata_resolver.normalize_host_spec host h_utf8

/--
info: 'Theorems.metadata_resolver.normalize_host' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.normalize_host

/-- **N11, the UTF-8 premise is the weakest**: on bytes that are not UTF-8 (no Rust `&str`), the
model of `to_ascii_lowercase` fails, so `normalize_host` fails with `undef`. The proof needs the
converse of the lemmas `Proofs.External.MetadataResolver.isUtf8_dropTrailingDots` and
`Proofs.External.MetadataResolver.isUtf8_map_asciiLowercase` (module
`Proofs.External.MetadataResolver`; lead decision 2026-11-26: the proof effort is accepted):
`IsUtf8 (dropTrailingDots l) → IsUtf8 l` (the removed bytes are ASCII `.`) and
`IsUtf8 (l.map asciiLowercase) → IsUtf8 l` (the map changes only ASCII letters, into ASCII
letters), and that `ExtModel.strOfBytes? l = none` when `¬ IsUtf8 l`. -/
theorem Theorems.metadata_resolver.normalize_host_fail (host : Str)
    (h : ¬ ExtModel.IsUtf8 host.val) :
    rmcp.transport.auth.metadata_resolver.normalize_host host = fail .undef :=
  @rmcp.transport.auth.metadata_resolver.normalize_host_fail host h

/--
info: 'Theorems.metadata_resolver.normalize_host_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.normalize_host_fail

/-! ## Laws of the definitions

About `Defs.utf8Bytes` and `Defs.MetadataResolver` only (no translated function); they say what
the policy means and are what the composition theorems below reduce to. None is tagged
`@[step]`. -/

/-! ### Strings and their bytes (finding Q8 of spec round 2; finding R5 of spec round 3)

Library facts about `Defs.utf8Bytes`, stated in `Defs.MetadataResolver` (not in the signed-off
namespace `Defs`) because only these statements use them. Neither is a new claim: each is
derived here, in one line, from an existing proved theorem. -/

/-- **Distinct strings have distinct UTF-8 bytes** (`String::as_bytes` is the identity on the
bytes of a Rust `String`). The bridge between the `String` hosts that `allowed_addresses`
compares (upstream line 195) and the byte hosts that `proxyHost` computes. Not a new
statement: `Proofs.External.Utf8.utf8_injective` (`formal/proofs/Proofs/External/String.lean`
line 130, restated as `Theorems.External.Utf8.utf8_injective`), read through
`Proofs.External.Utf8.utf8Bytes_eq_utf8` (line 74, `Defs.utf8Bytes s = ExtModel.utf8 s` by
`rfl`). Proved as `Defs.MetadataResolver.utf8Bytes_injective` in
`Proofs/Transport/MetadataResolver.lean`. -/
theorem Theorems.metadata_resolver.utf8Bytes_injective : Function.Injective Defs.utf8Bytes :=
  Defs.MetadataResolver.utf8Bytes_injective

/--
info: 'Theorems.metadata_resolver.utf8Bytes_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.utf8Bytes_injective

/-- **A string is in a list exactly when its bytes are in the list of their bytes**: Mathlib's
`List.mem_map_of_injective` with `utf8Bytes_injective`. Proved as
`Defs.MetadataResolver.utf8Bytes_mem_map_iff` in `Proofs/Transport/MetadataResolver.lean`. -/
theorem Theorems.metadata_resolver.utf8Bytes_mem_map_iff {hosts : List String} {host : String} :
    Defs.utf8Bytes host ∈ hosts.map Defs.utf8Bytes ↔ host ∈ hosts :=
  @Defs.MetadataResolver.utf8Bytes_mem_map_iff hosts host

/--
info: 'Theorems.metadata_resolver.utf8Bytes_mem_map_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.utf8Bytes_mem_map_iff

/-! ### The policy check (N08) -/

/-- **A public address is always allowed** (upstream line 182), whatever the granted classes. -/
theorem Theorems.metadata_resolver.isAllowed_public (base : List AddressClass) :
    isAllowed .Public base = true :=
  @Defs.MetadataResolver.isAllowed_public base

/--
info: 'Theorems.metadata_resolver.isAllowed_public' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.isAllowed_public

/-- **A blocked address is never allowed** (upstream line 184), whatever the granted classes. -/
theorem Theorems.metadata_resolver.isAllowed_blocked (base : List AddressClass) :
    isAllowed .Blocked base = false :=
  @Defs.MetadataResolver.isAllowed_blocked base

/--
info: 'Theorems.metadata_resolver.isAllowed_blocked' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.isAllowed_blocked

/-- **Granting more classes never refuses more** (upstream line 183: membership in
`base_classes`). -/
theorem Theorems.metadata_resolver.isAllowed_mono {base base' : List AddressClass}
    (h_sub : base ⊆ base') {c : AddressClass} (h : isAllowed c base = true) :
    isAllowed c base' = true :=
  @Defs.MetadataResolver.isAllowed_mono base base' h_sub c h

/--
info: 'Theorems.metadata_resolver.isAllowed_mono' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.isAllowed_mono

/-- **Without `Loopback` and `Private` granted, only public addresses are allowed** (upstream
lines 181–185). This is the case of a base URL that names a domain other than a `localhost`
name, a public or blocked IP literal, or no host (`loopback_mem_baseClasses_iff`,
`private_mem_baseClasses_iff`). -/
theorem Theorems.metadata_resolver.eq_public_of_isAllowed {base : List AddressClass}
    (h_loopback : AddressClass.Loopback ∉ base) (h_private : AddressClass.Private ∉ base)
    {c : AddressClass} (h : isAllowed c base = true) : c = .Public :=
  @Defs.MetadataResolver.eq_public_of_isAllowed base h_loopback h_private c h

/--
info: 'Theorems.metadata_resolver.eq_public_of_isAllowed' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.eq_public_of_isAllowed

/-! ### The policy for an IP-literal target (N07) -/

/-- **The base URL's own host is always allowed** (doc comment of `allows_url`, upstream lines
162–163: "The base URL's own literal is always allowed"; line 167: `self.base_ip == Some(ip)`;
line 170: a host without an IP literal is allowed): a target with the host of the base URL is
allowed by the base URL's literal, whatever the granted classes, also when its literal is
`Blocked`. -/
theorem Theorems.metadata_resolver.allowsHost_literalIp_self (base : List AddressClass)
    (host : Option (url.host.Host Str)) :
    allowsHost (literalIp host) base host = true :=
  @Defs.MetadataResolver.allowsHost_literalIp_self base host

/--
info: 'Theorems.metadata_resolver.allowsHost_literalIp_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.allowsHost_literalIp_self

/-! ### The classes a base URL grants (N04) -/

/-- **A base URL grants `Loopback` exactly through its own host** (module docstring, upstream
lines 4–7; lines 111–120): a loopback IP literal (also embedded in IPv6) or a `localhost`
name. -/
theorem Theorems.metadata_resolver.loopback_mem_baseClasses_iff (host : Option (url.host.Host Str))
  :
    AddressClass.Loopback ∈ baseClasses host ↔
      (∃ ip, literalIp host = some ip ∧ addressClass ip = .Loopback) ∨
        ∃ d, host = some (url.host.Host.Domain d) ∧ isLocalhostName d.val = true :=
  @Defs.MetadataResolver.loopback_mem_baseClasses_iff host

/--
info: 'Theorems.metadata_resolver.loopback_mem_baseClasses_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.loopback_mem_baseClasses_iff

/-- **A base URL grants `Private` exactly when its host is a private IP literal** (also
embedded in IPv6; module docstring, upstream lines 4–7; lines 111–120). -/
theorem Theorems.metadata_resolver.private_mem_baseClasses_iff (host : Option (url.host.Host Str)) :
    AddressClass.Private ∈ baseClasses host ↔
      ∃ ip, literalIp host = some ip ∧ addressClass ip = .Private :=
  @Defs.MetadataResolver.private_mem_baseClasses_iff host

/--
info: 'Theorems.metadata_resolver.private_mem_baseClasses_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.private_mem_baseClasses_iff

/-- **A base URL grants at most one class** (upstream lines 112–119: each arm builds a vector of
at most one element). -/
theorem Theorems.metadata_resolver.length_baseClasses_le_one (host : Option (url.host.Host Str)) :
    (baseClasses host).length ≤ 1 :=
  @Defs.MetadataResolver.length_baseClasses_le_one host

/--
info: 'Theorems.metadata_resolver.length_baseClasses_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.length_baseClasses_le_one

/-! ### The address filter (N09) -/

/-- **`resolve` returns a sublist of the resolved addresses** (in order; upstream lines 196,
199–202). -/
theorem Theorems.metadata_resolver.allowedAddresses_sublist {unfiltered : List String}
    {base : List AddressClass} {host : String} {resolved v : List core.net.socket_addr.SocketAddr}
    (h : allowedAddresses unfiltered base host resolved = some v) : v.Sublist resolved :=
  @Defs.MetadataResolver.allowedAddresses_sublist unfiltered base host resolved v h

/--
info: 'Theorems.metadata_resolver.allowedAddresses_sublist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.allowedAddresses_sublist

/-- **An unfiltered host gets every resolved address** (upstream lines 195–197), also none. -/
theorem Theorems.metadata_resolver.allowedAddresses_eq_some_of_mem {unfiltered : List String}
    (base : List AddressClass) {host : String} (resolved : List core.net.socket_addr.SocketAddr)
    (h : host ∈ unfiltered) : allowedAddresses unfiltered base host resolved = some resolved :=
  @Defs.MetadataResolver.allowedAddresses_eq_some_of_mem unfiltered base host resolved h

/--
info: 'Theorems.metadata_resolver.allowedAddresses_eq_some_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.allowedAddresses_eq_some_of_mem

/-- **A filtered host fails exactly when no resolved address is allowed** (upstream lines
199–209; `none` is the error of the async shell). -/
theorem Theorems.metadata_resolver.allowedAddresses_eq_none_iff {unfiltered : List String}
    (base : List AddressClass) {host : String} (resolved : List core.net.socket_addr.SocketAddr)
    (h : host ∉ unfiltered) :
    allowedAddresses unfiltered base host resolved = none ↔
      ∀ a ∈ resolved, isAllowed (addressClass (socketIp a)) base = false :=
  @Defs.MetadataResolver.allowedAddresses_eq_none_iff unfiltered base host resolved h

/--
info: 'Theorems.metadata_resolver.allowedAddresses_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.allowedAddresses_eq_none_iff

/-- **The resolve invariant**: every address returned for a filtered host is allowed by the
granted classes (`AllAllowed`, the check of upstream line 201). -/
theorem Theorems.metadata_resolver.allAllowed_of_allowedAddresses_eq_some {unfiltered : List String}
    {base : List AddressClass} {host : String} {resolved v : List core.net.socket_addr.SocketAddr}
    (h : allowedAddresses unfiltered base host resolved = some v) (h_host : host ∉ unfiltered) :
    AllAllowed base v :=
  @Defs.MetadataResolver.allAllowed_of_allowedAddresses_eq_some
    unfiltered base host resolved v h h_host

/--
info: 'Theorems.metadata_resolver.allAllowed_of_allowedAddresses_eq_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.allAllowed_of_allowedAddresses_eq_some

/-- **No blocked address is returned for a filtered host** (module docstring, upstream lines
8–9: link-local, unspecified, broadcast, multicast and reserved addresses are never allowed),
whatever the granted classes; corollary of `allAllowed_of_allowedAddresses_eq_some` and
`isAllowed_blocked`. -/
theorem Theorems.metadata_resolver.addressClass_ne_blocked_of_mem_allowedAddresses
    {unfiltered : List String} {base : List AddressClass} {host : String}
    {resolved v : List core.net.socket_addr.SocketAddr}
    (h : allowedAddresses unfiltered base host resolved = some v) (h_host : host ∉ unfiltered)
    {a : core.net.socket_addr.SocketAddr} (ha : a ∈ v) :
    addressClass (socketIp a) ≠ .Blocked :=
  @Defs.MetadataResolver.addressClass_ne_blocked_of_mem_allowedAddresses
    unfiltered base host resolved v h h_host a ha

/--
info: 'Theorems.metadata_resolver.addressClass_ne_blocked_of_mem_allowedAddresses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.addressClass_ne_blocked_of_mem_allowedAddresses

/-! ### Host normalization (N11) -/

/-- **Normalization is idempotent** (upstream line 224). -/
theorem Theorems.metadata_resolver.normalizeHost_idem (host : List U8) :
    normalizeHost (normalizeHost host) = normalizeHost host :=
  @Defs.MetadataResolver.normalizeHost_idem host

/--
info: 'Theorems.metadata_resolver.normalizeHost_idem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.normalizeHost_idem

/-- **A trailing `.` does not change the normalized host** (`trim_end_matches('.')`, upstream
line 224). -/
theorem Theorems.metadata_resolver.normalizeHost_append_dot (host : List U8) :
    normalizeHost (host ++ [dotByte]) = normalizeHost host :=
  @Defs.MetadataResolver.normalizeHost_append_dot host

/--
info: 'Theorems.metadata_resolver.normalizeHost_append_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.normalizeHost_append_dot

/-- **ASCII case does not change the normalized host** (`to_ascii_lowercase`, upstream line
224). -/
theorem Theorems.metadata_resolver.normalizeHost_map_asciiToLower (host : List U8) :
    normalizeHost (host.map asciiToLower) = normalizeHost host :=
  @Defs.MetadataResolver.normalizeHost_map_asciiToLower host

/--
info: 'Theorems.metadata_resolver.normalizeHost_map_asciiToLower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.normalizeHost_map_asciiToLower

/-- **A `localhost` name stays one under normalization**, and another name stays another
(`auth.rs` lines 1403–1406 normalize first). -/
theorem Theorems.metadata_resolver.isLocalhostName_normalizeHost (host : List U8) :
    isLocalhostName (normalizeHost host) = isLocalhostName host :=
  @Defs.MetadataResolver.isLocalhostName_normalizeHost host

/--
info: 'Theorems.metadata_resolver.isLocalhostName_normalizeHost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.isLocalhostName_normalizeHost

/-! ## Composition theorems and invariants

About the translated functions named in each statement. None is tagged `@[step]`. -/

/-! ### Classes (N01 with A01) -/

/-- **N01 ∘ A01**: an IPv6 address that carries the IPv4 address `w` (`embedded_ipv4` returns
`some w`) has the class of `w` (upstream lines 43–48), so a loopback, private or blocked IPv4
address keeps its class in IPv4-mapped, NAT64, IPv4-compatible or 6to4 form. An equation
between computations; covers only a call of `embedded_ipv4` that returns `some w` (the suffix
`_some` distinguishes it from the case `ok none`). -/
theorem Theorems.metadata_resolver.AddressClass.of_v6_eq_of_embedded_ipv4_eq_ok_some
    (a : core.net.ip_addr.Ipv6Addr) (w : core.net.ip_addr.Ipv4Addr)
    (h : rmcp.transport.auth.AuthorizationManager.embedded_ipv4 a = ok (some w)) :
    rmcp.transport.auth.metadata_resolver.AddressClass.of (.V6 a) =
      rmcp.transport.auth.metadata_resolver.AddressClass.of (.V4 w) :=
  @rmcp.transport.auth.metadata_resolver.AddressClass.of_v6_eq_of_embedded_ipv4_eq_ok_some a w h

/--
info: 'Theorems.metadata_resolver.AddressClass.of_v6_eq_of_embedded_ipv4_eq_ok_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.AddressClass.of_v6_eq_of_embedded_ipv4_eq_ok_some

/-! ### Builders (N03, N05, N06) -/

/-- **N05, the unfiltered hosts stay normalized**: if the unfiltered hosts of `self` are
normalized (`HostsNormalized`), so are those of the resolver that `with_proxy_hosts self
proxies` returns (the new ones are `normalize_host` results, upstream line 138, and
normalization is idempotent). So the membership test of `resolve` (line 195), which normalizes
the name first (line 193), exempts exactly the names that normalize to a stored host. Covers
only successful calls. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.hostsNormalized_of_with_proxy_hosts_eq_ok
    (self r : MetadataAddressResolver) (proxies : alloc.vec.Vec String)
    (h_self : HostsNormalized self.unfiltered_hosts.data.val)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.with_proxy_hosts
      (core.iter.traits.collect.IntoIteratorVec String) self proxies = ok r) :
    HostsNormalized r.unfiltered_hosts.data.val :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.hostsNormalized_of_with_proxy_hosts_eq_ok
    self r proxies h_self h

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.hostsNormalized_of_with_proxy_hosts_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.hostsNormalized_of_with_proxy_hosts_eq_ok

/-- **N03, the unfiltered hosts are normalized** (`HostsNormalized`): for the resolver that
`new base_url` returns, for every value of `ExtModel.proxyEnvValues`. Covers only successful
calls. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.hostsNormalized_of_new_eq_ok
    (base_url : url.Url) (r : MetadataAddressResolver)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new base_url = ok r) :
    HostsNormalized r.unfiltered_hosts.data.val :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.hostsNormalized_of_new_eq_ok
    base_url r h

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.hostsNormalized_of_new_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.hostsNormalized_of_new_eq_ok

/-- **N03, membership in the unfiltered hosts** (finding Q8 of spec round 2): for the resolver
that `new base_url` returns, a `String` is an unfiltered host (the test of upstream line 195)
exactly when its UTF-8 bytes are the normalized host (`proxyHost`) of one of the proxy values
`new` reads (`ExtModel.proxyEnvValues`, upstream lines 102–106); from
`new_unfiltered_hosts_of_eq_ok` and `Defs.MetadataResolver.utf8Bytes_mem_map_iff`. Covers only
successful calls. No premise. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.mem_unfiltered_hosts_iff_of_new_eq_ok
    (base_url : url.Url) (r : MetadataAddressResolver)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new base_url = ok r)
    (host : String) :
    host ∈ r.unfiltered_hosts.data.val ↔
      Defs.utf8Bytes host ∈
        ExtModel.proxyEnvValues.val.filterMap (proxyHost ∘ Defs.utf8Bytes) :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.mem_unfiltered_hosts_iff_of_new_eq_ok
    base_url r h host

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.mem_unfiltered_hosts_iff_of_new_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.mem_unfiltered_hosts_iff_of_new_eq_ok

/-- **N06 then N08**: after `allowing_private_addresses`, a class is allowed exactly when it was
allowed before or it is `Private`; in particular the loopback policy is unchanged and blocked
addresses stay refused. Covers only a successful call of `allowing_private_addresses`. -/
theorem
    Theorems.metadata_resolver.MetadataAddressResolver.is_allowed_of_allowing_private_addresses_eq_ok
    (self r : MetadataAddressResolver)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowing_private_addresses
      self = ok r)
    (c : AddressClass) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.is_allowed c r.base_classes.data
      ⦃ (result : Bool) =>
      result = (isAllowed c self.base_classes.data.val || decide (c = .Private)) ⦄ :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.is_allowed_of_allowing_private_addresses_eq_ok
    self r h c

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.is_allowed_of_allowing_private_addresses_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.is_allowed_of_allowing_private_addresses_eq_ok

/-- **N06 is idempotent**: calling `allowing_private_addresses` twice is calling it once (the
second call finds `Private` and returns its argument, line 151). An equation between
computations, failure included. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.allowing_private_addresses_idem
    (self : MetadataAddressResolver) :
    (do
      let r ←
        rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowing_private_addresses
          self
      rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowing_private_addresses r) =
      rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowing_private_addresses
        self :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowing_private_addresses_idem
    self

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allowing_private_addresses_idem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allowing_private_addresses_idem

/-- **N03 then N06, `new_allowing_private_addresses` builds its resolver whenever `new` does**
(`auth.rs` line 1527: `new(&base_url).allowing_private_addresses()`; finding R3 of spec round 3):
if `new base_url` returns `r₀`, then `allowing_private_addresses r₀` succeeds. The base URL
grants at most one class (`new_fields_of_eq_ok`, `length_baseClasses_le_one`, upstream lines
112–119), so the premise of `allowing_private_addresses_spec` (patched line 155) holds. With
`new base_url = ok r₀` this discharges the hypothesis
`(do let r₀ ← new base_url; allowing_private_addresses r₀) = ok r` of the four
`…_of_new_allowing_private_addresses_eq_ok` theorems. Covers only a successful call of `new`.
No premise. -/
theorem
    Theorems.metadata_resolver.MetadataAddressResolver.exists_allowing_private_addresses_eq_ok_of_new_eq_ok
    (base_url : url.Url) (r₀ : MetadataAddressResolver)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new base_url = ok r₀) :
    ∃ r,
      rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowing_private_addresses r₀ =
        ok r :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.exists_allowing_private_addresses_eq_ok_of_new_eq_ok
    base_url r₀ h

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.exists_allowing_private_addresses_eq_ok_of_new_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.exists_allowing_private_addresses_eq_ok_of_new_eq_ok

/-! ### `allows_url` (N07 with N03, N04, N06, N10)

The checks of every OAuth request (`execute`, `auth.rs` line 193) and of every redirect (the
redirect policy, line 160), on the resolver of `AuthorizationManager::new` (line 1513) or of
`new_allowing_private_addresses` (line 1527). -/

/-- **N04 then N07, the base URL's own literal is always allowed** (doc comment, upstream lines
162–163): the resolver built from `base_url` allows `base_url` itself, whatever its class (also
a blocked one, such as a link-local literal). Covers only a successful call of
`with_base_url`. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.allows_url_self_of_with_base_url_eq_ok
    (base_url : url.Url) (lookup : Lookup) (r : MetadataAddressResolver)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.with_base_url base_url lookup
      = ok r) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allows_url r base_url = ok true :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allows_url_self_of_with_base_url_eq_ok
    base_url lookup r h

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allows_url_self_of_with_base_url_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allows_url_self_of_with_base_url_eq_ok

/-- **N03 then N07, the base URL itself is always allowed in production**
(`AuthorizationManager::new`, `auth.rs` line 1513; the checks of the redirect policy, line 160,
and of `execute`, line 193; doc comment of `allows_url`, upstream lines 162–163, and line 167):
the resolver that `new base_url` returns allows `base_url` itself, whatever its host and class
(also a blocked literal, such as a link-local one), for every value of
`ExtModel.proxyEnvValues`. From `allows_url_of_new_eq_ok` and `allowsHost_literalIp_self`.
Covers only a successful call of `new`. No premise. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.allows_url_self_of_new_eq_ok
    (base_url : url.Url) (r : MetadataAddressResolver)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new base_url = ok r) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allows_url r base_url = ok true :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allows_url_self_of_new_eq_ok
    base_url r h

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allows_url_self_of_new_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allows_url_self_of_new_eq_ok

/-- **N04 then N07, a public base name allows only public literals**: for a base URL whose host
is a domain other than a `localhost` name, the resolver allows a target exactly when its host
is not an IP literal or the literal is `Public` (loopback, private and blocked literals,
including embedded ones, are refused; for `Public`, see the header). Covers only a successful
call of `with_base_url`. -/
theorem
    Theorems.metadata_resolver.MetadataAddressResolver.allows_url_iff_public_of_with_base_url_eq_ok
    (base_url : url.Url) (lookup : Lookup) (r : MetadataAddressResolver) (d : Str)
    (h_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (h_name : isLocalhostName d.val = false)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.with_base_url base_url lookup
      = ok r)
    (target : url.Url) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allows_url r target
      ⦃ (result : Bool) =>
      (result = true ↔
        ∀ ip, literalIp (ExtModel.urlHost target) = some ip →
          addressClass ip = .Public) ⦄ :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allows_url_iff_public_of_with_base_url_eq_ok
    base_url lookup r d h_host h_name h target

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allows_url_iff_public_of_with_base_url_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allows_url_iff_public_of_with_base_url_eq_ok

/-- **N03 then N07, the policy of `AuthorizationManager::new`** (`auth.rs` line 1513; the checks
of lines 160 and 193): the resolver that `new base_url` returns decides a target by the base
URL's own literal and the classes the base URL grants (`allowsHost` with `literalIp` and
`baseClasses` of the base URL's host), for every value of `ExtModel.proxyEnvValues` (the proxy
values change only the unfiltered hosts). Covers only a successful call of `new`. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.allows_url_of_new_eq_ok
    (base_url : url.Url) (r : MetadataAddressResolver)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new base_url = ok r)
    (target : url.Url) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allows_url r target
      ⦃ (result : Bool) =>
      result = allowsHost (literalIp (ExtModel.urlHost base_url))
        (baseClasses (ExtModel.urlHost base_url)) (ExtModel.urlHost target) ⦄ :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allows_url_of_new_eq_ok
    base_url r h target

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allows_url_of_new_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allows_url_of_new_eq_ok

/-- **N03 then N07, a public base name allows only public literals in production**
(`AuthorizationManager::new`, `auth.rs` line 1513; the checks of lines 160 and 193): for a base
URL whose host is a domain other than a `localhost` name, the resolver that `new base_url`
returns allows a target exactly when its host is not an IP literal or the literal is `Public`.
For `Public`, see the header. For every value of `ExtModel.proxyEnvValues`. Covers only a
successful call of `new`. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.allows_url_iff_public_of_new_eq_ok
    (base_url : url.Url) (r : MetadataAddressResolver) (d : Str)
    (h_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (h_name : isLocalhostName d.val = false)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new base_url = ok r)
    (target : url.Url) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allows_url r target
      ⦃ (result : Bool) =>
      (result = true ↔
        ∀ ip, literalIp (ExtModel.urlHost target) = some ip →
          addressClass ip = .Public) ⦄ :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allows_url_iff_public_of_new_eq_ok
    base_url r d h_host h_name h target

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allows_url_iff_public_of_new_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allows_url_iff_public_of_new_eq_ok

/-- **N03, N06 then N07, the policy of `new_allowing_private_addresses`** (`auth.rs` line 1527:
`new(&base_url).allowing_private_addresses()`; the checks of lines 160 and 193): the resolver
decides a target by the base URL's own literal and the classes the base URL grants with
`Private` added (`withPrivate`, upstream lines 150–160), for every value of
`ExtModel.proxyEnvValues`. Covers only a successful call of the composition. -/
theorem
    Theorems.metadata_resolver.MetadataAddressResolver.allows_url_of_new_allowing_private_addresses_eq_ok
    (base_url : url.Url) (r : MetadataAddressResolver) (h : (do
      let r₀ ← rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new base_url
      rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowing_private_addresses r₀) =
        ok r)
    (target : url.Url) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allows_url r target
      ⦃ (result : Bool) =>
      result = allowsHost (literalIp (ExtModel.urlHost base_url))
        (withPrivate (baseClasses (ExtModel.urlHost base_url))) (ExtModel.urlHost target) ⦄ :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allows_url_of_new_allowing_private_addresses_eq_ok
    base_url r h target

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allows_url_of_new_allowing_private_addresses_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allows_url_of_new_allowing_private_addresses_eq_ok

/-- **N03, N06 then N07, a public base name allows public and private literals only**
(`new_allowing_private_addresses`, `auth.rs` line 1527; the checks of lines 160 and 193): for a
base URL whose host is a domain other than a `localhost` name, the resolver allows a target
exactly when its host is not an IP literal or the literal is `Public` or `Private` (loopback
and blocked literals, including embedded ones, are refused; for `Public`, see the header). For
every value of `ExtModel.proxyEnvValues`. Covers only a successful call of the composition. -/
theorem
    Theorems.metadata_resolver.MetadataAddressResolver.allows_url_iff_public_or_private_of_new_allowing_private_addresses_eq_ok
    (base_url : url.Url) (r : MetadataAddressResolver) (d : Str)
    (h_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (h_name : isLocalhostName d.val = false) (h : (do
      let r₀ ← rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new base_url
      rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowing_private_addresses r₀) =
        ok r)
    (target : url.Url) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allows_url r target
      ⦃ (result : Bool) =>
      (result = true ↔
        ∀ ip, literalIp (ExtModel.urlHost target) = some ip →
          addressClass ip = .Public ∨ addressClass ip = .Private) ⦄ :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allows_url_iff_public_or_private_of_new_allowing_private_addresses_eq_ok
    base_url r d h_host h_name h target

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allows_url_iff_public_or_private_of_new_allowing_private_addresses_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allows_url_iff_public_or_private_of_new_allowing_private_addresses_eq_ok

/-- **N07 refuses blocked literals**: a target whose IP literal is `Blocked` and is not the
base URL's own literal is refused, whatever the granted classes. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.allows_url_eq_false_of_blocked
    (self : MetadataAddressResolver) (target : url.Url) (ip : core.net.ip_addr.IpAddr)
    (h_ip : literalIp (ExtModel.urlHost target) = some ip) (h_blocked : addressClass ip = .Blocked)
    (h_base : self.base_ip ≠ some ip) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allows_url self target
      ⦃ (result : Bool) => result = false ⦄ :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allows_url_eq_false_of_blocked
    self target ip h_ip h_blocked h_base

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allows_url_eq_false_of_blocked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allows_url_eq_false_of_blocked

/-! ### `resolve` (N09 with N01, N08, N03, N04, N06)

Every name that an OAuth request or redirect resolves goes through `resolve` (upstream lines
190–212), whose pure part is `allowed_addresses`. -/

/-- **N09: every address returned for a filtered host passes `is_allowed`**: if
`allowed_addresses` returns `some v` for a host that is not unfiltered, then for every address
`a` of `v`, `is_allowed (AddressClass::of a.ip()) base_classes` returns `true` (the check of
upstream line 201). Covers only a successful call of `allowed_addresses` returning `some`. -/
theorem
    Theorems.metadata_resolver.MetadataAddressResolver.is_allowed_of_mem_of_allowed_addresses_eq_ok
    (self : MetadataAddressResolver) (host : String)
    (resolved v : alloc.vec.Vec core.net.socket_addr.SocketAddr)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowed_addresses self host
      resolved = ok (some v))
    (h_host : host ∉ self.unfiltered_hosts.data.val) (a : core.net.socket_addr.SocketAddr)
    (ha : a ∈ v.val) :
    (do
      let ip ← core.net.socket_addr.SocketAddr.ip a
      let c ← rmcp.transport.auth.metadata_resolver.AddressClass.of ip
      rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.is_allowed c
        self.base_classes.data) = ok true :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.is_allowed_of_mem_of_allowed_addresses_eq_ok
    self host resolved v h h_host a ha

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.is_allowed_of_mem_of_allowed_addresses_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.is_allowed_of_mem_of_allowed_addresses_eq_ok

/-- **N04 then N09, a public base name lets only public addresses through** (module docstring,
lines 4–7: "the base host's DNS answers never widen the policy"): for the resolver built by
`with_base_url` from a base URL whose host is a domain other than a `localhost` name, every
address `allowed_addresses` returns is `Public` (`AllPublic`; there is no unfiltered host before
`with_proxy_hosts`). For `Public`, see the header. Covers
only successful calls of `with_base_url` and of `allowed_addresses` returning `some`. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.allPublic_of_with_base_url_eq_ok
    (base_url : url.Url) (lookup : Lookup) (r : MetadataAddressResolver) (d : Str)
    (h_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (h_name : isLocalhostName d.val = false)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.with_base_url base_url lookup
      = ok r)
    (host : String) (resolved v : alloc.vec.Vec core.net.socket_addr.SocketAddr)
    (h_res : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowed_addresses r host
      resolved = ok (some v)) :
    AllPublic v.val :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allPublic_of_with_base_url_eq_ok
    base_url lookup r d h_host h_name h host resolved v h_res

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allPublic_of_with_base_url_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allPublic_of_with_base_url_eq_ok

/-- **N03 then N09, the addresses `AuthorizationManager::new` lets through**
(`auth.rs` line 1513): for the resolver that `new base_url` builds, every address
`allowed_addresses` returns for a host that is not a configured proxy host is allowed by the
classes the base URL grants (`AllAllowed` of `baseClasses`), for every value of
`ExtModel.proxyEnvValues`. Covers only successful calls of `new` and of `allowed_addresses`
returning `some`. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.allAllowed_of_new_eq_ok
    (base_url : url.Url) (r : MetadataAddressResolver)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new base_url = ok r)
    (host : String) (h_unfiltered : host ∉ r.unfiltered_hosts.data.val)
    (resolved v : alloc.vec.Vec core.net.socket_addr.SocketAddr)
    (h_res : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowed_addresses r host
      resolved = ok (some v)) :
    AllAllowed (baseClasses (ExtModel.urlHost base_url)) v.val :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allAllowed_of_new_eq_ok
    base_url r h host h_unfiltered resolved v h_res

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allAllowed_of_new_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allAllowed_of_new_eq_ok

/-- **N03 then N09, the production guarantee of `AuthorizationManager::new`** (module
docstring, lines 4–11; `auth.rs` line 1513): for the resolver that `new base_url` builds, from
a base URL whose host is a domain other than a `localhost` name, every address
`allowed_addresses` returns for a host that is not a configured proxy host is `Public`
(`AllPublic`), for every value of `ExtModel.proxyEnvValues`. For `Public`, see the header. The
premise on the base host is the production case; by
`eq_public_of_isAllowed` the same holds whenever the base URL grants neither `Loopback` nor
`Private` (also a public or blocked IP literal, or no host). No UTF-8 premise: a successful
`new` has checked the base domain. Covers only successful calls of `new` and of
`allowed_addresses` returning `some`. -/
theorem Theorems.metadata_resolver.MetadataAddressResolver.allPublic_of_new_eq_ok
    (base_url : url.Url) (r : MetadataAddressResolver) (d : Str)
    (h_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (h_name : isLocalhostName d.val = false)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new base_url = ok r)
    (host : String) (h_unfiltered : host ∉ r.unfiltered_hosts.data.val)
    (resolved v : alloc.vec.Vec core.net.socket_addr.SocketAddr)
    (h_res : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowed_addresses r host
      resolved = ok (some v)) :
    AllPublic v.val :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allPublic_of_new_eq_ok
    base_url r d h_host h_name h host h_unfiltered resolved v h_res

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allPublic_of_new_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allPublic_of_new_eq_ok

/-- **N03, N06 then N09, the addresses `new_allowing_private_addresses` lets through**
(`auth.rs` line 1527: `new(&base_url).allowing_private_addresses()`): for that resolver, every
address `allowed_addresses` returns for a host that is not a configured proxy host is allowed by
the classes the base URL grants with `Private` added (`AllAllowed` of `withPrivate`): `Public`,
`Private`, and `Loopback` only if the base URL grants it (`loopback_mem_baseClasses_iff`);
never `Blocked`. For every value of `ExtModel.proxyEnvValues`. Covers only successful calls of
the composition and of `allowed_addresses` returning `some`. -/
theorem
    Theorems.metadata_resolver.MetadataAddressResolver.allAllowed_of_new_allowing_private_addresses_eq_ok
    (base_url : url.Url) (r : MetadataAddressResolver) (h : (do
      let r₀ ← rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new base_url
      rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowing_private_addresses r₀) =
        ok r)
    (host : String) (h_unfiltered : host ∉ r.unfiltered_hosts.data.val)
    (resolved v : alloc.vec.Vec core.net.socket_addr.SocketAddr)
    (h_res : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowed_addresses r host
      resolved = ok (some v)) :
    AllAllowed (withPrivate (baseClasses (ExtModel.urlHost base_url))) v.val :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allAllowed_of_new_allowing_private_addresses_eq_ok
    base_url r h host h_unfiltered resolved v h_res

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allAllowed_of_new_allowing_private_addresses_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allAllowed_of_new_allowing_private_addresses_eq_ok

/-- **N03, N06 then N09, the production guarantee of `new_allowing_private_addresses`**
(`auth.rs` line 1527; its doc comment, lines 1517–1521: "Loopback addresses still need a
loopback base URL, and link-local and other reserved addresses stay rejected"): from a base URL
whose host is a domain other than a `localhost` name, every address `allowed_addresses` returns
for a host that is not a configured proxy host is `Public` or `Private`
(`AllPublicOrPrivate`): no loopback and no blocked address. For `Public`, see the header. For
every value of `ExtModel.proxyEnvValues`. Covers only
successful calls of the composition and of `allowed_addresses` returning `some`. -/
theorem
    Theorems.metadata_resolver.MetadataAddressResolver.allPublicOrPrivate_of_new_allowing_private_addresses_eq_ok
    (base_url : url.Url) (r : MetadataAddressResolver) (d : Str)
    (h_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (h_name : isLocalhostName d.val = false) (h : (do
      let r₀ ← rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new base_url
      rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowing_private_addresses r₀) =
        ok r)
    (host : String) (h_unfiltered : host ∉ r.unfiltered_hosts.data.val)
    (resolved v : alloc.vec.Vec core.net.socket_addr.SocketAddr)
    (h_res : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowed_addresses r host
      resolved = ok (some v)) :
    AllPublicOrPrivate v.val :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allPublicOrPrivate_of_new_allowing_private_addresses_eq_ok
    base_url r d h_host h_name h host h_unfiltered resolved v h_res

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allPublicOrPrivate_of_new_allowing_private_addresses_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allPublicOrPrivate_of_new_allowing_private_addresses_eq_ok

/-- **N03 then N09, a configured proxy host gets every resolved address** (human decision
2026-11-26; module docstring, upstream lines 10–11: "Configured proxy hosts are not filtered";
doc comment of `AuthorizationManager::new`, `auth.rs` line 1508: "Hosts of proxies set through
`HTTP_PROXY`, `HTTPS_PROXY` or `ALL_PROXY` are not filtered"): for the resolver that
`new base_url` builds, a host whose UTF-8 bytes are the normalized host (`proxyHost`) of one of
the proxy values `new` reads (`ExtModel.proxyEnvValues`, upstream lines 102–106) is an unfiltered
host (`mem_unfiltered_hosts_iff_of_new_eq_ok`), and `allowed_addresses` returns `some` of the
resolved addresses unchanged: the membership test (upstream line 195, patched lines 215–217)
returns them before any filtering (upstream line 196), whatever their classes, also when there
is none (the emptiness check, upstream lines 203–209, patched 225–227, applies only to filtered
hosts; the async shell then returns an empty address list, not an error). For every value of
`ExtModel.proxyEnvValues`. Covers only a successful call of `new`. No other premise. -/
theorem
    Theorems.metadata_resolver.MetadataAddressResolver.allowed_addresses_eq_ok_some_of_new_eq_ok_of_mem_proxyHosts
    (base_url : url.Url) (r : MetadataAddressResolver)
    (h : rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.new base_url = ok r)
    (host : String)
    (h_proxy : Defs.utf8Bytes host ∈ ExtModel.proxyEnvValues.val.filterMap
      (proxyHost ∘ Defs.utf8Bytes))
    (resolved : alloc.vec.Vec core.net.socket_addr.SocketAddr) :
    rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowed_addresses r host resolved
      = ok (some resolved) :=
  @rmcp.transport.auth.metadata_resolver.MetadataAddressResolver.allowed_addresses_eq_ok_some_of_new_eq_ok_of_mem_proxyHosts
    base_url r h host h_proxy resolved

/--
info: 'Theorems.metadata_resolver.MetadataAddressResolver.allowed_addresses_eq_ok_some_of_new_eq_ok_of_mem_proxyHosts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.MetadataAddressResolver.allowed_addresses_eq_ok_some_of_new_eq_ok_of_mem_proxyHosts

/-! ### Normalization (N11) -/

/-- **N11 is idempotent**: normalizing the (dereferenced) result of `normalize_host` gives the
same string. An equation between computations, failure included (both sides fail with
`undef` on bytes that are not UTF-8), so no premise. -/
theorem Theorems.metadata_resolver.normalize_host_idem (host : Str) :
    (do
      let r ← rmcp.transport.auth.metadata_resolver.normalize_host host
      let s ← alloc.string.String.Insts.CoreOpsDerefDerefStr.deref r
      rmcp.transport.auth.metadata_resolver.normalize_host s) =
        rmcp.transport.auth.metadata_resolver.normalize_host host :=
  @rmcp.transport.auth.metadata_resolver.normalize_host_idem host

/--
info: 'Theorems.metadata_resolver.normalize_host_idem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.metadata_resolver.normalize_host_idem
