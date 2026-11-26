/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Proofs.Transport.MetadataResolver.Common

@[expose] public section

/-!
# Spec theorems for the OAuth metadata address policy (N01, N03–N11)

The address policy of `MetadataAddressResolver` decides which addresses OAuth metadata requests
and their redirects may reach: N01 `AddressClass::of` classifies an IP address, N03 `new` (the
equation `with_proxy_hosts ∘ with_base_url` and facts about its successful calls), N04
`with_lookup` (through the private `with_base_url` of patch 05 and its callee
`AuthorizationManager::is_loopback_metadata_host`) fixes the classes the base URL grants, N05
`with_proxy_hosts` (with the private `proxy_host`) exempts the proxy hosts, N06
`allowing_private_addresses` adds `Private`, N07 `allows_url` checks IP-literal targets, N08
`is_allowed` is the policy check, N09 `resolve` filters resolved addresses (through its pure part
`allowed_addresses`), N10 `literal_ip` and N11 `normalize_host`. Then the laws of the
definitions of `Defs.MetadataResolver` and the composition theorems and invariants, among them
the production guarantees for `AuthorizationManager::new` and `new_allowing_private_addresses`.

The statements are the ones signed off by the human spec owner on 2026-11-26 (statements
unchanged, two docstring cross-references updated: `utf8Bytes_injective`,
`utf8Bytes_mem_map_iff`); they are restated, as
`Theorems.metadata_resolver.*` and `Theorems.auth.AuthorizationManager.is_loopback_metadata_host*`,
in `Proofs.Internal.Transport.Auth.MetadataResolver`. Each proof goes through the equations and
inversion lemmas of `Proofs.Transport.MetadataResolver.Common`; the composition theorems combine
the spec theorems with the laws of the definitions.

Source: "crates/rmcp/src/transport/auth/metadata_resolver.rs", lines 33–225 at upstream `7caec76`
(translated through `formal/trusted/patches/05-metadata-resolver.patch`), and
"crates/rmcp/src/transport/auth.rs", lines 1401–1410 (`is_loopback_metadata_host`)
-/

open Aeneas Aeneas.Std Result
open rmcp
open Defs.MetadataResolver
-- The newtype `Lookup` of patch 05 hunk H1 (patched line 102), declared at the root by
-- `Rmcp.TypesExternal`.
open transport.auth.metadata_resolver (Lookup)
open ExtModel Proofs.External.Utf8 Proofs.External.WP
open Proofs.Transport.MetadataResolver

set_option autoImplicit false

namespace rmcp.transport.auth.metadata_resolver

/-! ## N01 `AddressClass::of` (upstream lines 42–74) -/

/-- **Spec theorem for `rmcp::transport::auth::metadata_resolver::AddressClass::of`** (N01)

Never fails. The class of the address (`Defs.MetadataResolver.addressClass`): an IPv6 address
that carries an IPv4 address (A01: IPv4-mapped, NAT64 `64:ff9b::/96`, IPv4-compatible, 6to4) is
classified as that IPv4 address (lines 43–48); an IPv4 address is `Loopback` in `127/8`,
`Private` in `10/8`, `172.16/12`, `192.168/16`, `100.64/10`, otherwise `Blocked` if A02 blocks
it, otherwise `Public` (lines 50–61); another IPv6 address is `Loopback` for `::1`, `Private` in
`fc00::/7`, otherwise `Blocked` if A03 blocks it, otherwise `Public` (lines 62–72). For
`Public` (H8 among it), see the header. No premise. -/
@[step]
theorem AddressClass.of_spec (addr : core.net.ip_addr.IpAddr) :
    AddressClass.of addr ⦃ (result : AddressClass) =>
      result = addressClass addr ⦄ := by
  rw [of_eq, WP.spec_ok]

/-! ## N03 `MetadataAddressResolver::new` (upstream lines 101–107; patched 105–108) -/

/-- **N03 `new` is `with_proxy_hosts ∘ with_base_url`** (patched lines 105–108, hunk H3):
`new base_url` builds the resolver of `base_url` with the operating-system resolver
`ExtModel.systemLookup` and then exempts the hosts of the proxy values read from the
environment. Names `ExtModel.proxyEnvValues` only to say that the reading is passed to
`with_proxy_hosts` (review rule at `ExtModel.proxyEnvValues`); an equation between
computations, failure included. Not tagged `@[step]`. -/
theorem MetadataAddressResolver.new_eq (base_url : url.Url) :
    MetadataAddressResolver.new base_url =
      (do
        let r ← MetadataAddressResolver.with_base_url base_url ExtModel.systemLookup
        MetadataAddressResolver.with_proxy_hosts
          (core.iter.traits.collect.IntoIteratorVec String) r ExtModel.proxyEnvValues) := by
  exact new_eq_bind base_url

/-- **N03, the fields not set from the environment** (human decision T4, 2026-11-26): if
`new base_url` returns `r`, then `r` has the base literal, the granted classes and the lookup
of `with_base_url base_url ExtModel.systemLookup` (N04): `base_ip` is the IP literal of the
base URL, `base_classes` is `baseClasses (urlHost base_url)` and `lookup` is the
operating-system resolver; this holds for every value of `ExtModel.proxyEnvValues`. Covers only
successful calls and does not show that the call succeeds (see the module docstring). No
premise. -/
theorem MetadataAddressResolver.new_fields_of_eq_ok (base_url : url.Url)
    (r : MetadataAddressResolver) (h : MetadataAddressResolver.new base_url = ok r) :
    r.base_ip = literalIp (ExtModel.urlHost base_url) ∧
      r.base_classes.data.val = baseClasses (ExtModel.urlHost base_url) ∧
      r.lookup = ExtModel.systemLookup := by
  obtain ⟨m, h1, h2⟩ := exists_with_base_url_eq_ok_of_new_eq_ok base_url r h
  obtain ⟨-, e1, e2, e3⟩ := fields_of_with_proxy_hosts_eq_ok _ _ _ h2
  obtain ⟨f1, -, f3, f4⟩ := with_base_url_of_eq_ok _ _ _ h1
  exact ⟨e1.trans f1, by rw [e2, f3], e3.trans f4⟩

/-- **N03, the unfiltered hosts** (human decision 2026-11-26, extension of T4): if
`new base_url` returns `r`, its unfiltered hosts are, in order, the normalized hosts
(`proxyHost`) of the proxy values that `new` reads from the environment
(`ExtModel.proxyEnvValues`, upstream lines 102–106) and passes to `with_proxy_hosts` (N05),
skipping the values without one; `with_base_url` starts with none (line 123). Names
`ExtModel.proxyEnvValues` only as the values `new` passes on, with no premise on them. Covers
only successful calls and does not show that the call succeeds. No premise. -/
theorem MetadataAddressResolver.new_unfiltered_hosts_of_eq_ok (base_url : url.Url)
    (r : MetadataAddressResolver) (h : MetadataAddressResolver.new base_url = ok r) :
    r.unfiltered_hosts.data.val.map Defs.utf8Bytes =
      ExtModel.proxyEnvValues.val.filterMap (fun p => proxyHost (Defs.utf8Bytes p)) := by
  obtain ⟨m, h1, h2⟩ := exists_with_base_url_eq_ok_of_new_eq_ok base_url r h
  obtain ⟨e1, -⟩ := fields_of_with_proxy_hosts_eq_ok _ _ _ h2
  obtain ⟨-, f2, -, -⟩ := with_base_url_of_eq_ok _ _ _ h1
  rw [e1, f2]; rfl

/-! ## N04 `with_lookup` (upstream lines 109–127), through `with_base_url` (patched 114–136) -/

end rmcp.transport.auth.metadata_resolver

namespace rmcp.transport.auth.AuthorizationManager

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::is_loopback_metadata_host`**
(helper of N04; `auth.rs` lines 1401–1410, patch 05 hunk H9)

For a host whose domain, if any, is UTF-8 (rule (ii)(a): the `&str` carried by the argument
`Host<&str>`), never fails: `true` exactly for a `localhost` name (after removing trailing dots
and lowercasing ASCII letters, `localhost` or a name ending in `.localhost`), an IPv4 address
in `127/8` or the IPv6 address `::1` (`Defs.MetadataResolver.isLoopbackHost`). The premise is
the weakest (`is_loopback_metadata_host_fail`). -/
@[step]
theorem is_loopback_metadata_host_spec (host : url.host.Host Str)
    (h_utf8 : ∀ d, host = url.host.Host.Domain d → ExtModel.IsUtf8 d.val) :
    is_loopback_metadata_host host ⦃ (result : Bool) =>
      result = isLoopbackHost host ⦄ := by
  rw [is_loopback_metadata_host_eq host h_utf8, WP.spec_ok]

/-- **`is_loopback_metadata_host`, the UTF-8 premise is the weakest**: for a domain whose
bytes are not UTF-8 (no Rust `&str`), `to_ascii_lowercase` (`auth.rs` line 1404:
`domain.trim_end_matches('.').to_ascii_lowercase()`) fails, so the call fails with `undef`.
The proof needs the converse UTF-8 lemmas named at `normalize_host_fail`. -/
theorem is_loopback_metadata_host_fail (d : Str) (h : ¬ ExtModel.IsUtf8 d.val) :
    is_loopback_metadata_host (url.host.Host.Domain d) = fail .undef := by
  exact is_loopback_metadata_host_domain_eq_fail d h

end rmcp.transport.auth.AuthorizationManager

namespace rmcp.transport.auth.metadata_resolver

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
@[step]
theorem MetadataAddressResolver.with_base_url_spec (base_url : url.Url)
    (lookup : Lookup)
    (h_utf8 : ∀ d, ExtModel.urlHost base_url = some (url.host.Host.Domain d) →
      ExtModel.IsUtf8 d.val) :
    MetadataAddressResolver.with_base_url base_url lookup
      ⦃ (result : MetadataAddressResolver) =>
      result.base_ip = literalIp (ExtModel.urlHost base_url) ∧
      result.unfiltered_hosts.data.val = [] ∧
      result.base_classes.data.val = baseClasses (ExtModel.urlHost base_url) ∧
      result.lookup = lookup ⦄ := by
  obtain ⟨r, hr, h⟩ := exists_with_base_url_eq_ok base_url lookup h_utf8
  rw [hr, WP.spec_ok]; exact h

/-- **`with_base_url`, the UTF-8 premise is the weakest**: for a base URL whose domain is not
UTF-8, the call of `is_loopback_metadata_host` (patched line 121; upstream line 115) fails, so
`with_base_url` fails with `undef` (`is_loopback_metadata_host_fail`). -/
theorem MetadataAddressResolver.with_base_url_fail (base_url : url.Url)
    (lookup : Lookup) (d : Str)
    (h_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (h : ¬ ExtModel.IsUtf8 d.val) :
    MetadataAddressResolver.with_base_url base_url lookup = fail .undef := by
  exact with_base_url_eq_fail base_url lookup d h_host h

/-! ## N05 `with_proxy_hosts` (upstream lines 131–147; patched 140–149, `proxy_host` 233–245)
-/

/-- **Spec theorem for `rmcp::transport::auth::metadata_resolver::proxy_host`** (helper of N05;
upstream lines 132–139, the `filter_map` closure; patched lines 233–245, hunk H4)

For a proxy value that fits the string models (`ProxyFits`) and whose parsed URL's host
string, if any, is UTF-8 (`ProxyHostUtf8`, rule (ii)(b)), never fails: the normalized host of
the URL `proxyUrl proxy` (the value, with `http://` in front if it has no `://`), or `none` if
that does not parse or has no host (`Defs.MetadataResolver.proxyHost`, as bytes). Both premises are
the weakest (`proxy_host_fail`, `proxy_host_fail_undef`). -/
@[step]
theorem proxy_host_spec (proxy : String) (h_fits : ProxyFits proxy)
    (h_utf8 : ProxyHostUtf8 proxy) :
    proxy_host proxy ⦃ (result : Option String) =>
      result.map Defs.utf8Bytes = proxyHost (Defs.utf8Bytes proxy) ⦄ := by
  obtain ⟨o, ho⟩ := exists_proxy_host_eq_ok proxy h_fits h_utf8
  rw [ho, WP.spec_ok]; exact (proxy_host_of_eq_ok ho).1

/-- **`proxy_host`, the size premise is exact for the Lean models** (memory convention): for a
value that does not fit (`¬ ProxyFits proxy`), the call fails: with `maximumSizeExceeded` if
its bytes do not fit in a slice (the model of `String::deref`, patched line 234), otherwise
with `panic` (the value has no `://` and `http://` followed by it exceeds `isize::MAX` bytes:
the capacity panic of `String::push_str`, patched line 238; upstream line 136, `format!`). -/
theorem proxy_host_fail (proxy : String) (h : ¬ ProxyFits proxy) :
    proxy_host proxy =
      fail (if proxy.utf8ByteSize ≤ Usize.max then .panic else .maximumSizeExceeded) := by
  exact proxy_host_eq_fail proxy h

/-- **`proxy_host`, the UTF-8 premise is the weakest**: for a value that fits but violates
`ProxyHostUtf8` (its URL `proxyUrl proxy` parses to some `u` with a host string `h` that is not
UTF-8), the call of `normalize_host` on `h` (patched line 244) fails, so `proxy_host` fails with
`undef` (`normalize_host_fail`). -/
theorem proxy_host_fail_undef (proxy : String) (h_fits : ProxyFits proxy)
    (h : ¬ ProxyHostUtf8 proxy) :
    proxy_host proxy = fail .undef := by
  unfold ProxyHostUtf8 at h
  push Not at h
  obtain ⟨u, hs, hu, hhs, hn⟩ := h
  rw [proxy_host_eq_proxyHostTail proxy h_fits, proxyHostTail, hu]
  simp only [hhs, normalize_host_eq_fail hs hn, bind_fail]

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
@[step]
theorem MetadataAddressResolver.with_proxy_hosts_spec (self : MetadataAddressResolver)
    (proxies : alloc.vec.Vec String) (h_fits : ∀ p ∈ proxies.val, ProxyFits p)
    (h_utf8 : ∀ p ∈ proxies.val, ProxyHostUtf8 p)
    (h_len : self.unfiltered_hosts.data.val.length +
      (proxies.val.filterMap (fun p => proxyHost (Defs.utf8Bytes p))).length ≤ Usize.max) :
    MetadataAddressResolver.with_proxy_hosts (core.iter.traits.collect.IntoIteratorVec String)
      self proxies ⦃ (result : MetadataAddressResolver) =>
      result.unfiltered_hosts.data.val.map Defs.utf8Bytes =
        self.unfiltered_hosts.data.val.map Defs.utf8Bytes ++
          proxies.val.filterMap (fun p => proxyHost (Defs.utf8Bytes p)) ∧
      result.base_ip = self.base_ip ∧
      result.base_classes = self.base_classes ∧
      result.lookup = self.lookup ⦄ := by
  have hok : ∃ r, MetadataAddressResolver.with_proxy_hosts
      (core.iter.traits.collect.IntoIteratorVec String) self proxies = ok r := by
    unfold MetadataAddressResolver.with_proxy_hosts
    simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, bind_ok, to_vec_string]
    rw [into_iter_eq_mkIntoIter, bind_ok]
    obtain ⟨v, hv⟩ := exists_with_proxy_hosts_loop_eq_ok proxies.val proxies.property
      ⟨self.unfiltered_hosts.data⟩ (fun p hp => ⟨h_fits p hp, h_utf8 p hp⟩) h_len
    rw [hv, bind_ok]
    simp [core.convert.IntoFrom.into, alloc.sync.ArcSlice.Insts.CoreConvertFromVec.from]
  obtain ⟨r, hr⟩ := hok
  rw [hr, WP.spec_ok]
  exact fields_of_with_proxy_hosts_eq_ok self r proxies hr

/-- **N05, what a successful call returns** (human decision 2026-11-26, extension of T4): if
`with_proxy_hosts self proxies` returns `r`, then `r` is described as in
`with_proxy_hosts_spec`: the unfiltered hosts are the old ones followed, in order, by the
normalized host (`proxyHost`) of each proxy value that has one, and `base_ip`, `base_classes`,
`lookup` are unchanged. No premise: a successful call has passed every `deref`, `push_str`,
`normalize_host` and `push` of the loop (patched lines 140–149, 233–245), so each value fitted
and each host string was UTF-8. Covers only successful calls and does not show that the call
succeeds. -/
theorem MetadataAddressResolver.with_proxy_hosts_of_eq_ok (self r : MetadataAddressResolver)
    (proxies : alloc.vec.Vec String)
    (h : MetadataAddressResolver.with_proxy_hosts
      (core.iter.traits.collect.IntoIteratorVec String) self proxies = ok r) :
    r.unfiltered_hosts.data.val.map Defs.utf8Bytes =
        self.unfiltered_hosts.data.val.map Defs.utf8Bytes ++
          proxies.val.filterMap (fun p => proxyHost (Defs.utf8Bytes p)) ∧
      r.base_ip = self.base_ip ∧ r.base_classes = self.base_classes ∧
      r.lookup = self.lookup := by
  exact (with_proxy_hosts_of_eq_ok_and_premises self r proxies h).1

/-- **N05, the premises of `with_proxy_hosts_spec` are necessary** (finding Q2 of spec round 2):
if `with_proxy_hosts self proxies` returns `r`, every proxy value fits the string models
(`ProxyFits`) and the host string of its parsed URL, if any, is UTF-8 (`ProxyHostUtf8`). The
loop (patched lines 142–146) calls `proxy_host` on every value, in order, and a failing call
fails the loop; `proxy_host` fails exactly when one of the two is violated (`proxy_host_fail`,
`proxy_host_fail_undef`). With `with_proxy_hosts_spec`, the premises are exact at this level;
the third premise, the length bound, is necessary because the hosts of `r`
(`with_proxy_hosts_of_eq_ok`) are a `Slice`. No premise. -/
theorem MetadataAddressResolver.proxyFits_and_proxyHostUtf8_of_with_proxy_hosts_eq_ok
    (self r : MetadataAddressResolver) (proxies : alloc.vec.Vec String)
    (h : MetadataAddressResolver.with_proxy_hosts
      (core.iter.traits.collect.IntoIteratorVec String) self proxies = ok r) :
    ∀ p ∈ proxies.val, ProxyFits p ∧ ProxyHostUtf8 p := by
  exact (with_proxy_hosts_of_eq_ok_and_premises self r proxies h).2

/-! ## N06 `allowing_private_addresses` (upstream lines 150–160; patched 152–159) -/

/-- **Spec theorem for
`rmcp::transport::auth::metadata_resolver::MetadataAddressResolver::allowing_private_addresses`**
(N06)

If `Private` is already granted or there is room for one more class (`Vec::push`, patch 05 hunk
H5), never fails: `Private` is appended to the granted classes unless already present
(`withPrivate`); `base_ip`, `unfiltered_hosts` and `lookup` are unchanged. The premise is exact
for the Lean models (`allowing_private_addresses_fail`). -/
@[step]
theorem MetadataAddressResolver.allowing_private_addresses_spec (self : MetadataAddressResolver)
    (h_room : AddressClass.Private ∈ self.base_classes.data.val ∨
      self.base_classes.data.val.length < Usize.max) :
    MetadataAddressResolver.allowing_private_addresses self
      ⦃ (result : MetadataAddressResolver) =>
      result.base_classes.data.val = withPrivate self.base_classes.data.val ∧
      result.base_ip = self.base_ip ∧
      result.unfiltered_hosts = self.unfiltered_hosts ∧
      result.lookup = self.lookup ⦄ := by
  obtain ⟨r, h1, h2⟩ := exists_allowing_private_addresses_eq_ok self h_room
  rw [h1, WP.spec_ok]; exact h2

/-- **`allowing_private_addresses`, the premise is exact for the Lean models** (memory
convention): without `Private` and with `Usize.max` classes already, the `push` of patched
line 155 fails with `maximumSizeExceeded` (no such slice fits in memory in Rust). -/
theorem MetadataAddressResolver.allowing_private_addresses_fail (self : MetadataAddressResolver)
    (h : ¬ (AddressClass.Private ∈ self.base_classes.data.val ∨
      self.base_classes.data.val.length < Usize.max)) :
    MetadataAddressResolver.allowing_private_addresses self = fail .maximumSizeExceeded := by
  exact allowing_private_addresses_eq_fail self h

/-! ## N07 `allows_url` (upstream lines 164–172; patched 163–171) -/

/-- **Spec theorem for
`rmcp::transport::auth::metadata_resolver::MetadataAddressResolver::allows_url`** (N07)

Never fails. The policy for the target's host (`Defs.MetadataResolver.allowsHost`): `true` when
the host is not an IP literal (line 170: names are left to `resolve`); for an IP literal, `true`
exactly when it is the base URL's own literal (line 167) or its class is allowed by the granted
classes (line 168, N01 and N08). No premise. -/
@[step]
theorem MetadataAddressResolver.allows_url_spec (self : MetadataAddressResolver)
    (target : url.Url) :
    MetadataAddressResolver.allows_url self target ⦃ (result : Bool) =>
      result =
        allowsHost self.base_ip self.base_classes.data.val (ExtModel.urlHost target) ⦄ := by
  unfold MetadataAddressResolver.allows_url allowsHost
  rw [literal_ip_eq, bind_ok]
  cases literalIp (ExtModel.urlHost target) with
  | none => simp
  | some ip =>
    simp only
    have heq : core.option.Option.Insts.CoreCmpPartialEqOption.eq
        core.net.ip_addr.IpAddr.Insts.CoreCmpPartialEqIpAddr self.base_ip (some ip) =
        ok (decide (self.base_ip = some ip)) := by
      cases hb : self.base_ip with
      | none => simp [core.option.Option.Insts.CoreCmpPartialEqOption.eq]
      | some l =>
        simp only [core.option.Option.Insts.CoreCmpPartialEqOption.eq, Option.some.injEq]
        obtain ⟨b, hb', hbv⟩ := exists_ok_of_spec
          (core.net.ip_addr.IpAddr.Insts.CoreCmpPartialEqIpAddr.eq_spec l ip)
        rw [hb']; congr 1; cases b <;> simp_all
    rw [heq, bind_ok]
    by_cases hb : self.base_ip = some ip
    · simp [hb]
    · simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.false_or, of_eq, bind_ok,
        alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, is_allowed_eq, WP.spec_ok]

/-! ## N08 `is_allowed` (upstream lines 180–186) -/

/-- **Spec theorem for
`rmcp::transport::auth::metadata_resolver::MetadataAddressResolver::is_allowed`** (N08)

Never fails. `Public`: `true`; `Loopback`, `Private`: `true` exactly when the class is in
`base_classes`; `Blocked`: `false` (`Defs.MetadataResolver.isAllowed`). No premise. -/
@[step]
theorem MetadataAddressResolver.is_allowed_spec («class» : AddressClass)
    (base_classes : Slice AddressClass) :
    MetadataAddressResolver.is_allowed «class» base_classes ⦃ (result : Bool) =>
      result = isAllowed «class» base_classes.val ⦄ := by
  cases «class» <;> simp [MetadataAddressResolver.is_allowed, contains_addressClass, isAllowed]

/-! ## N09 `resolve` (upstream lines 190–212), through `allowed_addresses` (patched 210–229) -/

/-- **Spec theorem for
`rmcp::transport::auth::metadata_resolver::MetadataAddressResolver::allowed_addresses`** (N09;
the pure part of `resolve`, upstream lines 195–210, moved by patch 05 hunk H6)

Never fails. For a host in `unfiltered_hosts` (line 195): `some` of all resolved addresses
(also none). Otherwise: the resolved addresses whose class (N01) is allowed by
`base_classes` (N08), in order (lines 199–202), or `none` if there is none (lines 203–209,
where the async shell returns the error) (`Defs.MetadataResolver.allowedAddresses`). No
premise. -/
@[step]
theorem MetadataAddressResolver.allowed_addresses_spec (self : MetadataAddressResolver)
    (host : String) (resolved : alloc.vec.Vec core.net.socket_addr.SocketAddr) :
    MetadataAddressResolver.allowed_addresses self host resolved
      ⦃ (result : Option (alloc.vec.Vec core.net.socket_addr.SocketAddr)) =>
      result.map (fun v => v.val) =
        allowedAddresses self.unfiltered_hosts.data.val self.base_classes.data.val host
          resolved.val ⦄ := by
  unfold MetadataAddressResolver.allowed_addresses allowedAddresses
  simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, bind_ok, contains_string]
  by_cases hm : host ∈ self.unfiltered_hosts.data.val
  · simp [hm]
  · simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [bind_into_iter]
    obtain ⟨v, hv, hvv⟩ := exists_allowed_addresses_loop_eq_ok resolved.val resolved rfl
      self.base_classes (alloc.vec.Vec.new _)
      (by simp [alloc.vec.Vec.new])
    rw [hv, bind_ok]
    simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append] at hvv
    simp only [alloc.vec.Vec.is_empty, bind_ok]
    cases hf : List.filter
        (fun x => isAllowed (addressClass (socketIp x)) self.base_classes.data.val)
        resolved.val with
    | nil =>
      have : v.length = 0 := by simp [alloc.vec.Vec.length, hvv, hf]
      simp [this]
    | cons y ys =>
      have : ¬ v.length = 0 := by simp [alloc.vec.Vec.length, hvv, hf]
      simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok, Option.map_some,
          hvv, hf]

/-! ## N10 `literal_ip` (upstream lines 215–221; patched 247–253) -/

/-- **Spec theorem for `rmcp::transport::auth::metadata_resolver::literal_ip`** (N10)

Never fails. The IP address of the URL's host if it is an IPv4 or IPv6 literal, `none` for a
domain or no host (`Defs.MetadataResolver.literalIp` of `ExtModel.urlHost target`). No
premise. -/
@[step]
theorem literal_ip_spec (target : url.Url) :
    literal_ip target ⦃ (result : Option core.net.ip_addr.IpAddr) =>
      result = literalIp (ExtModel.urlHost target) ⦄ := by
  rw [literal_ip_eq]; simp

/-! ## N11 `normalize_host` (upstream lines 223–225; patched 255–257) -/

/-- **Spec theorem for `rmcp::transport::auth::metadata_resolver::normalize_host`** (N11)

For a UTF-8 `host` (rule (ii)(a), the `&str` argument), never fails: the string whose bytes are
those of `host` without trailing `.` bytes, with ASCII letters lowercased
(`Defs.MetadataResolver.normalizeHost`). The premise is the weakest (`normalize_host_fail`). -/
@[step]
theorem normalize_host_spec (host : Str) (h_utf8 : ExtModel.IsUtf8 host.val) :
    normalize_host host ⦃ (result : String) =>
      Defs.utf8Bytes result = normalizeHost host.val ⦄ := by
  obtain ⟨s, hs, hsv⟩ := exists_normalize_host_eq_ok host h_utf8
  rw [hs, WP.spec_ok]; exact hsv

/-- **N11, the UTF-8 premise is the weakest**: on bytes that are not UTF-8 (no Rust `&str`), the
model of `to_ascii_lowercase` fails, so `normalize_host` fails with `undef`. The proof needs the
converse of the lemmas `Proofs.External.MetadataResolver.isUtf8_dropTrailingDots` and
`Proofs.External.MetadataResolver.isUtf8_map_asciiLowercase` (module
`Proofs.External.MetadataResolver`; lead decision 2026-11-26: the proof effort is accepted):
`IsUtf8 (dropTrailingDots l) → IsUtf8 l` (the removed bytes are ASCII `.`) and
`IsUtf8 (l.map asciiLowercase) → IsUtf8 l` (the map changes only ASCII letters, into ASCII
letters), and that `ExtModel.strOfBytes? l = none` when `¬ IsUtf8 l`. -/
theorem normalize_host_fail (host : Str) (h : ¬ ExtModel.IsUtf8 host.val) :
    normalize_host host = fail .undef := by
  exact normalize_host_eq_fail host h

end rmcp.transport.auth.metadata_resolver

/-! ## Laws of the definitions

About `Defs.utf8Bytes` and `Defs.MetadataResolver` only (no translated function); they say what
the policy means and are what the composition theorems below reduce to. None is tagged
`@[step]`. -/

namespace Defs.MetadataResolver

open rmcp.transport.auth.metadata_resolver (AddressClass)

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
`rfl`). Restated as `Theorems.metadata_resolver.utf8Bytes_injective` in
`Proofs/Internal/Transport/Auth/MetadataResolver.lean`. -/
theorem utf8Bytes_injective : Function.Injective Defs.utf8Bytes :=
  fun _ _ h => Proofs.External.Utf8.utf8_injective h

/-- **A string is in a list exactly when its bytes are in the list of their bytes**: Mathlib's
`List.mem_map_of_injective` with `utf8Bytes_injective`. Restated as
`Theorems.metadata_resolver.utf8Bytes_mem_map_iff` in
`Proofs/Internal/Transport/Auth/MetadataResolver.lean`. -/
theorem utf8Bytes_mem_map_iff {hosts : List String} {host : String} :
    Defs.utf8Bytes host ∈ hosts.map Defs.utf8Bytes ↔ host ∈ hosts :=
  List.mem_map_of_injective utf8Bytes_injective

/-! ### The policy check (N08) -/

/-- **A public address is always allowed** (upstream line 182), whatever the granted classes. -/
theorem isAllowed_public (base : List AddressClass) : isAllowed .Public base = true := by
  rfl

/-- **A blocked address is never allowed** (upstream line 184), whatever the granted classes. -/
theorem isAllowed_blocked (base : List AddressClass) : isAllowed .Blocked base = false := by
  rfl

/-- **Granting more classes never refuses more** (upstream line 183: membership in
`base_classes`). -/
theorem isAllowed_mono {base base' : List AddressClass} (h_sub : base ⊆ base')
    {c : AddressClass} (h : isAllowed c base = true) : isAllowed c base' = true := by
  cases c <;> simp only [isAllowed, decide_eq_true_eq, Bool.false_eq_true] at h ⊢ <;>
    exact h_sub h

/-- **Without `Loopback` and `Private` granted, only public addresses are allowed** (upstream
lines 181–185). This is the case of a base URL that names a domain other than a `localhost`
name, a public or blocked IP literal, or no host (`loopback_mem_baseClasses_iff`,
`private_mem_baseClasses_iff`). -/
theorem eq_public_of_isAllowed {base : List AddressClass}
    (h_loopback : AddressClass.Loopback ∉ base) (h_private : AddressClass.Private ∉ base)
    {c : AddressClass} (h : isAllowed c base = true) : c = .Public := by
  cases c <;> simp_all [isAllowed]

/-! ### The policy for an IP-literal target (N07) -/

/-- **The base URL's own host is always allowed** (doc comment of `allows_url`, upstream lines
162–163: "The base URL's own literal is always allowed"; line 167: `self.base_ip == Some(ip)`;
line 170: a host without an IP literal is allowed): a target with the host of the base URL is
allowed by the base URL's literal, whatever the granted classes, also when its literal is
`Blocked`. -/
theorem allowsHost_literalIp_self (base : List AddressClass) (host : Option (url.host.Host Str)) :
    allowsHost (literalIp host) base host = true := by
  unfold allowsHost; cases literalIp host <;> simp

/-! ### The classes a base URL grants (N04) -/

/-- **A base URL grants `Loopback` exactly through its own host** (module docstring, upstream
lines 4–7; lines 111–120): a loopback IP literal (also embedded in IPv6) or a `localhost`
name. -/
theorem loopback_mem_baseClasses_iff (host : Option (url.host.Host Str)) :
    AddressClass.Loopback ∈ baseClasses host ↔
      (∃ ip, literalIp host = some ip ∧ addressClass ip = .Loopback) ∨
        ∃ d, host = some (url.host.Host.Domain d) ∧ isLocalhostName d.val = true := by
  rcases host with _ | ⟨d⟩ | ⟨a⟩ | ⟨a⟩
  · simp [baseClasses, literalIp]
  · by_cases hl : isLocalhostName d.val = true <;> simp [baseClasses, literalIp, hostIp, hl]
  · simp only [baseClasses, literalIp, hostIp, Option.bind_some, List.mem_singleton]
    constructor
    · intro h; left; exact ⟨_, rfl, h.symm⟩
    · rintro (⟨ip, hip, hc⟩ | ⟨d, hd, -⟩)
      · cases hip; exact hc.symm
      · cases hd
  · simp only [baseClasses, literalIp, hostIp, Option.bind_some, List.mem_singleton]
    constructor
    · intro h; left; exact ⟨_, rfl, h.symm⟩
    · rintro (⟨ip, hip, hc⟩ | ⟨d, hd, -⟩)
      · cases hip; exact hc.symm
      · cases hd

/-- **A base URL grants `Private` exactly when its host is a private IP literal** (also
embedded in IPv6; module docstring, upstream lines 4–7; lines 111–120). -/
theorem private_mem_baseClasses_iff (host : Option (url.host.Host Str)) :
    AddressClass.Private ∈ baseClasses host ↔
      ∃ ip, literalIp host = some ip ∧ addressClass ip = .Private := by
  rcases host with _ | ⟨d⟩ | ⟨a⟩ | ⟨a⟩
  · simp [baseClasses, literalIp]
  · by_cases hl : isLocalhostName d.val = true <;> simp [baseClasses, literalIp, hostIp, hl]
  · simp only [baseClasses, literalIp, hostIp, Option.bind_some, List.mem_singleton]
    constructor
    · intro h; exact ⟨_, rfl, h.symm⟩
    · rintro ⟨ip, hip, hc⟩; cases hip; exact hc.symm
  · simp only [baseClasses, literalIp, hostIp, Option.bind_some, List.mem_singleton]
    constructor
    · intro h; exact ⟨_, rfl, h.symm⟩
    · rintro ⟨ip, hip, hc⟩; cases hip; exact hc.symm

/-- **A base URL grants at most one class** (upstream lines 112–119: each arm builds a vector of
at most one element). -/
theorem length_baseClasses_le_one (host : Option (url.host.Host Str)) :
    (baseClasses host).length ≤ 1 := by
  rcases host with _ | ⟨d⟩ | ⟨a⟩ | ⟨a⟩
  · simp [baseClasses]
  · simp only [baseClasses]
    split <;> simp
  · simp [baseClasses]
  · simp [baseClasses]

/-! ### The address filter (N09) -/

/-- **`resolve` returns a sublist of the resolved addresses** (in order; upstream lines 196,
199–202). -/
theorem allowedAddresses_sublist {unfiltered : List String} {base : List AddressClass}
    {host : String} {resolved v : List core.net.socket_addr.SocketAddr}
    (h : allowedAddresses unfiltered base host resolved = some v) : v.Sublist resolved := by
  unfold allowedAddresses at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact List.Sublist.refl _
  · cases hf : resolved.filter (fun a => isAllowed (addressClass (socketIp a)) base) with
    | nil => rw [hf] at h; cases h
    | cons y ys =>
      rw [hf] at h; simp only [Option.some.injEq] at h; subst h; rw [← hf]
      exact List.filter_sublist

/-- **An unfiltered host gets every resolved address** (upstream lines 195–197), also none. -/
theorem allowedAddresses_eq_some_of_mem {unfiltered : List String} (base : List AddressClass)
    {host : String} (resolved : List core.net.socket_addr.SocketAddr)
    (h : host ∈ unfiltered) : allowedAddresses unfiltered base host resolved = some resolved := by
  simp [allowedAddresses, h]

/-- **A filtered host fails exactly when no resolved address is allowed** (upstream lines
199–209; `none` is the error of the async shell). -/
theorem allowedAddresses_eq_none_iff {unfiltered : List String} (base : List AddressClass)
    {host : String} (resolved : List core.net.socket_addr.SocketAddr) (h : host ∉ unfiltered) :
    allowedAddresses unfiltered base host resolved = none ↔
      ∀ a ∈ resolved, isAllowed (addressClass (socketIp a)) base = false := by
  unfold allowedAddresses
  rw [ite_eq_right h]
  cases hf : resolved.filter (fun a => isAllowed (addressClass (socketIp a)) base) with
  | nil => simp only [true_iff]; intro a ha; rw [List.filter_eq_nil_iff] at hf; simpa using hf a ha
  | cons y ys =>
    simp only [reduceCtorEq, false_iff]; intro hall
    have : resolved.filter (fun a => isAllowed (addressClass (socketIp a)) base) = [] := by
      rw [List.filter_eq_nil_iff]; intro a ha; simp [hall a ha]
    rw [this] at hf; cases hf

/-- **The resolve invariant**: every address returned for a filtered host is allowed by the
granted classes (`AllAllowed`, the check of upstream line 201). -/
theorem allAllowed_of_allowedAddresses_eq_some {unfiltered : List String}
    {base : List AddressClass} {host : String} {resolved v : List core.net.socket_addr.SocketAddr}
    (h : allowedAddresses unfiltered base host resolved = some v) (h_host : host ∉ unfiltered) :
    AllAllowed base v := by
  unfold allowedAddresses at h
  rw [ite_eq_right h_host] at h
  cases hf : resolved.filter (fun a => isAllowed (addressClass (socketIp a)) base) with
  | nil => rw [hf] at h; cases h
  | cons y ys =>
    rw [hf] at h; simp only [Option.some.injEq] at h; subst h
    intro a ha; rw [← hf] at ha; exact (List.mem_filter.1 ha).2

/-- **No blocked address is returned for a filtered host** (module docstring, upstream lines
8–9: link-local, unspecified, broadcast, multicast and reserved addresses are never allowed),
whatever the granted classes; corollary of `allAllowed_of_allowedAddresses_eq_some` and
`isAllowed_blocked`. -/
theorem addressClass_ne_blocked_of_mem_allowedAddresses {unfiltered : List String}
    {base : List AddressClass} {host : String} {resolved v : List core.net.socket_addr.SocketAddr}
    (h : allowedAddresses unfiltered base host resolved = some v) (h_host : host ∉ unfiltered)
    {a : core.net.socket_addr.SocketAddr} (ha : a ∈ v) :
    addressClass (socketIp a) ≠ .Blocked := by
  intro hb
  have := allAllowed_of_allowedAddresses_eq_some h h_host a ha
  rw [hb, isAllowed_blocked] at this; cases this

/-! ### Host normalization (N11) -/

/-- **Normalization is idempotent** (upstream line 224). -/
theorem normalizeHost_idem (host : List U8) :
    normalizeHost (normalizeHost host) = normalizeHost host := by
  unfold normalizeHost
  rw [trimTrailingDots_map_asciiToLower, trimTrailingDots, trimTrailingDots,
    List.rdropWhile_idempotent, List.map_map]
  congr 1
  funext b
  exact asciiToLower_idem b

/-- **A trailing `.` does not change the normalized host** (`trim_end_matches('.')`, upstream
line 224). -/
theorem normalizeHost_append_dot (host : List U8) :
    normalizeHost (host ++ [dotByte]) = normalizeHost host := by
  unfold normalizeHost trimTrailingDots
  rw [List.rdropWhile_concat]
  simp

/-- **ASCII case does not change the normalized host** (`to_ascii_lowercase`, upstream line
224). -/
theorem normalizeHost_map_asciiToLower (host : List U8) :
    normalizeHost (host.map asciiToLower) = normalizeHost host := by
  unfold normalizeHost
  rw [trimTrailingDots_map_asciiToLower, List.map_map]
  congr 1; funext b; exact asciiToLower_idem b

/-- **A `localhost` name stays one under normalization**, and another name stays another
(`auth.rs` lines 1403–1406 normalize first). -/
theorem isLocalhostName_normalizeHost (host : List U8) :
    isLocalhostName (normalizeHost host) = isLocalhostName host := by
  unfold isLocalhostName; rw [normalizeHost_idem]

end Defs.MetadataResolver

/-! ## Composition theorems and invariants

About the translated functions named in each statement. None is tagged `@[step]`. -/

namespace rmcp.transport.auth.metadata_resolver

/-! ### Classes (N01 with A01) -/

/-- **N01 ∘ A01**: an IPv6 address that carries the IPv4 address `w` (`embedded_ipv4` returns
`some w`) has the class of `w` (upstream lines 43–48), so a loopback, private or blocked IPv4
address keeps its class in IPv4-mapped, NAT64, IPv4-compatible or 6to4 form. An equation
between computations; covers only a call of `embedded_ipv4` that returns `some w` (the suffix
`_some` distinguishes it from the case `ok none`). -/
theorem AddressClass.of_v6_eq_of_embedded_ipv4_eq_ok_some (a : core.net.ip_addr.Ipv6Addr)
    (w : core.net.ip_addr.Ipv4Addr)
    (h : transport.auth.AuthorizationManager.embedded_ipv4 a = ok (some w)) :
    AddressClass.of (.V6 a) = AddressClass.of (.V4 w) := by
  exact Proofs.Transport.MetadataResolver.of_v6_eq_of_embedded_ipv4_eq_ok_some a w h

/-! ### Builders (N03, N05, N06) -/

/-- **N05, the unfiltered hosts stay normalized**: if the unfiltered hosts of `self` are
normalized (`HostsNormalized`), so are those of the resolver that `with_proxy_hosts self
proxies` returns (the new ones are `normalize_host` results, upstream line 138, and
normalization is idempotent). So the membership test of `resolve` (line 195), which normalizes
the name first (line 193), exempts exactly the names that normalize to a stored host. Covers
only successful calls. -/
theorem MetadataAddressResolver.hostsNormalized_of_with_proxy_hosts_eq_ok
    (self r : MetadataAddressResolver) (proxies : alloc.vec.Vec String)
    (h_self : HostsNormalized self.unfiltered_hosts.data.val)
    (h : MetadataAddressResolver.with_proxy_hosts
      (core.iter.traits.collect.IntoIteratorVec String) self proxies = ok r) :
    HostsNormalized r.unfiltered_hosts.data.val := by
  obtain ⟨e1, -⟩ := fields_of_with_proxy_hosts_eq_ok _ _ _ h
  intro host hh
  have hb : Defs.utf8Bytes host ∈ r.unfiltered_hosts.data.val.map Defs.utf8Bytes :=
    List.mem_map_of_mem hh
  rw [e1, List.mem_append] at hb
  rcases hb with hb | hb
  · obtain ⟨h0, h0m, h0e⟩ := List.mem_map.1 hb
    rw [← h0e]; exact h_self h0 h0m
  · obtain ⟨p, -, hp⟩ := List.mem_filterMap.1 hb
    unfold proxyHost at hp
    split at hp
    · obtain ⟨hs, -, hse⟩ := Option.map_eq_some_iff.1 hp
      rw [← hse, normalizeHost_idem]
    · cases hp

/-- **N03, the unfiltered hosts are normalized** (`HostsNormalized`): for the resolver that
`new base_url` returns, for every value of `ExtModel.proxyEnvValues`. Covers only successful
calls. -/
theorem MetadataAddressResolver.hostsNormalized_of_new_eq_ok (base_url : url.Url)
    (r : MetadataAddressResolver) (h : MetadataAddressResolver.new base_url = ok r) :
    HostsNormalized r.unfiltered_hosts.data.val := by
  obtain ⟨m, h1, h2⟩ := exists_with_base_url_eq_ok_of_new_eq_ok base_url r h
  obtain ⟨-, f2, -, -⟩ := with_base_url_of_eq_ok _ _ _ h1
  exact hostsNormalized_of_with_proxy_hosts_eq_ok m r _ (by intro x hx; rw [f2] at hx; cases hx) h2

/-- **N03, membership in the unfiltered hosts** (finding Q8 of spec round 2): for the resolver
that `new base_url` returns, a `String` is an unfiltered host (the test of upstream line 195)
exactly when its UTF-8 bytes are the normalized host (`proxyHost`) of one of the proxy values
`new` reads (`ExtModel.proxyEnvValues`, upstream lines 102–106); from
`new_unfiltered_hosts_of_eq_ok` and `Defs.MetadataResolver.utf8Bytes_mem_map_iff`. Covers only
successful calls. No premise. -/
theorem MetadataAddressResolver.mem_unfiltered_hosts_iff_of_new_eq_ok (base_url : url.Url)
    (r : MetadataAddressResolver) (h : MetadataAddressResolver.new base_url = ok r)
    (host : String) :
    host ∈ r.unfiltered_hosts.data.val ↔
      Defs.utf8Bytes host ∈
        ExtModel.proxyEnvValues.val.filterMap (proxyHost ∘ Defs.utf8Bytes) := by
  rw [← utf8Bytes_mem_map_iff, new_unfiltered_hosts_of_eq_ok base_url r h]; exact Iff.rfl

/-- **N06 then N08**: after `allowing_private_addresses`, a class is allowed exactly when it was
allowed before or it is `Private`; in particular the loopback policy is unchanged and blocked
addresses stay refused. Covers only a successful call of `allowing_private_addresses`. -/
theorem MetadataAddressResolver.is_allowed_of_allowing_private_addresses_eq_ok
    (self r : MetadataAddressResolver)
    (h : MetadataAddressResolver.allowing_private_addresses self = ok r) (c : AddressClass) :
    MetadataAddressResolver.is_allowed c r.base_classes.data ⦃ (result : Bool) =>
      result = (isAllowed c self.base_classes.data.val || decide (c = .Private)) ⦄ := by
  obtain ⟨e1, -⟩ := allowing_private_addresses_of_eq_ok self r h
  have hc := is_allowed_eq c r.base_classes.data
  rw [hc, WP.spec_ok, e1]
  cases c <;>
    simp only [isAllowed, withPrivate, reduceCtorEq, decide_false, decide_true, Bool.or_false,
      Bool.or_true, Bool.or_self] <;>
    split <;> simp_all

/-- **N06 is idempotent**: calling `allowing_private_addresses` twice is calling it once (the
second call finds `Private` and returns its argument, line 151). An equation between
computations, failure included. -/
theorem MetadataAddressResolver.allowing_private_addresses_idem (self : MetadataAddressResolver) :
    (do
      let r ← MetadataAddressResolver.allowing_private_addresses self
      MetadataAddressResolver.allowing_private_addresses r) =
      MetadataAddressResolver.allowing_private_addresses self := by
  cases h : MetadataAddressResolver.allowing_private_addresses self using Result.cases with
  | ret r =>
    rw [bind_ok]
    have hm : AddressClass.Private ∈ r.base_classes.data.val := by
      rw [(allowing_private_addresses_of_eq_ok self r h).1, withPrivate]; split <;> simp_all
    exact allowing_private_addresses_eq_ok_self r hm
  | vis i k =>
    rw [bind_vis]; congr 1; funext x; cases i; exact x.elim
  | div => rw [bind_div]

/-- **N03 then N06, `new_allowing_private_addresses` builds its resolver whenever `new` does**
(`auth.rs` line 1527: `new(&base_url).allowing_private_addresses()`; finding R3 of spec round 3):
if `new base_url` returns `r₀`, then `allowing_private_addresses r₀` succeeds. The base URL
grants at most one class (`new_fields_of_eq_ok`, `length_baseClasses_le_one`, upstream lines
112–119), so the premise of `allowing_private_addresses_spec` (patched line 155) holds. With
`new base_url = ok r₀` this discharges the hypothesis
`(do let r₀ ← new base_url; allowing_private_addresses r₀) = ok r` of the four
`…_of_new_allowing_private_addresses_eq_ok` theorems. Covers only a successful call of `new`.
No premise. -/
theorem MetadataAddressResolver.exists_allowing_private_addresses_eq_ok_of_new_eq_ok
    (base_url : url.Url) (r₀ : MetadataAddressResolver)
    (h : MetadataAddressResolver.new base_url = ok r₀) :
    ∃ r, MetadataAddressResolver.allowing_private_addresses r₀ = ok r := by
  obtain ⟨-, f2, -⟩ := new_fields_of_eq_ok base_url r₀ h
  have hl := length_baseClasses_le_one (ExtModel.urlHost base_url)
  have hu : 1 < Usize.max := by
    have : U32.max ≤ Usize.max := by
      simp only [U32.max, Usize.max, U32.numBits, Usize.numBits]
      rcases System.Platform.numBits_eq with h | h <;> simp [h]
    have : 1 < U32.max := by simp [U32.max, U32.numBits]
    omega
  obtain ⟨r, h1, -⟩ := exists_allowing_private_addresses_eq_ok r₀ (Or.inr (by rw [f2]; omega))
  exact ⟨r, h1⟩

/-! ### `allows_url` (N07 with N03, N04, N06, N10)

The checks of every OAuth request (`execute`, `auth.rs` line 193) and of every redirect (the
redirect policy, line 160), on the resolver of `AuthorizationManager::new` (line 1513) or of
`new_allowing_private_addresses` (line 1527). -/

/-- **N04 then N07, the base URL's own literal is always allowed** (doc comment, upstream lines
162–163): the resolver built from `base_url` allows `base_url` itself, whatever its class (also
a blocked one, such as a link-local literal). Covers only a successful call of
`with_base_url`. -/
theorem MetadataAddressResolver.allows_url_self_of_with_base_url_eq_ok (base_url : url.Url)
    (lookup : Lookup) (r : MetadataAddressResolver)
    (h : MetadataAddressResolver.with_base_url base_url lookup = ok r) :
    MetadataAddressResolver.allows_url r base_url = ok true := by
  obtain ⟨f1, -, f3, -⟩ := with_base_url_of_eq_ok _ _ _ h
  obtain ⟨b, hb, hbv⟩ := exists_ok_of_spec (allows_url_spec r base_url)
  rw [hb, hbv, f1, f3, allowsHost_literalIp_self]

/-- **N03 then N07, the base URL itself is always allowed in production**
(`AuthorizationManager::new`, `auth.rs` line 1513; the checks of the redirect policy, line 160,
and of `execute`, line 193; doc comment of `allows_url`, upstream lines 162–163, and line 167):
the resolver that `new base_url` returns allows `base_url` itself, whatever its host and class
(also a blocked literal, such as a link-local one), for every value of
`ExtModel.proxyEnvValues`. From `allows_url_of_new_eq_ok` and `allowsHost_literalIp_self`.
Covers only a successful call of `new`. No premise. -/
theorem MetadataAddressResolver.allows_url_self_of_new_eq_ok (base_url : url.Url)
    (r : MetadataAddressResolver) (h : MetadataAddressResolver.new base_url = ok r) :
    MetadataAddressResolver.allows_url r base_url = ok true := by
  obtain ⟨f1, f2, -⟩ := new_fields_of_eq_ok base_url r h
  obtain ⟨b, hb, hbv⟩ := exists_ok_of_spec (allows_url_spec r base_url)
  rw [hb, hbv, f1, f2, allowsHost_literalIp_self]

/-- **N04 then N07, a public base name allows only public literals**: for a base URL whose host
is a domain other than a `localhost` name, the resolver allows a target exactly when its host
is not an IP literal or the literal is `Public` (loopback, private and blocked literals,
including embedded ones, are refused; for `Public`, see the header). Covers only a successful
call of `with_base_url`. -/
theorem MetadataAddressResolver.allows_url_iff_public_of_with_base_url_eq_ok
    (base_url : url.Url) (lookup : Lookup) (r : MetadataAddressResolver) (d : Str)
    (h_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (h_name : isLocalhostName d.val = false)
    (h : MetadataAddressResolver.with_base_url base_url lookup = ok r) (target : url.Url) :
    MetadataAddressResolver.allows_url r target ⦃ (result : Bool) =>
      (result = true ↔
        ∀ ip, literalIp (ExtModel.urlHost target) = some ip →
          addressClass ip = .Public) ⦄ := by
  obtain ⟨f1, -, f3, -⟩ := with_base_url_of_eq_ok _ _ _ h
  apply WP.spec_mono (allows_url_spec r target)
  intro b hb
  rw [hb, f1, f3, h_host]
  have h0 : literalIp (some (url.host.Host.Domain d)) = none := rfl
  simp only [h0, baseClasses, h_name, Bool.false_eq_true, ↓reduceIte, allowsHost]
  cases literalIp (ExtModel.urlHost target) with
  | none => simp
  | some ip => cases hc : addressClass ip <;> simp [isAllowed, hc]

/-- **N03 then N07, the policy of `AuthorizationManager::new`** (`auth.rs` line 1513; the checks
of lines 160 and 193): the resolver that `new base_url` returns decides a target by the base
URL's own literal and the classes the base URL grants (`allowsHost` with `literalIp` and
`baseClasses` of the base URL's host), for every value of `ExtModel.proxyEnvValues` (the proxy
values change only the unfiltered hosts). Covers only a successful call of `new`. -/
theorem MetadataAddressResolver.allows_url_of_new_eq_ok (base_url : url.Url)
    (r : MetadataAddressResolver) (h : MetadataAddressResolver.new base_url = ok r)
    (target : url.Url) :
    MetadataAddressResolver.allows_url r target ⦃ (result : Bool) =>
      result = allowsHost (literalIp (ExtModel.urlHost base_url))
        (baseClasses (ExtModel.urlHost base_url)) (ExtModel.urlHost target) ⦄ := by
  obtain ⟨f1, f2, -⟩ := new_fields_of_eq_ok base_url r h
  apply WP.spec_mono (allows_url_spec r target)
  intro b hb; rw [hb, f1, f2]

/-- **N03 then N07, a public base name allows only public literals in production**
(`AuthorizationManager::new`, `auth.rs` line 1513; the checks of lines 160 and 193): for a base
URL whose host is a domain other than a `localhost` name, the resolver that `new base_url`
returns allows a target exactly when its host is not an IP literal or the literal is `Public`.
For `Public`, see the header. For every value of `ExtModel.proxyEnvValues`. Covers only a
successful call of `new`. -/
theorem MetadataAddressResolver.allows_url_iff_public_of_new_eq_ok (base_url : url.Url)
    (r : MetadataAddressResolver) (d : Str)
    (h_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (h_name : isLocalhostName d.val = false)
    (h : MetadataAddressResolver.new base_url = ok r) (target : url.Url) :
    MetadataAddressResolver.allows_url r target ⦃ (result : Bool) =>
      (result = true ↔
        ∀ ip, literalIp (ExtModel.urlHost target) = some ip →
          addressClass ip = .Public) ⦄ := by
  apply WP.spec_mono (allows_url_of_new_eq_ok base_url r h target)
  intro b hb
  rw [hb, h_host]
  have h0 : literalIp (some (url.host.Host.Domain d)) = none := rfl
  simp only [h0, baseClasses, h_name, Bool.false_eq_true, ↓reduceIte, allowsHost]
  cases literalIp (ExtModel.urlHost target) with
  | none => simp
  | some ip => cases hc : addressClass ip <;> simp [isAllowed, hc]

/-- **N03, N06 then N07, the policy of `new_allowing_private_addresses`** (`auth.rs` line 1527:
`new(&base_url).allowing_private_addresses()`; the checks of lines 160 and 193): the resolver
decides a target by the base URL's own literal and the classes the base URL grants with
`Private` added (`withPrivate`, upstream lines 150–160), for every value of
`ExtModel.proxyEnvValues`. Covers only a successful call of the composition. -/
theorem MetadataAddressResolver.allows_url_of_new_allowing_private_addresses_eq_ok
    (base_url : url.Url) (r : MetadataAddressResolver)
    (h : (do
      let r₀ ← MetadataAddressResolver.new base_url
      MetadataAddressResolver.allowing_private_addresses r₀) = ok r)
    (target : url.Url) :
    MetadataAddressResolver.allows_url r target ⦃ (result : Bool) =>
      result = allowsHost (literalIp (ExtModel.urlHost base_url))
        (withPrivate (baseClasses (ExtModel.urlHost base_url))) (ExtModel.urlHost target) ⦄ := by
  obtain ⟨r₀, h0, h⟩ := bind_eq_ok_iff.1 h
  obtain ⟨f1, f2, -⟩ := new_fields_of_eq_ok base_url r₀ h0
  obtain ⟨e1, e2, -, -⟩ := allowing_private_addresses_of_eq_ok r₀ r h
  apply WP.spec_mono (allows_url_spec r target)
  intro b hb; rw [hb, e1, e2, f1, f2]

/-- **N03, N06 then N07, a public base name allows public and private literals only**
(`new_allowing_private_addresses`, `auth.rs` line 1527; the checks of lines 160 and 193): for a
base URL whose host is a domain other than a `localhost` name, the resolver allows a target
exactly when its host is not an IP literal or the literal is `Public` or `Private` (loopback
and blocked literals, including embedded ones, are refused; for `Public`, see the header). For
every value of `ExtModel.proxyEnvValues`. Covers only a successful call of the composition. -/
theorem
    MetadataAddressResolver.allows_url_iff_public_or_private_of_new_allowing_private_addresses_eq_ok
    (base_url : url.Url) (r : MetadataAddressResolver) (d : Str)
    (h_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (h_name : isLocalhostName d.val = false)
    (h : (do
      let r₀ ← MetadataAddressResolver.new base_url
      MetadataAddressResolver.allowing_private_addresses r₀) = ok r)
    (target : url.Url) :
    MetadataAddressResolver.allows_url r target ⦃ (result : Bool) =>
      (result = true ↔
        ∀ ip, literalIp (ExtModel.urlHost target) = some ip →
          addressClass ip = .Public ∨ addressClass ip = .Private) ⦄ := by
  apply WP.spec_mono (allows_url_of_new_allowing_private_addresses_eq_ok base_url r h target)
  intro b hb
  rw [hb, h_host]
  have h0 : literalIp (some (url.host.Host.Domain d)) = none := rfl
  simp only [h0, baseClasses, h_name, Bool.false_eq_true, ↓reduceIte, allowsHost, withPrivate]
  cases literalIp (ExtModel.urlHost target) with
  | none => simp
  | some ip => cases hc : addressClass ip <;> simp [isAllowed, hc]

/-- **N07 refuses blocked literals**: a target whose IP literal is `Blocked` and is not the
base URL's own literal is refused, whatever the granted classes. -/
theorem MetadataAddressResolver.allows_url_eq_false_of_blocked (self : MetadataAddressResolver)
    (target : url.Url) (ip : core.net.ip_addr.IpAddr)
    (h_ip : literalIp (ExtModel.urlHost target) = some ip)
    (h_blocked : addressClass ip = .Blocked) (h_base : self.base_ip ≠ some ip) :
    MetadataAddressResolver.allows_url self target ⦃ (result : Bool) => result = false ⦄ := by
  apply WP.spec_mono (allows_url_spec self target)
  intro b hb
  rw [hb, allowsHost, h_ip]
  simp [h_base, h_blocked, isAllowed]

/-! ### `resolve` (N09 with N01, N08, N03, N04, N06)

Every name that an OAuth request or redirect resolves goes through `resolve` (upstream lines
190–212), whose pure part is `allowed_addresses`. -/

/-- **N09: every address returned for a filtered host passes `is_allowed`**: if
`allowed_addresses` returns `some v` for a host that is not unfiltered, then for every address
`a` of `v`, `is_allowed (AddressClass::of a.ip()) base_classes` returns `true` (the check of
upstream line 201). Covers only a successful call of `allowed_addresses` returning `some`. -/
theorem MetadataAddressResolver.is_allowed_of_mem_of_allowed_addresses_eq_ok
    (self : MetadataAddressResolver) (host : String)
    (resolved v : alloc.vec.Vec core.net.socket_addr.SocketAddr)
    (h : MetadataAddressResolver.allowed_addresses self host resolved = ok (some v))
    (h_host : host ∉ self.unfiltered_hosts.data.val)
    (a : core.net.socket_addr.SocketAddr) (ha : a ∈ v.val) :
    (do
      let ip ← core.net.socket_addr.SocketAddr.ip a
      let c ← AddressClass.of ip
      MetadataAddressResolver.is_allowed c self.base_classes.data) = ok true := by
  obtain ⟨o, ho, hov⟩ := exists_ok_of_spec (allowed_addresses_spec self host resolved)
  rw [h, ok.injEq] at ho; subst ho
  have hv : allowedAddresses self.unfiltered_hosts.data.val self.base_classes.data.val host
      resolved.val = some v.val := by
    rw [← hov]; rfl
  have := allAllowed_of_allowedAddresses_eq_some hv h_host a ha
  rw [ip_eq_socketIp, bind_ok, of_eq, bind_ok, is_allowed_eq, this]

/-- **N04 then N09, a public base name lets only public addresses through** (module docstring,
lines 4–7: "the base host's DNS answers never widen the policy"): for the resolver built by
`with_base_url` from a base URL whose host is a domain other than a `localhost` name, every
address `allowed_addresses` returns is `Public` (`AllPublic`; there is no unfiltered host before
`with_proxy_hosts`). For `Public`, see the header. Covers
only successful calls of `with_base_url` and of `allowed_addresses` returning `some`. -/
theorem MetadataAddressResolver.allPublic_of_with_base_url_eq_ok
    (base_url : url.Url) (lookup : Lookup) (r : MetadataAddressResolver) (d : Str)
    (h_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (h_name : isLocalhostName d.val = false)
    (h : MetadataAddressResolver.with_base_url base_url lookup = ok r) (host : String)
    (resolved v : alloc.vec.Vec core.net.socket_addr.SocketAddr)
    (h_res : MetadataAddressResolver.allowed_addresses r host resolved = ok (some v)) :
    AllPublic v.val := by
  obtain ⟨-, f2, f3, -⟩ := with_base_url_of_eq_ok _ _ _ h
  obtain ⟨o, ho, hov⟩ := exists_ok_of_spec (allowed_addresses_spec r host resolved)
  rw [h_res, ok.injEq] at ho; subst ho
  have hv : allowedAddresses r.unfiltered_hosts.data.val r.base_classes.data.val host
      resolved.val = some v.val := by
    rw [← hov]; rfl
  have hall := allAllowed_of_allowedAddresses_eq_some hv (by rw [f2]; simp)
  intro a ha
  have := hall a ha
  rw [f3, h_host] at this
  simp only [baseClasses, h_name, Bool.false_eq_true, ↓reduceIte] at this
  exact eq_public_of_isAllowed (by simp) (by simp) this

/-- **N03 then N09, the addresses `AuthorizationManager::new` lets through**
(`auth.rs` line 1513): for the resolver that `new base_url` builds, every address
`allowed_addresses` returns for a host that is not a configured proxy host is allowed by the
classes the base URL grants (`AllAllowed` of `baseClasses`), for every value of
`ExtModel.proxyEnvValues`. Covers only successful calls of `new` and of `allowed_addresses`
returning `some`. -/
theorem MetadataAddressResolver.allAllowed_of_new_eq_ok
    (base_url : url.Url) (r : MetadataAddressResolver)
    (h : MetadataAddressResolver.new base_url = ok r) (host : String)
    (h_unfiltered : host ∉ r.unfiltered_hosts.data.val)
    (resolved v : alloc.vec.Vec core.net.socket_addr.SocketAddr)
    (h_res : MetadataAddressResolver.allowed_addresses r host resolved = ok (some v)) :
    AllAllowed (baseClasses (ExtModel.urlHost base_url)) v.val := by
  obtain ⟨-, f2, -⟩ := new_fields_of_eq_ok base_url r h
  obtain ⟨o, ho, hov⟩ := exists_ok_of_spec (allowed_addresses_spec r host resolved)
  rw [h_res, ok.injEq] at ho; subst ho
  have hv : allowedAddresses r.unfiltered_hosts.data.val r.base_classes.data.val host
      resolved.val = some v.val := by
    rw [← hov]; rfl
  rw [← f2]; exact allAllowed_of_allowedAddresses_eq_some hv h_unfiltered

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
theorem MetadataAddressResolver.allPublic_of_new_eq_ok
    (base_url : url.Url) (r : MetadataAddressResolver) (d : Str)
    (h_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (h_name : isLocalhostName d.val = false)
    (h : MetadataAddressResolver.new base_url = ok r) (host : String)
    (h_unfiltered : host ∉ r.unfiltered_hosts.data.val)
    (resolved v : alloc.vec.Vec core.net.socket_addr.SocketAddr)
    (h_res : MetadataAddressResolver.allowed_addresses r host resolved = ok (some v)) :
    AllPublic v.val := by
  have hall := allAllowed_of_new_eq_ok base_url r h host h_unfiltered resolved v h_res
  intro a ha
  have := hall a ha
  rw [h_host] at this
  simp only [baseClasses, h_name, Bool.false_eq_true, ↓reduceIte] at this
  exact eq_public_of_isAllowed (by simp) (by simp) this

/-- **N03, N06 then N09, the addresses `new_allowing_private_addresses` lets through**
(`auth.rs` line 1527: `new(&base_url).allowing_private_addresses()`): for that resolver, every
address `allowed_addresses` returns for a host that is not a configured proxy host is allowed by
the classes the base URL grants with `Private` added (`AllAllowed` of `withPrivate`): `Public`,
`Private`, and `Loopback` only if the base URL grants it (`loopback_mem_baseClasses_iff`);
never `Blocked`. For every value of `ExtModel.proxyEnvValues`. Covers only successful calls of
the composition and of `allowed_addresses` returning `some`. -/
theorem MetadataAddressResolver.allAllowed_of_new_allowing_private_addresses_eq_ok
    (base_url : url.Url) (r : MetadataAddressResolver)
    (h : (do
      let r₀ ← MetadataAddressResolver.new base_url
      MetadataAddressResolver.allowing_private_addresses r₀) = ok r)
    (host : String) (h_unfiltered : host ∉ r.unfiltered_hosts.data.val)
    (resolved v : alloc.vec.Vec core.net.socket_addr.SocketAddr)
    (h_res : MetadataAddressResolver.allowed_addresses r host resolved = ok (some v)) :
    AllAllowed (withPrivate (baseClasses (ExtModel.urlHost base_url))) v.val := by
  obtain ⟨r₀, h0, h⟩ := bind_eq_ok_iff.1 h
  obtain ⟨-, f2, -⟩ := new_fields_of_eq_ok base_url r₀ h0
  obtain ⟨e1, -, -, -⟩ := allowing_private_addresses_of_eq_ok r₀ r h
  obtain ⟨o, ho, hov⟩ := exists_ok_of_spec (allowed_addresses_spec r host resolved)
  rw [h_res, ok.injEq] at ho; subst ho
  have hv : allowedAddresses r.unfiltered_hosts.data.val r.base_classes.data.val host
      resolved.val = some v.val := by
    rw [← hov]; rfl
  rw [← f2, ← e1]; exact allAllowed_of_allowedAddresses_eq_some hv h_unfiltered

/-- **N03, N06 then N09, the production guarantee of `new_allowing_private_addresses`**
(`auth.rs` line 1527; its doc comment, lines 1517–1521: "Loopback addresses still need a
loopback base URL, and link-local and other reserved addresses stay rejected"): from a base URL
whose host is a domain other than a `localhost` name, every address `allowed_addresses` returns
for a host that is not a configured proxy host is `Public` or `Private`
(`AllPublicOrPrivate`): no loopback and no blocked address. For `Public`, see the header. For
every value of `ExtModel.proxyEnvValues`. Covers only
successful calls of the composition and of `allowed_addresses` returning `some`. -/
theorem MetadataAddressResolver.allPublicOrPrivate_of_new_allowing_private_addresses_eq_ok
    (base_url : url.Url) (r : MetadataAddressResolver) (d : Str)
    (h_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (h_name : isLocalhostName d.val = false)
    (h : (do
      let r₀ ← MetadataAddressResolver.new base_url
      MetadataAddressResolver.allowing_private_addresses r₀) = ok r)
    (host : String) (h_unfiltered : host ∉ r.unfiltered_hosts.data.val)
    (resolved v : alloc.vec.Vec core.net.socket_addr.SocketAddr)
    (h_res : MetadataAddressResolver.allowed_addresses r host resolved = ok (some v)) :
    AllPublicOrPrivate v.val := by
  have hall := allAllowed_of_new_allowing_private_addresses_eq_ok base_url r h host h_unfiltered
    resolved v h_res
  intro a ha
  have := hall a ha
  rw [h_host] at this
  simp only [baseClasses, h_name, Bool.false_eq_true, ↓reduceIte, withPrivate] at this
  cases hc : addressClass (socketIp a) <;> simp_all [isAllowed]

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
theorem MetadataAddressResolver.allowed_addresses_eq_ok_some_of_new_eq_ok_of_mem_proxyHosts
    (base_url : url.Url) (r : MetadataAddressResolver)
    (h : MetadataAddressResolver.new base_url = ok r) (host : String)
    (h_proxy : Defs.utf8Bytes host ∈
      ExtModel.proxyEnvValues.val.filterMap (proxyHost ∘ Defs.utf8Bytes))
    (resolved : alloc.vec.Vec core.net.socket_addr.SocketAddr) :
    MetadataAddressResolver.allowed_addresses r host resolved = ok (some resolved) := by
  have hm := (mem_unfiltered_hosts_iff_of_new_eq_ok base_url r h host).2 h_proxy
  unfold MetadataAddressResolver.allowed_addresses
  simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, bind_ok, contains_string]
  simp [hm]

/-! ### Normalization (N11) -/

/-- **N11 is idempotent**: normalizing the (dereferenced) result of `normalize_host` gives the
same string. An equation between computations, failure included (both sides fail with
`undef` on bytes that are not UTF-8), so no premise. -/
theorem normalize_host_idem (host : Str) :
    (do
      let r ← normalize_host host
      let s ← alloc.string.String.Insts.CoreOpsDerefDerefStr.deref r
      normalize_host s) = normalize_host host := by
  cases hn : normalize_host host using Result.cases with
  | ret r =>
    rw [bind_ok]
    obtain ⟨h1, _⟩ := normalize_host_of_eq_ok hn
    have hsz : r.utf8ByteSize ≤ Usize.max := by
      rw [← length_utf8, h1]; exact le_trans (length_normalizeHost_le _) host.property
    rw [deref_eq r hsz, bind_ok_str,
      normalize_host_eq (Slice.from (utf8 r) (by rw [length_utf8]; exact hsz))]
    rw [Slice.from_val, h1, normalizeHost_idem, ← h1, strOfBytes?_utf8]
  | vis i k => rw [bind_vis]; congr 1; funext x; cases i; exact x.elim
  | div => rw [bind_div]

end rmcp.transport.auth.metadata_resolver
