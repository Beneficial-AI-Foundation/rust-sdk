/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Proofs.Transport.AuthMetadata.Common

@[expose] public section

/-!
# Spec theorems for the OAuth metadata URL and issuer checks (A04–A10)

The private checks of `AuthorizationManager` in `crates/rmcp/src/transport/auth.rs` that
translation patch 06 makes translatable (human decisions AD1–AD8): A04 `is_http_url`, the
same-origin check `is_same_origin`, A05 `is_disallowed_metadata_host` with
`is_disallowed_metadata_hostname`, A06 `is_allowed_metadata_url` with its patch helper
`is_allowed_disallowed_host`, A07 `resolve_resource_metadata_url`, A08
`check_authorization_response_issuer`, A09 `check_authorization_metadata_issuer` with
`expected_issuer_for_authorization_metadata_url`, `issuer_identifiers_match`, `trim_root_slash`
and `is_root_url`, and A10 `check_resource_metadata_resource` with
`is_resource_identifier_valid`. Then the laws of the definitions of `Defs.AuthMetadata` and the
composition theorems (the security meaning end to end, and the "on success" facts).

The statements are the ones signed off by the human spec owner on 2026-11-27 (statements
unchanged); they are restated, as `Theorems.auth.AuthorizationManager.*` and, for the laws,
`Theorems.auth.*`, in `Proofs.Internal.Transport.Auth.AuthMetadata`, with the recorded bugs
H9–H16 and the premise keys. The law of the trusted model `trimWhitespace_utf8Bytes` is proved
in `Proofs.External.Auth`. Each spec theorem is proved through the equations of
`Proofs.Transport.AuthMetadata.Common`; the compositions combine the spec theorems with the laws.
The documented premises that the models do not need (AD7 `h_fits`, `h_discovery`; AD8
`h_scheme`) are consumed with `have _ := …`, so the statement text stays unchanged.

Source: "crates/rmcp/src/transport/auth.rs", upstream `7caec76` lines 1330–1473 (A04–A07) and
2320–3021 (A08–A10, the bodies of the `validate_*` wrappers), translated through
`formal/trusted/patches/06-auth-metadata.patch` (patched lines 1325–1486 and 2342–3063)
-/

open Aeneas Aeneas.Std Result
open rmcp
open Defs (utf8Bytes)
open Defs.AuthMetadata Defs.MetadataResolver Defs.Net
open rmcp.transport.auth.metadata_resolver (AddressClass)
open rmcp.transport.auth (IssuerError StoredAuthorizationState AuthorizationMetadata
  ResourceServerMetadata ProtectedResourceMetadataInvalidReason)
open ExtModel Proofs.External.Utf8 Proofs.External.WP Proofs.External.MetadataResolver
open Proofs.Transport.MetadataResolver
open Proofs.Transport.AuthMetadata hiding knownDefaultPort_eq_defaultPort trim_root_slash_fail
open rmcp.transport.auth.AuthorizationManager.is_allowed_disallowed_host.closure.Insts

set_option autoImplicit false

namespace rmcp.transport.auth.AuthorizationManager

/-! ## A04 `is_http_url` (upstream lines 1330–1332; patched 1325–1327) -/

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::is_http_url`** (A04)

Never fails. `true` exactly when the URL's scheme is `http` or `https` and it has a host string
(`Defs.AuthMetadata.isHttpUrl`; `matches!(url.scheme(), "http" | "https") &&
url.host_str().is_some()`). No premise. -/
@[step]
theorem is_http_url_spec (target : url.Url) :
    is_http_url target ⦃ (result : Bool) =>
      result = isHttpUrl target ⦄ := by
  rw [is_http_url_eq, WP.spec_ok]

/-! ## `is_same_origin` (callee of A07; upstream lines 1334–1341, patched 1329–1336) -/

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::is_same_origin`** (callee of
A07)

Never fails. `true` exactly when the schemes have the same bytes, both URLs have a host string
and the two are equal up to ASCII case (`str::eq_ignore_ascii_case`), and the ports or known
default ports are equal (`Defs.AuthMetadata.isSameOrigin`). No premise. -/
@[step]
theorem is_same_origin_spec (base candidate : url.Url) :
    is_same_origin base candidate ⦃ (result : Bool) =>
      result = isSameOrigin base candidate ⦄ := by
  rw [is_same_origin_eq, WP.spec_ok]

/-! ## A05 `is_disallowed_metadata_host` (upstream lines 1385–1399; patched 1380–1397) -/

/-- **Spec theorem for
`rmcp::transport::auth::AuthorizationManager::is_disallowed_metadata_hostname`** (callee of A05)

Never fails. `true` exactly when the bytes are `localhost`, end in `.localhost`, or are one of
`metadata`, `metadata.google.internal`, `metadata.azure.internal`, compared byte for byte
(`Defs.AuthMetadata.isDisallowedHostname`; upstream lines 1385–1389, the constant
`CLOUD_METADATA_HOSTS` of lines 39–43 inlined by the first hunk of patch 06, hunk H1 in the
patch header). No normalization here: the only caller passes a normalized name. No premise. -/
@[step]
theorem is_disallowed_metadata_hostname_spec (host : Str) :
    is_disallowed_metadata_hostname host ⦃ (result : Bool) =>
      result = isDisallowedHostname host.val ⦄ := by
  rw [is_disallowed_metadata_hostname_eq, WP.spec_ok]

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::is_disallowed_metadata_host`**
(A05)

For a host whose domain, if any, is UTF-8 (rule (ii)(a): the `&str` of the argument
`Host<&str>`), never fails: for a domain, `true` exactly when after removing trailing dots and
lowercasing ASCII letters (`normalizeHost`, line 1394) it is `localhost`, ends in `.localhost`
(RFC 6761 §6.3), or is a cloud-metadata name; for an IPv4 literal, A02 (`ipv4Disallowed`); for an
IPv6 literal, A03 (`ipv6Disallowed`, which decides an IPv4-mapped, NAT64, IPv4-compatible or
6to4 address by its embedded IPv4 address) (`Defs.AuthMetadata.isDisallowedHost`). The
premise is the weakest (`is_disallowed_metadata_host_fail`). H11 (recorded bug): the
IPv4-translated range `::ffff:0:0:0/96`, `100::/64` and `192.0.0.192` are not rejected. -/
@[step]
theorem is_disallowed_metadata_host_spec (host : url.host.Host Str)
    (h_utf8 : ∀ d, host = url.host.Host.Domain d → ExtModel.IsUtf8 d.val) :
    is_disallowed_metadata_host host ⦃ (result : Bool) =>
      result = isDisallowedHost host ⦄ := by
  rw [is_disallowed_metadata_host_eq host h_utf8, WP.spec_ok]

/-- **`is_disallowed_metadata_host`, the UTF-8 premise is the weakest**: for a domain whose bytes
are not UTF-8 (no Rust `&str`), `to_ascii_lowercase` (upstream line 1394, patched 1392) fails,
so the call fails with `undef`. -/
theorem is_disallowed_metadata_host_fail (d : Str) (h : ¬ ExtModel.IsUtf8 d.val) :
    is_disallowed_metadata_host (url.host.Host.Domain d) = fail .undef := by
  rw [is_disallowed_metadata_host_domain_eq]
  cases hs : strOfBytes? (normalizeHost d.val) with
  | none => rfl
  | some s =>
    exfalso; apply h
    rw [strOfBytes?_eq_some_iff, normalizeHost_eq_map_dropTrailingDots] at hs
    exact isUtf8_of_isUtf8_dropTrailingDots (isUtf8_of_isUtf8_map_asciiLowercase ⟨s, hs⟩)

/-! ## A06 `is_allowed_metadata_url` (upstream lines 1412–1436; patched 1410–1430, with
`is_allowed_disallowed_host`, patched 1433–1447) -/

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::is_allowed_metadata_url`**
(A06)

If the target, when it is HTTP(S) with a host string, has a UTF-8 domain (if any), and the base
URL's domain, if any, is UTF-8 (rule (ii)(b)), never fails. The result, in the Rust order of
checks (`Defs.AuthMetadata.isAllowedMetadataUrl`): `false` unless the target is HTTP(S) with a
host string (A04, lines 1413–1415); `false` without a host (lines 1417–1419); `true` if the
guard does not reject the host (A05, lines 1421–1423); otherwise `true` exactly when
`allow_private` holds and the host is a `Private` literal (lines 1425–1432), or the base URL's
host and the target's host are both loopback hosts (lines 1434–1435). The target premise is the
weakest (`is_allowed_metadata_url_fail`); the base premise is needed only when the base host is
read (`is_allowed_metadata_url_fail_base`). H12 (recorded bug): for some targets this refuses
what the resolver policy allows, and for IP-literal targets it is never looser
(`allowsHost_of_isAllowedMetadataUrl`; cases in the module docstring of
`Proofs.Defs.AuthMetadata`). H16 (recorded bug): the cloud-metadata names are only three. -/
@[step]
theorem is_allowed_metadata_url_spec (base_url target : url.Url) (allow_private : Bool)
    (h_base : HostUtf8 base_url) (h_target : isHttpUrl target = true → HostUtf8 target) :
    is_allowed_metadata_url base_url target allow_private ⦃ (result : Bool) =>
      result = isAllowedMetadataUrl base_url target allow_private ⦄ := by
  rw [is_allowed_metadata_url_eq]
  unfold isAllowedMetadataUrl
  cases hh : isHttpUrl target
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, WP.spec_ok]
  · simp only [↓reduceIte, Bool.true_and]
    cases ht : ExtModel.urlHost target with
    | none => simp only [WP.spec_ok]
    | some h =>
      have hu : ∀ d, h = url.host.Host.Domain d → IsUtf8 d.val :=
        fun d hd => h_target hh d (ht.trans (by rw [hd]))
      simp only [is_disallowed_metadata_host_eq h hu, bind_ok]
      cases hd : isDisallowedHost h
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_or, WP.spec_ok]
      · simp only [↓reduceIte, Bool.not_true, Bool.false_or]
        rw [is_allowed_disallowed_host_eq base_url h allow_private h_base hu, WP.spec_ok]

/-- **`is_allowed_metadata_url`, the target premise is the weakest**: for an HTTP(S) target with
a host string whose host is a domain that is not UTF-8, the guard (A05, upstream line 1421)
fails, so the call fails with `undef`. -/
theorem is_allowed_metadata_url_fail (base_url target : url.Url) (allow_private : Bool) (d : Str)
    (h_http : isHttpUrl target = true)
    (h_host : ExtModel.urlHost target = some (url.host.Host.Domain d))
    (h : ¬ ExtModel.IsUtf8 d.val) :
    is_allowed_metadata_url base_url target allow_private = fail .undef := by
  rw [is_allowed_metadata_url_eq]
  simp only [h_http, ↓reduceIte, h_host]
  rw [is_disallowed_metadata_host_fail d h, bind_fail]

/-- **`is_allowed_metadata_url`, when the base premise is needed**: for an HTTP(S) target whose
host is rejected by the guard and not exempted as a `Private` literal with `allow_private`, the
base URL's host is read (upstream line 1434, `is_loopback_metadata_host` on it); if it is a
domain that is not UTF-8, the call fails with `undef`. No premise on the target's domain: if it
is not UTF-8, the guard (upstream line 1421) already fails with `undef`
(`is_allowed_metadata_url_fail`). -/
theorem is_allowed_metadata_url_fail_base (base_url target : url.Url) (allow_private : Bool)
    (h : url.host.Host Str) (d : Str)
    (h_http : isHttpUrl target = true) (h_host : ExtModel.urlHost target = some h)
    (h_dis : isDisallowedHost h = true)
    (h_priv : ¬ (allow_private = true ∧ (hostIp h).map addressClass = some AddressClass.Private))
    (h_base_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (hd : ¬ ExtModel.IsUtf8 d.val) :
    is_allowed_metadata_url base_url target allow_private = fail .undef := by
  rw [is_allowed_metadata_url_eq]
  simp only [h_http, ↓reduceIte, h_host]
  -- the guard either fails (a non-UTF-8 domain target) or returns `true`
  have hg :
      is_disallowed_metadata_host h = fail .undef ∨ is_disallowed_metadata_host h = ok true := by
    cases h with
    | Domain t =>
      rw [is_disallowed_metadata_host_domain_eq]
      cases strOfBytes? (normalizeHost t.val)
      · left; rfl
      · right; rw [h_dis]
    | Ipv4 a => right; rw [is_disallowed_metadata_host_eq _ (by intro _ h; cases h), h_dis]
    | Ipv6 a => right; rw [is_disallowed_metadata_host_eq _ (by intro _ h; cases h), h_dis]
  rcases hg with hg | hg
  · rw [hg, bind_fail]
  · rw [hg, bind_ok]
    simp only [↓reduceIte]
    have hbase : core.option.Option.is_some_and
        CoreOpsFunctionFnOnceTupleHostShared0StrBool
        (ExtModel.urlHost base_url) () = fail .undef := by
      rw [h_base_host]
      exact is_loopback_metadata_host_domain_eq_fail d hd
    have rest : ∀ c : Option AddressClass, c = (hostIp h).map addressClass →
        (if allow_private = true then do
            let b ← core.option.Option.Insts.CoreCmpPartialEqOption.eq
              AddressClass.Insts.CoreCmpPartialEqAddressClass c (some AddressClass.Private)
            if b = true then ok true
              else do
                let o ← url.Url.host base_url
                let b1 ← core.option.Option.is_some_and
                  CoreOpsFunctionFnOnceTupleHostShared0StrBool o ()
                if b1 = true then is_loopback_metadata_host h else ok false
          else do
            let o ← url.Url.host base_url
            let b ← core.option.Option.is_some_and
              CoreOpsFunctionFnOnceTupleHostShared0StrBool o ()
            if b = true then is_loopback_metadata_host h else ok false) = fail .undef := by
      intro c hc
      simp only [url.Url.host, bind_ok, hbase, bind_fail]
      cases allow_private with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]
      | true =>
        simp only [↓reduceIte]
        have hnp : c ≠ some AddressClass.Private := by
          intro e; apply h_priv; exact ⟨rfl, hc ▸ e⟩
        cases c with
        | none => simp only [core.option.Option.Insts.CoreCmpPartialEqOption.eq, bind_ok,
          Bool.false_eq_true, ↓reduceIte]
        | some c =>
          simp only [core.option.Option.Insts.CoreCmpPartialEqOption.eq]
          rw [addressClass_eq_eq]
          have : c ≠ AddressClass.Private := fun e => hnp (by rw [e])
          simp only [this, decide_false, bind_ok, Bool.false_eq_true, ↓reduceIte]
    unfold is_allowed_disallowed_host
    cases h with
    | Domain t => dsimp only; rw [bind_ok]; exact rest none rfl
    | Ipv4 a => simp only [Proofs.Transport.MetadataResolver.of_eq, bind_ok]; exact rest _ rfl
    | Ipv6 a => simp only [Proofs.Transport.MetadataResolver.of_eq, bind_ok]; exact rest _ rfl

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::is_allowed_disallowed_host`**
(patch helper of A06; upstream lines 1425–1435)

If the base URL's domain, if any, is UTF-8 and the host's domain, if any, is UTF-8 (rules
(ii)(b) and (ii)(a)), never fails: `true` exactly when `allow_private` holds and the host is an
IP literal of class `Private` (N01: `10/8`, `172.16/12`, `192.168/16`, `100.64/10`, `fc00::/7`,
or an IPv6 embedding of one), or when the base URL's host and the host are both loopback hosts
(`isLoopbackHost`: a `localhost` name, `127/8`, or `::1`)
(`Defs.AuthMetadata.isAllowedDisallowedHost`). Sufficient premises; each is needed only when the
code reads that host (`is_allowed_metadata_url_fail_base`). H10 (recorded bug): with
`allow_private`, the cloud-metadata endpoints `100.100.100.200` and `fd00:ec2::254` (class
`Private`) are allowed. -/
@[step]
theorem is_allowed_disallowed_host_spec (base_url : url.Url) (host : url.host.Host Str)
    (allow_private : Bool) (h_base : HostUtf8 base_url)
    (h_utf8 : ∀ d, host = url.host.Host.Domain d → ExtModel.IsUtf8 d.val) :
    is_allowed_disallowed_host base_url host allow_private ⦃ (result : Bool) =>
      result = isAllowedDisallowedHost (ExtModel.urlHost base_url) host allow_private ⦄ := by
  rw [is_allowed_disallowed_host_eq base_url host allow_private h_base h_utf8, WP.spec_ok]

/-! ## A07 `resolve_resource_metadata_url` (upstream lines 1439–1473; patched 1451–1486) -/

/-- **Spec theorem for
`rmcp::transport::auth::AuthorizationManager::resolve_resource_metadata_url`** (A07)

If the base URL's scheme is `http` or `https` (human decision AD8: Rust's `Url::join` can panic
for some `file:` bases, which the model does not capture), the base URL's domain is UTF-8 and the
candidate URL's domain is UTF-8 (rule (ii)(b)), never fails. The result, in the Rust order of
checks (`Defs.AuthMetadata.resolveResourceMetadataUrl`): the value is trimmed of Unicode
`White_Space` at both ends (line 1444; `trimWhitespace_utf8Bytes`); `none` if nothing remains
(lines 1445–1448); otherwise the value parsed as an absolute URL, or else resolved against the
base URL, `none` if both fail (lines 1450–1456, `metadataCandidate`); that candidate if it is
HTTP(S) with a host and same-origin with the base URL (lines 1458–1460); `none` if the base URL
is `https` and the candidate's scheme is not (lines 1461–1464); the candidate if A06 allows it
(lines 1465–1466); otherwise `none`. The AD8 premise is documented, not used by the model, and
only this statement and the others that promise no failure take it (the "on success"
statements do not); the UTF-8 premises are true of every `url::Url`, and each is needed when
the code reads that host (`resolve_resource_metadata_url_fail`,
`resolve_resource_metadata_url_fail_base`). -/
@[step]
theorem resolve_resource_metadata_url_spec (value : Str) (base_url : url.Url)
    (allow_private : Bool) (h_scheme : isHttpScheme (ExtModel.urlScheme base_url).val = true)
    (h_base : HostUtf8 base_url)
    (h_candidate : ∀ u, metadataCandidate value.val base_url = some u → HostUtf8 u) :
    resolve_resource_metadata_url value base_url allow_private
      ⦃ (result : Option url.Url) =>
      result = resolveResourceMetadataUrl value.val base_url allow_private ⦄ := by
  have _ := h_scheme
  rw [resolve_resource_metadata_url_eq]
  unfold resolveResourceMetadataUrl
  cases hc : metadataCandidate value.val base_url with
  | none => simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Option.bind_none, WP.spec_ok]
  | some u =>
    simp only [Option.bind_some, resolveTail]
    split
    · simp only [WP.spec_ok]
    · split
      · simp only [WP.spec_ok]
      · obtain ⟨b, hb, hbv⟩ := exists_ok_of_spec (is_allowed_metadata_url_spec base_url u
          allow_private h_base (fun _ => h_candidate u hc))
        rw [hb, bind_ok, hbv]
        split <;> simp_all only [Option.some.injEq, forall_eq', Bool.and_eq_true, not_and,
          Bool.not_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not, Decidable.not_not, WP.spec_ok]

/-- **`resolve_resource_metadata_url`, when the candidate premise is needed**: for a candidate
that is HTTP(S) with a host string, not same-origin with the base URL, not a downgrade from
`https`, and whose host is a domain that is not UTF-8, A06 (upstream line 1465) fails, so the
call fails with `undef`. -/
theorem resolve_resource_metadata_url_fail (value : Str) (base_url : url.Url)
    (allow_private : Bool) (u : url.Url) (d : Str)
    (h_candidate : metadataCandidate value.val base_url = some u)
    (h_http : isHttpUrl u = true) (h_origin : isSameOrigin base_url u = false)
    (h_downgrade : ¬ ((ExtModel.urlScheme base_url).val = utf8Bytes "https" ∧
      (ExtModel.urlScheme u).val ≠ utf8Bytes "https"))
    (h_host : ExtModel.urlHost u = some (url.host.Host.Domain d))
    (h : ¬ ExtModel.IsUtf8 d.val) :
    resolve_resource_metadata_url value base_url allow_private = fail .undef := by
  rw [resolve_resource_metadata_url_eq, h_candidate]
  simp only [resolveTail, h_http, h_origin, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  have hdg : (decide ((ExtModel.urlScheme base_url).val = utf8Bytes "https") &&
      !decide ((ExtModel.urlScheme u).val = utf8Bytes "https")) = false := by
    by_cases a : (ExtModel.urlScheme base_url).val = utf8Bytes "https" <;>
      by_cases b : (ExtModel.urlScheme u).val = utf8Bytes "https" <;> simp_all only [ne_eq,
        not_true_eq_false, and_false, not_false_eq_true, decide_true, Bool.not_true, Bool.and_false,
        and_self, decide_false, Bool.and_self, and_true, Bool.not_false, Bool.and_true]
  rw [hdg]; simp only [Bool.false_eq_true, ↓reduceIte]
  rw [is_allowed_metadata_url_fail base_url u allow_private d h_http h_host h, bind_fail]

/-- **`resolve_resource_metadata_url`, when the base premise is needed**: for a candidate that is
HTTP(S) with a host string, not same-origin with the base URL and not a downgrade from `https`,
whose host the guard rejects and that is not exempted as a `Private` literal with
`allow_private`, A06 (upstream line 1465) reads the base URL's host (upstream line 1434); if it
is a domain that is not UTF-8, the call fails with `undef` (`is_allowed_metadata_url_fail_base`).
The same-origin check (upstream line 1458) reads only the host strings and does not fail. -/
theorem resolve_resource_metadata_url_fail_base (value : Str) (base_url : url.Url)
    (allow_private : Bool) (u : url.Url) (h : url.host.Host Str) (d : Str)
    (h_candidate : metadataCandidate value.val base_url = some u)
    (h_http : isHttpUrl u = true) (h_origin : isSameOrigin base_url u = false)
    (h_downgrade : ¬ ((ExtModel.urlScheme base_url).val = utf8Bytes "https" ∧
      (ExtModel.urlScheme u).val ≠ utf8Bytes "https"))
    (h_host : ExtModel.urlHost u = some h) (h_dis : isDisallowedHost h = true)
    (h_priv : ¬ (allow_private = true ∧ (hostIp h).map addressClass = some AddressClass.Private))
    (h_base_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (hd : ¬ ExtModel.IsUtf8 d.val) :
    resolve_resource_metadata_url value base_url allow_private = fail .undef := by
  rw [resolve_resource_metadata_url_eq, h_candidate]
  simp only [resolveTail, h_http, h_origin, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  have hdg : (decide ((ExtModel.urlScheme base_url).val = utf8Bytes "https") &&
      !decide ((ExtModel.urlScheme u).val = utf8Bytes "https")) = false := by
    by_cases a : (ExtModel.urlScheme base_url).val = utf8Bytes "https" <;>
      by_cases b : (ExtModel.urlScheme u).val = utf8Bytes "https" <;> simp_all only [ne_eq,
        not_true_eq_false, and_false, not_false_eq_true, Option.map_eq_some_iff, not_and,
        not_exists, decide_true, Bool.not_true, Bool.and_false, and_self, decide_false,
        Bool.and_self, and_true, Bool.not_false, Bool.and_true]
  rw [hdg]; simp only [Bool.false_eq_true, ↓reduceIte]
  rw [is_allowed_metadata_url_fail_base base_url u allow_private h d h_http h_host h_dis h_priv
    h_base_host hd, bind_fail]

/-! ## A08 `check_authorization_response_issuer` (patched lines 2342–2375; the body of
`validate_authorization_response_issuer`, upstream lines 2320–2353) -/

/-- **Spec theorem for
`rmcp::transport::auth::AuthorizationManager::check_authorization_response_issuer`** (A08)

If the recorded expected issuer, if any, fits in a slice (every Rust `String`) and, when an
issuer is recorded, the received issuer is UTF-8 (rule (ii)(a), the `&str` carried by
`Option<&str>`), never fails. The result (`Defs.AuthMetadata.responseIssuerCheck`), in the Rust
order of checks: without a recorded issuer, `Err (AuthorizationFailed m)` with the fixed message
`m` if an issuer was received or `require_issuer` is set (upstream lines 2324–2330), otherwise
`Ok` (line 2334); with a recorded issuer `e` and none received,
`Err (AuthorizationServerMissingIssuer e)` if `require_issuer` (lines 2336–2341), otherwise `Ok`
(line 2344); with both, `Ok` exactly when the received bytes are those of `e` (RFC 9207 §2.4,
simple string comparison), otherwise `Err (AuthorizationServerMismatch e r)` with the received
string `r` (lines 2346–2351). Both premises are the weakest
(`check_authorization_response_issuer_fail`, `…_fail_undef`). -/
@[step]
theorem check_authorization_response_issuer_spec (stored_state : StoredAuthorizationState)
    (received_issuer : Option Str)
    (h_fits : ∀ e, stored_state.expected_issuer = some e → e.utf8ByteSize ≤ Usize.max)
    (h_utf8 : ∀ e r, stored_state.expected_issuer = some e → received_issuer = some r →
      ExtModel.IsUtf8 r.val) :
    check_authorization_response_issuer stored_state received_issuer
      ⦃ (result : core.result.Result Unit IssuerError) =>
      result = responseIssuerCheck stored_state.expected_issuer stored_state.require_issuer
        (received_issuer.map (·.val)) ⦄ := by
  unfold check_authorization_response_issuer
  cases he : stored_state.expected_issuer with
  | none =>
    simp only [core.option.Option.as_deref, bind_ok, responseIssuerCheck]
    cases received_issuer <;> cases stored_state.require_issuer <;>
      simp only [core.option.Option.is_some, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        Option.map_none, Bool.or_self, WP.spec_ok, to_owned_issuerNotRecordedMessage, bind_ok,
        Bool.or_true, Option.isSome_some, Option.map_some, Bool.or_false]
  | some e =>
    have hf := h_fits e he
    simp only [core.option.Option.as_deref]
    rw [deref_eq e hf, bind_ok_str, bind_ok]
    have hto : Str.Insts.AllocBorrowToOwnedString.to_owned
        (Slice.from (utf8 e) (by rw [length_utf8]; exact hf)) = ok e :=
      to_owned_eq_ok_of_val_eq_utf8 _ _ (Slice.from_val _ _)
    cases hr : received_issuer with
    | none =>
      simp only [responseIssuerCheck, Option.map_none]
      cases stored_state.require_issuer <;> simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok,
        hto, bind_ok]
    | some r =>
      simp only [Str.Insts.CoreCmpPartialEqStr.eq, Slice.from_val, responseIssuerCheck,
        Option.map_some, utf8Bytes_eq_utf8]
      by_cases hre : r.val = utf8 e
      · simp only [hre, decide_true, bind_ok, ↓reduceIte, WP.spec_ok]
      · obtain ⟨t, ht⟩ := h_utf8 e r he hr
        have hs : stringOfUtf8 r.val = t := by simp only [stringOfUtf8, ht, strOfBytes?_utf8,
          Option.getD_some]
        simp only [hre, decide_false, hto, to_owned_eq_ok_of_val_eq_utf8 r t ht, bind_ok,
          Bool.false_eq_true, ↓reduceIte, hs, WP.spec_ok]

/-- **`check_authorization_response_issuer`, the size premise is exact for the Lean models**: a
recorded issuer of more than `Usize.max` bytes (no Rust `String`) fails `as_deref` (upstream line
2324) with `maximumSizeExceeded`. -/
theorem check_authorization_response_issuer_fail (stored_state : StoredAuthorizationState)
    (received_issuer : Option Str) (e : String)
    (h_expected : stored_state.expected_issuer = some e) (h : ¬ e.utf8ByteSize ≤ Usize.max) :
    check_authorization_response_issuer stored_state received_issuer =
      fail .maximumSizeExceeded := by
  unfold check_authorization_response_issuer
  rw [h_expected]
  simp only [core.option.Option.as_deref]
  rw [deref_eq_fail_of_not_le e h, bind_fail, bind_fail]

/-- **`check_authorization_response_issuer`, the UTF-8 premise is the weakest**: with a recorded
issuer that fits and a received issuer that is not UTF-8 (hence different from it), the
`to_owned` of the received issuer for the mismatch payload (upstream line 2349, patched 2371)
fails with `undef`. -/
theorem check_authorization_response_issuer_fail_undef (stored_state : StoredAuthorizationState)
    (e : String) (r : Str) (h_expected : stored_state.expected_issuer = some e)
    (h_fits : e.utf8ByteSize ≤ Usize.max) (h : ¬ ExtModel.IsUtf8 r.val) :
    check_authorization_response_issuer stored_state (some r) = fail .undef := by
  unfold check_authorization_response_issuer
  rw [h_expected]
  simp only [core.option.Option.as_deref]
  rw [deref_eq e h_fits, bind_ok_str, bind_ok]
  have hne : r.val ≠ utf8 e := fun he => h ⟨e, he⟩
  simp only [Str.Insts.CoreCmpPartialEqStr.eq, Slice.from_val, hne, decide_false, bind_ok,
    Bool.false_eq_true, ↓reduceIte]
  rw [to_owned_eq_ok_of_val_eq_utf8 _ e (Slice.from_val _ _), bind_ok,
    to_owned_eq_fail_of_not_isUtf8 r h, bind_fail]

/-! ## A09 `check_authorization_metadata_issuer` (patched lines 2829–2855; the body of
`validate_authorization_metadata_issuer`, upstream lines 2796–2821) and its callees, in source
order -/

/-- **Spec theorem for
`rmcp::transport::auth::AuthorizationManager::expected_issuer_for_authorization_metadata_url`**
(callee of A09; upstream lines 2745–2774, patched 2767–2788)

For a discovery URL of at most `u32::MAX` bytes (human decision AD7: the `url` setters behind
`prim::issuer_url` panic above it, which the model does not capture; documented premise,
stronger than the exact panic condition, see `DiscoveryUrlFits`), never fails: the issuer path
of the discovery URL's path (`issuerPath`: empty for the bare RFC 8414 or OpenID Connect
well-known path; the rest after `/.well-known/oauth-authorization-server/` or
`/.well-known/openid-configuration/`; the part before a final `/.well-known/openid-configuration`
without its leading `/`s; otherwise none), mapped to the opaque rewritten URL
`ExtModel.issuerUrl` (`Defs.AuthMetadata.derivedIssuer`). H9: a recorded issue in this check,
under private disclosure; details withheld until it is reported. -/
@[step]
theorem expected_issuer_for_authorization_metadata_url_spec (discovery_url : url.Url)
    (h_fits : DiscoveryUrlFits discovery_url) :
    expected_issuer_for_authorization_metadata_url discovery_url
      ⦃ (result : Option String) =>
      result = derivedIssuer discovery_url ⦄ := by
  have _ := h_fits
  rw [expected_issuer_for_authorization_metadata_url_eq, WP.spec_ok]

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::issuer_identifiers_match`**
(callee of A09; upstream lines 2776–2794, patched 2790–2796)

If the two issuers are byte-equal or both UTF-8 (rule (ii)(a)), never fails: `true` exactly
when they are byte-equal or equal after removing from each a final `/` after which what remains
parses as a URL whose path is empty or `/` (query and fragment allowed)
(`Defs.AuthMetadata.issuersMatch`; `eq_or_eq_append_slash_of_issuersMatch` says what this
allows). H15 (recorded bug): the root-`/` tolerance deviates from the "identical" of RFC 8414
§3.3 (asserted by the upstream test
`authorization_metadata_allows_only_root_trailing_slash_equivalence`, lines 5141–5151), and the
`/` removed may end a query or a fragment (`https://as.example?x/` matches
`https://as.example?x`). The premise is exact (`issuer_identifiers_match_fail`). -/
@[step]
theorem issuer_identifiers_match_spec (received_issuer expected_issuer : Str)
    (h_utf8 : received_issuer.val ≠ expected_issuer.val →
      ExtModel.IsUtf8 received_issuer.val ∧ ExtModel.IsUtf8 expected_issuer.val) :
    issuer_identifiers_match received_issuer expected_issuer ⦃ (result : Bool) =>
      result = issuersMatch received_issuer.val expected_issuer.val ⦄ := by
  rw [issuer_identifiers_match_eq received_issuer expected_issuer h_utf8, WP.spec_ok]

/-- **`issuer_identifiers_match`, the UTF-8 premise (U') is exact**: if the two issuers are not
byte-equal (the check of patched line 2791, upstream line 2777, does not return) and one of them
is not UTF-8, the comparison of patched line 2795 (upstream line 2793) calls `trim_root_slash` on
the received issuer, then on the expected one, and the first that is not UTF-8 fails with
`undef` in its `to_owned` (patched lines 2802 and 2804; `trim_root_slash_fail`). -/
theorem issuer_identifiers_match_fail (received_issuer expected_issuer : Str)
    (h_ne : received_issuer.val ≠ expected_issuer.val)
    (h : ¬ (ExtModel.IsUtf8 received_issuer.val ∧ ExtModel.IsUtf8 expected_issuer.val)) :
    issuer_identifiers_match received_issuer expected_issuer = fail .undef := by
  unfold issuer_identifiers_match
  simp only [Str.Insts.CoreCmpPartialEqStr.eq, h_ne, decide_false, bind_ok, Bool.false_eq_true,
    ↓reduceIte]
  by_cases hr : ExtModel.IsUtf8 received_issuer.val
  · have he : ¬ ExtModel.IsUtf8 expected_issuer.val := fun he => h ⟨hr, he⟩
    obtain ⟨r, hr', -⟩ := exists_trim_root_slash_eq_ok _ hr
    rw [hr', bind_ok, Proofs.Transport.AuthMetadata.trim_root_slash_fail _ he, bind_fail]
  · rw [Proofs.Transport.AuthMetadata.trim_root_slash_fail _ hr, bind_fail]

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::trim_root_slash`** (patch
helper of A09; patched lines 2798–2805, the closure of upstream lines 2781–2791)

For a UTF-8 issuer (rule (ii)(a)), never fails: the issuer without its final `/` if what remains
parses as a URL whose path is empty or `/` (query and fragment allowed), otherwise unchanged
(`Defs.AuthMetadata.trimRootSlash`), as bytes. The premise is the weakest
(`trim_root_slash_fail`). -/
@[step]
theorem trim_root_slash_spec (issuer : Str) (h_utf8 : ExtModel.IsUtf8 issuer.val) :
    trim_root_slash issuer ⦃ (result : String) =>
      utf8Bytes result = trimRootSlash issuer.val ⦄ := by
  obtain ⟨r, hr, hv⟩ := exists_trim_root_slash_eq_ok issuer h_utf8
  rw [hr, WP.spec_ok]; exact hv

/-- **`trim_root_slash`, the UTF-8 premise is the weakest**: for bytes that are not UTF-8,
`to_owned` (patched lines 2802 and 2804) fails with `undef` on both branches (removing a final
`/` does not make bytes UTF-8). -/
theorem trim_root_slash_fail (issuer : Str) (h : ¬ ExtModel.IsUtf8 issuer.val) :
    trim_root_slash issuer = fail .undef :=
  Proofs.Transport.AuthMetadata.trim_root_slash_fail issuer h

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::is_root_url`** (patch
helper of A09; patched lines 2807–2812, the `filter` closure of upstream lines 2784–2788)

Never fails. `true` exactly when the bytes parse as a URL whose path is empty or `/` (query and
fragment allowed) (`Defs.AuthMetadata.isRootUrl`). No premise. -/
@[step]
theorem is_root_url_spec (value : Str) :
    is_root_url value ⦃ (result : Bool) =>
      result = isRootUrl value.val ⦄ := by
  rw [is_root_url_eq, WP.spec_ok]

/-- **Spec theorem for
`rmcp::transport::auth::AuthorizationManager::check_authorization_metadata_issuer`** (A09)

If an explicit expected issuer is UTF-8 (rule (ii)(a)), the metadata's `issuer` fits in a slice
(every Rust `String`), and, without an explicit expected issuer, the derived issuer fits in a
slice and the discovery URL has at most `u32::MAX` bytes (human decision AD7, documented
premise), never fails. The result (`Defs.AuthMetadata.metadataIssuerCheck`), in the Rust order
of checks: the expected issuer is the explicit one, or else the one derived from the discovery
URL (`expectedIssuerOf`, patched lines 2835–2838); `Ok` without one (lines 2839–2841, upstream
2805–2807); with an expected issuer `e` and no `issuer` in the
metadata, `Ok` if `allow_missing_issuer`, otherwise `Err (AuthorizationServerMissingIssuer e)`
(lines 2842–2847); with an `issuer` `r`, `Ok` if `issuersMatch r e`, otherwise
`Err (AuthorizationServerMismatch e r)` (lines 2848–2853). H9: a recorded issue in this check,
under private disclosure; details withheld until it is reported. The UTF-8
premise is the weakest (`check_authorization_metadata_issuer_fail`); the size premises are needed
in the cases of `…_fail_size` and `…_fail_derived` (`h_derived` is not needed when
`metadata.issuer` is none). H15 (recorded bug): `issuersMatch`
tolerates the final `/` of a root URL. -/
@[step]
theorem check_authorization_metadata_issuer_spec (allow_missing_issuer : Bool)
    (discovery_url : url.Url) (expected_issuer : Option Str) (metadata : AuthorizationMetadata)
    (h_utf8 : ∀ s, expected_issuer = some s → ExtModel.IsUtf8 s.val)
    (h_received : ∀ r, metadata.issuer = some r → r.utf8ByteSize ≤ Usize.max)
    (h_derived : expected_issuer = none →
      ∀ e, derivedIssuer discovery_url = some e → e.utf8ByteSize ≤ Usize.max)
    (h_discovery : expected_issuer = none → DiscoveryUrlFits discovery_url) :
    check_authorization_metadata_issuer allow_missing_issuer discovery_url expected_issuer
      metadata ⦃ (result : core.result.Result Unit IssuerError) =>
      result = metadataIssuerCheck allow_missing_issuer
        (expectedIssuerOf (expected_issuer.map (·.val)) discovery_url) metadata.issuer ⦄ := by
  have _ := h_discovery
  unfold check_authorization_metadata_issuer
  cases hx : expected_issuer with
  | none =>
    dsimp only
    rw [expected_issuer_for_authorization_metadata_url_eq, bind_ok]
    simp only [Option.map_none, expectedIssuerOf]
    cases hd : derivedIssuer discovery_url with
    | none => simp only [metadataIssuerCheck, WP.spec_ok]
    | some e =>
      dsimp only
      have he := h_derived hx e hd
      cases hi : metadata.issuer with
      | none =>
        simp only [core.option.Option.as_deref, bind_ok, metadataIssuerCheck]
        cases allow_missing_issuer <;> simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      | some r =>
        have hr := h_received r hi
        simp only [core.option.Option.as_deref]
        rw [deref_eq r hr, bind_ok_str, bind_ok]
        dsimp only
        rw [deref_eq e he, bind_ok_str]
        rw [issuer_identifiers_match_eq _ _
          (fun _ => ⟨⟨r, Slice.from_val _ _⟩, ⟨e, Slice.from_val _ _⟩⟩), bind_ok]
        simp only [Slice.from_val, metadataIssuerCheck, utf8Bytes_eq_utf8]
        by_cases hm : issuersMatch (utf8 r) (utf8 e) = true
        · simp only [hm, ↓reduceIte, WP.spec_ok]
        · simp only [hm, Bool.false_eq_true, ↓reduceIte]
          rw [to_owned_eq_ok_of_val_eq_utf8 _ r (Slice.from_val _ _), bind_ok, WP.spec_ok]
  | some s =>
    dsimp only
    obtain ⟨t, ht⟩ := h_utf8 s hx
    rw [to_owned_eq_ok_of_val_eq_utf8 s t ht, bind_ok, bind_ok]
    have hs : stringOfUtf8 s.val = t := by simp only [stringOfUtf8, ht, strOfBytes?_utf8,
      Option.getD_some]
    simp only [Option.map_some, expectedIssuerOf, hs]
    have hf : t.utf8ByteSize ≤ Usize.max := by rw [← length_utf8, ← ht]; exact s.property
    cases hi : metadata.issuer with
    | none =>
      simp only [core.option.Option.as_deref, bind_ok, metadataIssuerCheck]
      cases allow_missing_issuer <;> simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    | some r =>
      have hr := h_received r hi
      simp only [core.option.Option.as_deref]
      rw [deref_eq r hr, bind_ok_str, bind_ok]
      dsimp only
      rw [deref_eq t hf, bind_ok_str]
      rw [issuer_identifiers_match_eq _ _
        (fun _ => ⟨⟨r, Slice.from_val _ _⟩, ⟨t, Slice.from_val _ _⟩⟩), bind_ok]
      simp only [Slice.from_val, metadataIssuerCheck, utf8Bytes_eq_utf8]
      by_cases hm : issuersMatch (utf8 r) (utf8 t) = true
      · simp only [hm, ↓reduceIte, WP.spec_ok]
      · simp only [hm, Bool.false_eq_true, ↓reduceIte]
        rw [to_owned_eq_ok_of_val_eq_utf8 _ r (Slice.from_val _ _), bind_ok, WP.spec_ok]

/-- **`check_authorization_metadata_issuer`, the UTF-8 premise is the weakest**: an explicit
expected issuer that is not UTF-8 fails `to_owned` (patched line 2836, upstream 2803) with
`undef`. -/
theorem check_authorization_metadata_issuer_fail (allow_missing_issuer : Bool)
    (discovery_url : url.Url) (s : Str) (metadata : AuthorizationMetadata)
    (h : ¬ ExtModel.IsUtf8 s.val) :
    check_authorization_metadata_issuer allow_missing_issuer discovery_url (some s) metadata =
      fail .undef := by
  unfold check_authorization_metadata_issuer
  dsimp only
  rw [to_owned_eq_fail_of_not_isUtf8 s h, bind_fail, bind_fail]

/-- **`check_authorization_metadata_issuer`, when the size premise on the received issuer is
needed**: with an expected issuer (here an explicit UTF-8 one), a metadata `issuer` of
more than `Usize.max` bytes (no Rust `String`) fails `as_deref` (patched line 2842, upstream
2808) with `maximumSizeExceeded`. -/
theorem check_authorization_metadata_issuer_fail_size (allow_missing_issuer : Bool)
    (discovery_url : url.Url) (s : Str) (metadata : AuthorizationMetadata) (r : String)
    (h_utf8 : ExtModel.IsUtf8 s.val) (h_issuer : metadata.issuer = some r)
    (h : ¬ r.utf8ByteSize ≤ Usize.max) :
    check_authorization_metadata_issuer allow_missing_issuer discovery_url (some s) metadata =
      fail .maximumSizeExceeded := by
  unfold check_authorization_metadata_issuer
  dsimp only
  obtain ⟨t, ht⟩ := h_utf8
  rw [to_owned_eq_ok_of_val_eq_utf8 s t ht, bind_ok, bind_ok]
  dsimp only
  simp only [h_issuer, core.option.Option.as_deref]
  rw [deref_eq_fail_of_not_le r h, bind_fail, bind_fail]

/-- **`check_authorization_metadata_issuer`, when the size premise on the derived issuer is
needed**: without an explicit expected issuer, a derived issuer of more than `Usize.max`
bytes (no Rust `String`) fails its `deref` (patched line 2848, `&expected_issuer`; upstream
2814) with `maximumSizeExceeded` when the metadata names an `issuer` (if that `issuer` is too
long as well, its `as_deref`, patched line 2842, fails first, with the same error). No premise:
the model of `prim::issuer_url` does not fail, so the AD7 premise plays no role here. -/
theorem check_authorization_metadata_issuer_fail_derived (allow_missing_issuer : Bool)
    (discovery_url : url.Url) (metadata : AuthorizationMetadata) (e r : String)
    (h_derived : derivedIssuer discovery_url = some e) (h : ¬ e.utf8ByteSize ≤ Usize.max)
    (h_issuer : metadata.issuer = some r) :
    check_authorization_metadata_issuer allow_missing_issuer discovery_url none metadata =
      fail .maximumSizeExceeded := by
  unfold check_authorization_metadata_issuer
  dsimp only
  rw [expected_issuer_for_authorization_metadata_url_eq, bind_ok, h_derived]
  dsimp only
  simp only [h_issuer, core.option.Option.as_deref]
  by_cases hr : r.utf8ByteSize ≤ Usize.max
  · rw [deref_eq r hr, bind_ok_str, bind_ok]
    dsimp only
    rw [deref_eq_fail_of_not_le e h, bind_fail]
  · rw [deref_eq_fail_of_not_le r hr, bind_fail, bind_fail]

/-! ## A10 `check_resource_metadata_resource` (patched lines 3001–3037; the body of
`validate_resource_metadata_resource`, upstream lines 2960–2996) and its callee (patched lines
3040–3063) -/

/-- **Spec theorem for
`rmcp::transport::auth::AuthorizationManager::check_resource_metadata_resource`** (A10)

If the metadata's `resource`, if any, fits in a slice (every Rust `String`), never fails. The
result (`Defs.AuthMetadata.resourceCheck`), in the Rust order of checks:
`Err MissingResource` without a resource (upstream lines 2964–2967); `Err (ResourceNotAUrl r)`
with the resource string if it does not parse (lines 2970–2975); `Err (ResourceHasFragment u)`
with the parsed URL if it has a fragment (lines 2978–2983, RFC 8707 §2); `Err (ResourceMismatch
base_url u)` if `u` is not a valid identifier of the base URL (lines 2986–2992); otherwise `Ok`.
The premise is exact for the Lean models (`check_resource_metadata_resource_fail`). -/
@[step]
theorem check_resource_metadata_resource_spec (base_url : url.Url)
    (metadata : ResourceServerMetadata)
    (h_fits : ∀ r, metadata.resource = some r → r.utf8ByteSize ≤ Usize.max) :
    check_resource_metadata_resource base_url metadata
      ⦃ (result : core.result.Result Unit ProtectedResourceMetadataInvalidReason) =>
      result = resourceCheck base_url metadata.resource ⦄ := by
  rw [check_resource_metadata_resource_eq base_url metadata h_fits, WP.spec_ok]

/-- **`check_resource_metadata_resource`, the size premise is exact for the Lean models**: a
resource of more than `Usize.max` bytes (no Rust `String`) fails `as_deref` (upstream line 2964)
with `maximumSizeExceeded`. -/
theorem check_resource_metadata_resource_fail (base_url : url.Url)
    (metadata : ResourceServerMetadata) (r : String) (h_resource : metadata.resource = some r)
    (h : ¬ r.utf8ByteSize ≤ Usize.max) :
    check_resource_metadata_resource base_url metadata = fail .maximumSizeExceeded := by
  unfold check_resource_metadata_resource
  simp only [h_resource, core.option.Option.as_deref]
  rw [deref_eq_fail_of_not_le r h, bind_fail, bind_fail]

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::is_resource_identifier_valid`**
(callee of A10; upstream lines 2998–3021, patched 3040–3063)

Never fails. `true` exactly when the serializations are equal (line 2999), or the schemes, host
strings and ports or known default ports are equal (lines 3003–3008) and the actual path covers
the expected path: equal, or a byte prefix of it that ends in `/` or is followed by `/` in it
(lines 3010–3021) (`Defs.AuthMetadata.isResourceIdentifierValid`). Query, fragment and user
information are not compared. No premise. H13 (recorded bug): this accepts an ancestor path, a
different query and different user information (`pathCovers_append_slash_append`). It rejects
the expected path with a final `/` added (`pathCovers_append_slash_eq_false`), as RFC 9728 §3.3
requires; that is not part of H13, but is inconsistent with the ancestor rule. -/
@[step]
theorem is_resource_identifier_valid_spec (expected actual : url.Url) :
    is_resource_identifier_valid expected actual ⦃ (result : Bool) =>
      result = isResourceIdentifierValid expected actual ⦄ := by
  rw [is_resource_identifier_valid_eq, WP.spec_ok]

end rmcp.transport.auth.AuthorizationManager

/-! ## Laws of `Defs.AuthMetadata` -/

namespace Defs.AuthMetadata

/-- **`is_same_origin`, the readable default-port table is the trusted one**: `knownDefaultPort`
(`url-2.5.9/src/parser.rs` lines 185–192) is the function `ExtModel.defaultPort` on which the
model of `Url::port_or_known_default` is built, so `portOrKnownDefault u` is the value that model
returns. -/
theorem knownDefaultPort_eq_defaultPort : knownDefaultPort = ExtModel.defaultPort :=
  Proofs.Transport.AuthMetadata.knownDefaultPort_eq_defaultPort

/-- **`is_same_origin`, same origin implies the same scheme** (upstream line 1335), so the
same-origin acceptance of A07 never downgrades from `https`. -/
theorem urlScheme_eq_of_isSameOrigin (base candidate : url.Url)
    (h : isSameOrigin base candidate = true) :
    (ExtModel.urlScheme base).val = (ExtModel.urlScheme candidate).val := by
  simp only [isSameOrigin, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- **A05, a domain is rejected exactly when its normalized name is** (the call of upstream lines
1393–1395: `is_disallowed_metadata_hostname` on the normalized name). -/
theorem isDisallowedHost_domain (d : Str) :
    isDisallowedHost (url.host.Host.Domain d) = isDisallowedHostname (normalizeHost d.val) := by
  simp only [isDisallowedHost, isLocalhostName, isCloudMetadataName, isDisallowedHostname,
    Bool.or_assoc]

/-- **A05 and N01, an IP literal is rejected exactly when its class is not `Public`**: the guard
(A02/A03) and the address classes of the metadata resolver agree on every IPv4 and IPv6 literal
(the loopback and private ranges lie inside the blocked lists). Which addresses are `Public` (H8
among them, and the IPv6 ranges of H11 that carry no A01 embedding, the IPv4-translated
`::ffff:0:0:0/96` and `100::/64`, and `192.0.0.192`): module docstrings of
`Proofs.Defs.MetadataResolver` and `Proofs.Defs.AuthMetadata`. -/
theorem isDisallowedHost_iff_addressClass_ne_public (h : url.host.Host Str)
    (ip : core.net.ip_addr.IpAddr) (hip : hostIp h = some ip) :
    isDisallowedHost h = true ↔ addressClass ip ≠ AddressClass.Public := by
  cases h with
  | Domain d => simp only [hostIp, reduceCtorEq] at hip
  | Ipv4 a =>
    simp only [hostIp, Option.some.injEq] at hip; subst hip
    exact (ipv4Class_ne_public_iff _).symm
  | Ipv6 a =>
    simp only [hostIp, Option.some.injEq] at hip; subst hip
    exact (ipv6Class_ne_public_iff _).symm

/-- **A05, a cloud-metadata name is not a `localhost` name** (so the loopback exemption of A06
never applies to it). -/
theorem isLocalhostName_eq_false_of_isCloudMetadataName (d : List U8)
    (h : isCloudMetadataName d = true) : isLocalhostName d = false := by
  unfold isCloudMetadataName at h
  unfold isLocalhostName
  generalize normalizeHost d = n at h ⊢
  simp only [cloudMetadataHosts, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> decide +kernel

/-- **A06, a loopback IP literal has class `Loopback`**: `127/8` and `::1` (`isLoopbackHost`) are
`Loopback` for N01; the converse fails for the IPv6 embeddings of `127/8` (such as
`::ffff:127.0.0.1`), which N01 calls `Loopback` but `Ipv6Addr::is_loopback` does not (H12). -/
theorem addressClass_eq_loopback_of_isLoopbackHost (h : url.host.Host Str)
    (ip : core.net.ip_addr.IpAddr) (hip : hostIp h = some ip) (hl : isLoopbackHost h = true) :
    addressClass ip = AddressClass.Loopback := by
  cases h with
  | Domain d => simp only [hostIp, reduceCtorEq] at hip
  | Ipv4 a =>
    simp only [hostIp, Option.some.injEq] at hip; subst hip
    simp only [isLoopbackHost] at hl
    simp only [addressClass, ipv4Class, hl, ↓reduceIte]
  | Ipv6 a =>
    simp only [hostIp, Option.some.injEq] at hip; subst hip
    simp only [isLoopbackHost] at hl
    simp only [addressClass, ipv6Class]
    have hv : ipv6Value a.addrSegments.val = 1 := by
      have := hl
      simp only [inPrefix, ipv6Loopback, ipv6Prefix] at this
      have e : ofBigEndianDigits 65536 [0, 0, 0, 0, 0, 0, 0, 1] = 1 := by decide
      simpa only [tsub_self, pow_zero, Nat.div_one, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd, List.replicate_zero, List.append_nil, e, Order.lt_one_iff, Nat.div_self,
        beq_iff_eq] using this
    rw [hv]
    have : embeddedIpv4 1 = none := by decide
    rw [this]; simp only
    have : inPrefix ipv6Loopback 1 = true := by decide
    simp only [this, ↓reduceIte]

/-- **A06, an allowed metadata URL is HTTP(S) with a host string** (A04, upstream line 1413). -/
theorem isHttpUrl_of_isAllowedMetadataUrl (base target : url.Url) (allowPrivate : Bool)
    (h : isAllowedMetadataUrl base target allowPrivate = true) : isHttpUrl target = true := by
  unfold isAllowedMetadataUrl at h
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- **A06, a cloud-metadata name is never allowed**: a target whose host is a domain that
normalizes to `metadata`, `metadata.google.internal` or `metadata.azure.internal` is refused,
whatever the base URL and `allowPrivate` (the guard rejects it, upstream lines 1388 and 1421; a
domain has no `Private` class; it is no `localhost` name). No premise. -/
theorem isAllowedMetadataUrl_eq_false_of_isCloudMetadataName (base target : url.Url)
    (allowPrivate : Bool) (d : Str)
    (h_host : ExtModel.urlHost target = some (url.host.Host.Domain d))
    (hc : isCloudMetadataName d.val = true) :
    isAllowedMetadataUrl base target allowPrivate = false := by
  simp only [isAllowedMetadataUrl, h_host, isDisallowedHost,
    isLocalhostName_eq_false_of_isCloudMetadataName _ hc, hc, Bool.or_true, Bool.not_true,
    isAllowedDisallowedHost, hostIp, Option.map_none, reduceCtorEq, decide_false, Bool.and_false,
    isLoopbackHost, Bool.or_self]

/-- **A06, a `Blocked` literal is never allowed**: a target whose host is an IP literal of class
`Blocked` (link-local such as `169.254.169.254`, unspecified, broadcast, multicast, `0/8`,
`198.18/15`, Teredo, `64:ff9b:1::/48`, or an IPv6 embedding of one) is refused, whatever the
base URL and `allowPrivate`: the guard rejects it, it is not `Private` (upstream lines
1425–1432) and it is not a loopback host (line 1434). This includes the base URL's own literal,
which the resolver allows (H14, `allowsHost_literalIp_self`). No premise. -/
theorem isAllowedMetadataUrl_eq_false_of_addressClass_eq_blocked (base target : url.Url)
    (allowPrivate : Bool) (h : url.host.Host Str) (h_host : ExtModel.urlHost target = some h)
    (h_blocked : (hostIp h).map addressClass = some AddressClass.Blocked) :
    isAllowedMetadataUrl base target allowPrivate = false := by
  obtain ⟨ip, hip, hc⟩ := Option.map_eq_some_iff.mp h_blocked
  have hd : isDisallowedHost h = true :=
    (isDisallowedHost_iff_addressClass_ne_public h ip hip).mpr (by rw [hc]; decide)
  have hnl : isLoopbackHost h = false := by
    cases hl : isLoopbackHost h
    · rfl
    · have := addressClass_eq_loopback_of_isLoopbackHost h ip hip hl
      rw [hc] at this; cases this
  simp only [isAllowedMetadataUrl, h_host, hd, Bool.not_true, isAllowedDisallowedHost, h_blocked,
    Option.some.injEq, reduceCtorEq, decide_false, Bool.and_false, hnl, Bool.or_self]

/-- **A06, a `Private` literal**: a target whose host is an IP literal of class `Private`
(`10/8`, `172.16/12`, `192.168/16`, `100.64/10`, `fc00::/7`, or an IPv6 embedding of one) is
allowed exactly when it is HTTP(S) with a host string and `allowPrivate` holds (upstream lines
1425–1432); a private base URL does not allow it by itself (unlike the resolver's
`baseClasses`, N04; H12). H10 (recorded bug): this includes the cloud-metadata endpoints
`100.100.100.200` and `fd00:ec2::254`. No premise. -/
theorem isAllowedMetadataUrl_eq_of_addressClass_eq_private (base target : url.Url)
    (allowPrivate : Bool) (h : url.host.Host Str) (h_host : ExtModel.urlHost target = some h)
    (h_private : (hostIp h).map addressClass = some AddressClass.Private) :
    isAllowedMetadataUrl base target allowPrivate = (isHttpUrl target && allowPrivate) := by
  obtain ⟨ip, hip, hc⟩ := Option.map_eq_some_iff.mp h_private
  have hd : isDisallowedHost h = true :=
    (isDisallowedHost_iff_addressClass_ne_public h ip hip).mpr (by rw [hc]; decide)
  have hnl : isLoopbackHost h = false := by
    cases hl : isLoopbackHost h
    · rfl
    · have := addressClass_eq_loopback_of_isLoopbackHost h ip hip hl
      rw [hc] at this; cases this
  simp only [isAllowedMetadataUrl, h_host, hd, Bool.not_true, isAllowedDisallowedHost, h_private,
    decide_true, Bool.and_true, hnl, Bool.and_false, Bool.or_false, Bool.false_or]

/-- **A06, a `Loopback` literal**: a target whose host is an IP literal of class `Loopback` is
allowed exactly when it is HTTP(S) with a host string, the base URL's host is a loopback host and
the target's host is one (`127/8` or `::1`; an IPv6 embedding of `127/8`, class `Loopback`, is
therefore never allowed, H12) (upstream lines 1434–1435); `allowPrivate` plays no role. No
premise. -/
theorem isAllowedMetadataUrl_eq_of_addressClass_eq_loopback (base target : url.Url)
    (allowPrivate : Bool) (h : url.host.Host Str) (h_host : ExtModel.urlHost target = some h)
    (h_loopback : (hostIp h).map addressClass = some AddressClass.Loopback) :
    isAllowedMetadataUrl base target allowPrivate =
      (isHttpUrl target && (ExtModel.urlHost base).any isLoopbackHost && isLoopbackHost h) := by
  obtain ⟨ip, hip, hc⟩ := Option.map_eq_some_iff.mp h_loopback
  have hd : isDisallowedHost h = true :=
    (isDisallowedHost_iff_addressClass_ne_public h ip hip).mpr (by rw [hc]; decide)
  simp only [isAllowedMetadataUrl, h_host, hd, Bool.not_true, isAllowedDisallowedHost, h_loopback,
    Option.some.injEq, reduceCtorEq, decide_false, Bool.and_false, Bool.false_or, Bool.and_assoc]

/-- **A06, a `localhost` name**: a target whose host is `localhost` or a `.localhost` name (after
normalization) is allowed exactly when it is HTTP(S) with a host string and the base URL's host
is a loopback host (upstream lines 1434–1435). No premise. -/
theorem isAllowedMetadataUrl_eq_of_isLocalhostName (base target : url.Url) (allowPrivate : Bool)
    (d : Str) (h_host : ExtModel.urlHost target = some (url.host.Host.Domain d))
    (h_local : isLocalhostName d.val = true) :
    isAllowedMetadataUrl base target allowPrivate =
      (isHttpUrl target && (ExtModel.urlHost base).any isLoopbackHost) := by
  simp only [isAllowedMetadataUrl, h_host, isDisallowedHost, h_local, Bool.true_or, Bool.not_true,
    isAllowedDisallowedHost, hostIp, Option.map_none, reduceCtorEq, decide_false, Bool.and_false,
    isLoopbackHost, Bool.and_true, Bool.false_or]

/-- **A06, every other host**: a target whose host the guard does not reject (a `Public` literal,
by `isDisallowedHost_iff_addressClass_ne_public`, H11 among them, or a domain that is neither a
`localhost` nor a cloud-metadata name) is allowed exactly when it is HTTP(S) with a host string
(upstream lines 1421–1423). No premise. With the SDK's default HTTP client and no proxy, a domain
is resolved later, under the resolver's address policy (N09); with a custom HTTP client or
through a proxy, nothing filters its addresses (H16: `instance-data` or `metadata.goog` is such
a domain). -/
theorem isAllowedMetadataUrl_eq_of_isDisallowedHost_eq_false (base target : url.Url)
    (allowPrivate : Bool) (h : url.host.Host Str) (h_host : ExtModel.urlHost target = some h)
    (h_ok : isDisallowedHost h = false) :
    isAllowedMetadataUrl base target allowPrivate = isHttpUrl target := by
  simp only [isAllowedMetadataUrl, h_host, h_ok, Bool.not_false, Bool.true_or, Bool.and_true]

private theorem loopback_mem_baseClasses (bh : url.host.Host Str) (h : isLoopbackHost bh = true) :
    AddressClass.Loopback ∈ baseClasses (some bh) := by
  cases bh with
  | Domain d => simp only [isLoopbackHost] at h; simp only [baseClasses, h, ↓reduceIte,
    List.mem_cons, List.not_mem_nil, or_false]
  | Ipv4 a =>
    have := addressClass_eq_loopback_of_isLoopbackHost (.Ipv4 a) (.V4 a) rfl h
    simp only [baseClasses, this, List.mem_cons, List.not_mem_nil, or_false]
  | Ipv6 a =>
    have := addressClass_eq_loopback_of_isLoopbackHost (.Ipv6 a) (.V6 a) rfl h
    simp only [baseClasses, this, List.mem_cons, List.not_mem_nil, or_false]

/-- **A06 is never looser than the resolver's host-level check** (H12): if A06 allows a target,
the resolver built for the same base URL (N04 `baseClasses`, with `Private` added by N06 when
`allowPrivate` holds, `withPrivate`) allows its host (N07 `allowsHost`). This is the whole
resolver policy for an IP-literal target, which reqwest connects to without resolving; for those
A06 refuses whenever the resolver would refuse. For a domain target the conclusion says nothing
(`allowsHost` lets every domain through): the resolver decides when the name is resolved (N09),
and with a custom HTTP client or through a proxy nothing does (H16). The converse fails: the H12
and H14 cases listed in the module docstring of `Proofs.Defs.AuthMetadata` (kernel-checked at
its end), and the domain targets A06 refuses (a cloud-metadata name, or a `localhost` name from
a base that is not a loopback host), which `allowsHost` lets through at host level. No
premise. -/
theorem allowsHost_of_isAllowedMetadataUrl (base target : url.Url) (allowPrivate : Bool)
    (h : isAllowedMetadataUrl base target allowPrivate = true) :
    allowsHost (literalIp (ExtModel.urlHost base))
      (if allowPrivate then withPrivate (baseClasses (ExtModel.urlHost base))
        else baseClasses (ExtModel.urlHost base))
      (ExtModel.urlHost target) = true := by
  unfold isAllowedMetadataUrl at h
  cases ht : ExtModel.urlHost target with
  | none => simp only [ht, Bool.and_false, Bool.false_eq_true] at h
  | some th =>
    simp only [ht, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    unfold allowsHost
    simp only [literalIp, Option.bind_some]
    cases hip : hostIp th with
    | none => rfl
    | some ip =>
      simp only [Bool.or_eq_true]
      right
      rcases h.2 with hd | ha
      · have : addressClass ip = .Public := by
          by_contra hne
          have := (isDisallowedHost_iff_addressClass_ne_public th ip hip).mpr hne
          rw [hd] at this; cases this
        rw [this]; cases allowPrivate <;> rfl
      · unfold isAllowedDisallowedHost at ha
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, hip, Option.map_some,
          Option.some.injEq] at ha
        rcases ha with ⟨hp, hc⟩ | ⟨hb, hl⟩
        · subst hp; rw [hc]
          simp only [isAllowed, ↓reduceIte, withPrivate, decide_eq_true_eq]
          split <;> simp_all only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
            or_true]
        · rw [addressClass_eq_loopback_of_isLoopbackHost th ip hip hl]
          cases hB : ExtModel.urlHost base with
          | none => rw [hB] at hb; cases hb
          | some bh =>
            rw [hB] at hb
            have hm := loopback_mem_baseClasses bh hb
            cases allowPrivate
            · simp only [isAllowed, Bool.false_eq_true, ↓reduceIte, hm, decide_true]
            · simp only [↓reduceIte, isAllowed, decide_eq_true_eq, withPrivate]
              split
              · exact hm
              · exact List.mem_append_left _ hm

/-- **The resolver allows the base URL's own IP literal, whatever its class** (H14, recorded bug
of the resolver, human decision 2026-11-27): for a base URL with host `host` (none, a domain or
an IP literal), the resolver policy (N07 `allowsHost` with the base's literal `literalIp host`,
the `self.base_ip == Some(ip)` disjunct of `metadata_resolver.rs` line 167) allows a target
with the same host, for any granted classes, so also when the literal has class `Blocked`
(base `http://169.254.1.1:8080`, target `http://169.254.1.1:9090/`). The docs this contradicts
and the doc that states it on purpose: module docstring of `Proofs.Defs.AuthMetadata`, H14. A06
refuses such a target (`isAllowedMetadataUrl_eq_false_of_addressClass_eq_blocked`;
kernel-checked host-level cases at the end of `Proofs.Defs.AuthMetadata`). No premise. -/
theorem allowsHost_literalIp_self (host : Option (url.host.Host Str))
    (classes : List AddressClass) :
    allowsHost (literalIp host) classes host = true := by
  unfold allowsHost
  cases literalIp host <;> simp only [decide_true, Bool.true_or]

/-- **A08, `stringOfUtf8` inverts `utf8Bytes` on UTF-8 bytes**: the mismatch payload is the
received issuer. -/
theorem utf8Bytes_stringOfUtf8 (l : List U8) (h : ExtModel.IsUtf8 l) :
    utf8Bytes (stringOfUtf8 l) = l := by
  obtain ⟨t, rfl⟩ := h
  simp only [stringOfUtf8, strOfBytes?_utf8, Option.getD_some, utf8Bytes_eq_utf8]

/-- **A08, RFC 9207 §2.4**: with a recorded issuer `e` and a received issuer `r`, the callback
check succeeds exactly when `r` is byte-identical to `e` (no normalization, no trailing-slash
tolerance). -/
theorem responseIssuerCheck_some_some_eq_ok_iff (e : String) (requireIssuer : Bool)
    (r : List U8) :
    responseIssuerCheck (some e) requireIssuer (some r) = .Ok () ↔ r = utf8Bytes e := by
  by_cases h : r = utf8Bytes e <;> simp only [responseIssuerCheck, h, ↓reduceIte, reduceCtorEq]

/-- **A09, the bare RFC 8414 well-known path gives the empty issuer path** (RFC 8414 §3.1, an
issuer without path). -/
theorem issuerPath_oauthWellKnown : issuerPath oauthWellKnown = some [] := by
  rw [issuerPath, ite_eq_left_of_eq_true _ _ (eq_true (Or.inl rfl))]

/-- **A09, the bare OpenID Connect well-known path gives the empty issuer path** (OpenID Connect
Discovery 1.0 §4, an issuer without path). -/
theorem issuerPath_oidcWellKnown : issuerPath oidcWellKnown = some [] := by
  rw [issuerPath, ite_eq_left_of_eq_true _ _ (eq_true (Or.inr rfl))]

/-- **A09, RFC 8414 §3.1 path insertion is inverted**: the discovery path
`/.well-known/oauth-authorization-server/` followed by `s` gives the issuer path `s`. -/
theorem issuerPath_oauthWellKnown_append (s : List U8) :
    issuerPath (oauthWellKnown ++ slashByte :: s) = some s := by
  have hl : (oauthWellKnown ++ slashByte :: s).length = 40 + s.length := by
    simp only [List.length_append, length_oauthWellKnown, List.length_cons]; omega
  have h1 : ¬ (oauthWellKnown ++ slashByte :: s = oauthWellKnown ∨
      oauthWellKnown ++ slashByte :: s = oidcWellKnown) := by
    rintro (h | h) <;> have := congrArg List.length h <;> simp only [hl, length_oauthWellKnown,
      length_oidcWellKnown] at this <;> omega
  have h2 : oauthWellKnown ++ [slashByte] <+: oauthWellKnown ++ slashByte :: s :=
    ⟨s, by simp only [List.append_assoc, List.cons_append, List.nil_append]⟩
  rw [issuerPath, ite_eq_right_of_eq_false _ _ (eq_false h1),
    ite_eq_left_of_eq_true _ _ (eq_true h2)]
  simp only [List.drop_length_add_append, List.drop_succ_cons, List.drop_zero]

/-- **A09, OpenID Connect path insertion is inverted** (the MCP compatibility form): the
discovery path `/.well-known/openid-configuration/` followed by `s` gives the issuer path `s`. -/
theorem issuerPath_oidcWellKnown_append (s : List U8) :
    issuerPath (oidcWellKnown ++ slashByte :: s) = some s := by
  have hp : oidcWellKnown ++ [slashByte] <+: oidcWellKnown ++ slashByte :: s := ⟨s,
    by simp only [List.append_assoc, List.cons_append, List.nil_append]⟩
  have h1 : ¬ (oidcWellKnown ++ slashByte :: s = oauthWellKnown ∨
      oidcWellKnown ++ slashByte :: s = oidcWellKnown) := by
    rintro (h | h)
    · apply not_oidcWellKnown_slash_prefix_oauthWellKnown_slash
      rw [h] at hp
      exact hp.trans (List.prefix_append _ _)
    · have := congrArg List.length h; simp only [List.length_append, List.length_cons,
        Nat.add_eq_left, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero,
        and_false] at this
  have h2 : ¬ oauthWellKnown ++ [slashByte] <+: oidcWellKnown ++ slashByte :: s := by
    intro h
    apply not_oidcWellKnown_slash_prefix_oauthWellKnown_slash
    exact List.prefix_of_prefix_length_le hp h (by simp only [List.length_append,
      length_oidcWellKnown, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      length_oauthWellKnown, Nat.reduceLeDiff])
  rw [issuerPath, ite_eq_right_of_eq_false _ _ (eq_false h1),
    ite_eq_right_of_eq_false _ _ (eq_false h2),
    ite_eq_left_of_eq_true _ _ (eq_true hp)]
  simp only [List.drop_length_add_append, List.drop_succ_cons, List.drop_zero]

/-- **A09, OpenID Connect path appending is inverted** (OpenID Connect Discovery 1.0 §4): a path
`p` followed by `/.well-known/openid-configuration` gives `p` without its leading `/` bytes,
unless `p ++ oidcWellKnown` starts with one of the two path-insertion prefixes (premise (P),
where the earlier branches of upstream lines 2752–2757 take precedence). -/
theorem issuerPath_append_oidcWellKnown (p : List U8)
    (h_oauth : ¬ oauthWellKnown ++ [slashByte] <+: p ++ oidcWellKnown)
    (h_oidc : ¬ oidcWellKnown ++ [slashByte] <+: p ++ oidcWellKnown) :
    issuerPath (p ++ oidcWellKnown) = some (p.dropWhile (· = slashByte)) := by
  by_cases hp : p = []
  · subst hp
    simp only [List.nil_append, List.dropWhile_nil]
    exact issuerPath_oidcWellKnown
  · have h1 : ¬ (p ++ oidcWellKnown = oauthWellKnown ∨ p ++ oidcWellKnown = oidcWellKnown) := by
      rintro (h | h)
      · apply not_oidcWellKnown_suffix_oauthWellKnown; rw [← h]; exact List.suffix_append _ _
      · apply hp
        have := congrArg List.length h
        simpa only [List.length_append, Nat.add_eq_right, List.length_eq_zero_iff] using this
    rw [issuerPath, ite_eq_right_of_eq_false _ _ (eq_false h1),
      ite_eq_right_of_eq_false _ _ (eq_false h_oauth),
      ite_eq_right_of_eq_false _ _ (eq_false h_oidc),
        ite_eq_left_of_eq_true _ _ (eq_true (List.suffix_append _ _))]
    simp only [List.length_append, add_tsub_cancel_right, List.take_left']

/-- **A09, issuer matching is reflexive.** -/
theorem issuersMatch_self (l : List U8) : issuersMatch l l = true := by
  simp only [issuersMatch, decide_true, Bool.or_self]

/-- **A09, issuer matching is symmetric.** -/
theorem issuersMatch_comm (r e : List U8) : issuersMatch r e = issuersMatch e r := by
  unfold issuersMatch
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor <;> rintro (h | h) <;> simp only [h, or_self, or_true]

/-- **A09, what the trailing-slash tolerance allows** (H15, recorded bug: RFC 8414 §3.3 requires
identical issuers; the code tolerates exactly the final `/` of a root URL, as the upstream test
`authorization_metadata_allows_only_root_trailing_slash_equivalence`, lines 5141–5151, asserts):
matching issuers are byte-equal, or one is the other followed by `/`, and the shorter one parses
as a URL whose path is empty or `/` (query and fragment allowed, so the `/` may be the last byte
of a query or a fragment: `https://as.example?x/` matches `https://as.example?x`). -/
theorem eq_or_eq_append_slash_of_issuersMatch (r e : List U8) (h : issuersMatch r e = true) :
    r = e ∨ (e = r ++ [slashByte] ∧ isRootUrl r = true) ∨
      (r = e ++ [slashByte] ∧ isRootUrl e = true) := by
  unfold issuersMatch at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact Or.inl h
  unfold trimRootSlash at h
  split_ifs at h with hr he he
  · left
    rw [eq_dropLast_append_slash_of_suffix hr.1, eq_dropLast_append_slash_of_suffix he.1, h]
  · right; right
    refine ⟨?_, ?_⟩
    · rw [eq_dropLast_append_slash_of_suffix hr.1, h]
    · rw [← h]; exact hr.2
  · right; left
    refine ⟨?_, ?_⟩
    · rw [eq_dropLast_append_slash_of_suffix he.1, h]
    · rw [h]; exact he.2
  · exact Or.inl h

/-- **A10, a path covers itself.** -/
theorem pathCovers_self (p : List U8) : pathCovers p p = true := by
  simp only [pathCovers, decide_true, List.prefix_rfl, lt_self_iff_false, not_false_eq_true,
    getElem?_neg, reduceCtorEq, decide_false, Bool.or_false, Bool.true_and, Bool.true_or]

/-- **A10, a covering path is a byte prefix of the expected path** (the resource identifier names
the base URL's path or a segment-aligned ancestor of it, never a descendant). -/
theorem prefix_of_pathCovers (expectedPath actualPath : List U8)
    (h : pathCovers expectedPath actualPath = true) : actualPath <+: expectedPath := by
  unfold pathCovers at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · rw [h]
  · exact h.1

/-- **A10, an ancestor at a segment boundary covers** (H13, recorded bug: looser than the
"identical" of RFC 9728 §3.3; deliberate per the upstream test
`resource_identifier_matching_allows_matching_host_or_parent_path`): the path `a` covers every
expected path `a ++ "/" ++ b`, for example `/mcp` covers `/mcp/tools`. -/
theorem pathCovers_append_slash_append (a b : List U8) :
    pathCovers (a ++ slashByte :: b) a = true := by
  simp only [pathCovers, List.append_right_eq_self, reduceCtorEq, decide_false, List.prefix_append,
    decide_true, List.length_append, List.length_cons, lt_add_iff_pos_right, Order.lt_add_one_iff,
    zero_le, getElem?_pos, Std.le_refl, List.getElem_append_right, tsub_self,
    List.getElem_cons_zero, Bool.or_true, Bool.and_self]

/-- **A10, the expected path with a final `/` added does not cover it**: `/mcp/` does not cover
`/mcp`. This agrees with RFC 9728 §3.3 and with the upstream test
`resource_identifier_matching_allows_matching_host_or_parent_path` (lines 7187–7190), and is not
part of the recorded bug H13; it is inconsistent with the ancestor rule
(`pathCovers_append_slash_append`: `/mcp` covers `/mcp/tools`). -/
theorem pathCovers_append_slash_eq_false (p : List U8) :
    pathCovers p (p ++ [slashByte]) = false := by
  have h1 : p ≠ p ++ [slashByte] := by
    intro h; have := congrArg List.length h; simp only [List.length_append, List.length_cons,
      List.length_nil, zero_add, Nat.left_eq_add, one_ne_zero] at this
  have h2 : ¬ p ++ [slashByte] <+: p := by
    intro h; have := h.length_le; simp only [List.length_append, List.length_cons, List.length_nil,
      zero_add, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero] at this
  simp only [pathCovers, h1, decide_false, h2, List.suffix_append, decide_true, List.length_append,
    List.length_cons, List.length_nil, zero_add, add_lt_iff_neg_left, not_lt_zero,
    not_false_eq_true, getElem?_neg, reduceCtorEq, Bool.or_false, Bool.and_true, Bool.or_self]

/-- **A10, a URL is a valid resource identifier of itself** (upstream line 2999). -/
theorem isResourceIdentifierValid_self (u : url.Url) : isResourceIdentifierValid u u = true := by
  simp only [isResourceIdentifierValid, decide_true, Bool.and_self, Bool.true_and, Bool.true_or]

end Defs.AuthMetadata

/-! ## Compositions: the security meaning end to end -/

namespace rmcp.transport.auth.AuthorizationManager

/-- **A06 with A05: a cloud-metadata name is never allowed** (premise (B)): a target whose host is
a domain that normalizes to `metadata`, `metadata.google.internal` or `metadata.azure.internal`
is refused, whatever the base URL and `allow_private`. Consequence of
`is_allowed_metadata_url_spec` and the premise-free law
`Defs.AuthMetadata.isAllowedMetadataUrl_eq_false_of_isCloudMetadataName`. No target premise:
such a domain is ASCII, hence UTF-8 (`normalizeHost` changes only ASCII letters and trailing
dots). (B) is needed: the base URL's host is read (upstream line 1434). -/
theorem is_allowed_metadata_url_eq_false_of_isCloudMetadataName (base_url target : url.Url)
    (allow_private : Bool) (d : Str) (h_base : HostUtf8 base_url)
    (h_host : ExtModel.urlHost target = some (url.host.Host.Domain d))
    (hc : isCloudMetadataName d.val = true) :
    is_allowed_metadata_url base_url target allow_private ⦃ (result : Bool) =>
      result = false ⦄ := by
  rw [is_allowed_metadata_url_eq]
  cases hh : isHttpUrl target
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
  · obtain ⟨u, hu⟩ := exists_strOfBytes?_normalizeHost_eq_some_of_isCloudMetadataName d hc
    have hd : isDisallowedHost (url.host.Host.Domain d) = true := by
      simp only [isDisallowedHost, hc, Bool.or_true]
    have hl : is_loopback_metadata_host (url.host.Host.Domain d) =
        ok (isLoopbackHost (url.host.Host.Domain d)) := by
      rw [is_loopback_metadata_host_domain_eq, hu]; rfl
    simp only [↓reduceIte, h_host, is_disallowed_metadata_host_domain_eq, hu, hd, bind_ok]
    rw [is_allowed_disallowed_host_eq_of_is_loopback_metadata_host_eq base_url _ allow_private
      h_base hl, WP.spec_ok]
    simp only [isAllowedDisallowedHost, hostIp, Option.map_none, reduceCtorEq, decide_false,
      Bool.and_false, isLoopbackHost,
      Defs.AuthMetadata.isLocalhostName_eq_false_of_isCloudMetadataName _ hc, Bool.or_self]

/-- **A06 with A05 and N01: a `Blocked` literal is never allowed** (premise (B)): a target whose
host is an IP literal of class `Blocked` is refused, whatever the base URL and `allow_private`,
also when it is the base URL's own literal (which the resolver allows, H14,
`Defs.AuthMetadata.allowsHost_literalIp_self`). Consequence of `is_allowed_metadata_url_spec`
and `Defs.AuthMetadata.isAllowedMetadataUrl_eq_false_of_addressClass_eq_blocked`. No target
premise (an IP literal has no domain). -/
theorem is_allowed_metadata_url_eq_false_of_addressClass_eq_blocked (base_url target : url.Url)
    (allow_private : Bool) (h : url.host.Host Str) (h_base : HostUtf8 base_url)
    (h_host : ExtModel.urlHost target = some h)
    (h_blocked : (hostIp h).map addressClass = some AddressClass.Blocked) :
    is_allowed_metadata_url base_url target allow_private ⦃ (result : Bool) =>
      result = false ⦄ := by
  have hT : isHttpUrl target = true → HostUtf8 target := by
    intro _ d hd
    rw [h_host] at hd; cases hd; simp only [hostIp, Option.map_none, reduceCtorEq] at h_blocked
  refine WP.spec_mono (is_allowed_metadata_url_spec base_url target allow_private h_base hT) ?_
  intro r hr
  rw [hr, isAllowedMetadataUrl_eq_false_of_addressClass_eq_blocked _ _ _ h h_host h_blocked]

/-- **A06, a `Private` literal** (premise (B)): allowed exactly when the target is HTTP(S) with a
host string and `allow_private` holds (H10: the cloud-metadata endpoints in private ranges
included). Consequence of `is_allowed_metadata_url_spec` and
`Defs.AuthMetadata.isAllowedMetadataUrl_eq_of_addressClass_eq_private`. No target premise (an
IP literal has no domain). -/
theorem is_allowed_metadata_url_eq_of_addressClass_eq_private (base_url target : url.Url)
    (allow_private : Bool) (h : url.host.Host Str) (h_base : HostUtf8 base_url)
    (h_host : ExtModel.urlHost target = some h)
    (h_private : (hostIp h).map addressClass = some AddressClass.Private) :
    is_allowed_metadata_url base_url target allow_private ⦃ (result : Bool) =>
      result = (isHttpUrl target && allow_private) ⦄ := by
  have hT : isHttpUrl target = true → HostUtf8 target := by
    intro _ d hd
    rw [h_host] at hd; cases hd; simp only [hostIp, Option.map_none, reduceCtorEq] at h_private
  refine WP.spec_mono (is_allowed_metadata_url_spec base_url target allow_private h_base hT) ?_
  intro r hr
  rw [hr, isAllowedMetadataUrl_eq_of_addressClass_eq_private _ _ _ h h_host h_private]

/-- **A06, a `Loopback` literal** (premise (B)): allowed exactly when the target is HTTP(S) with a
host string, the base URL's host is a loopback host and the target's host is `127/8` or `::1`;
`allow_private` plays no role. Consequence of `is_allowed_metadata_url_spec` and
`Defs.AuthMetadata.isAllowedMetadataUrl_eq_of_addressClass_eq_loopback`. No target premise (an
IP literal has no domain). -/
theorem is_allowed_metadata_url_eq_of_addressClass_eq_loopback (base_url target : url.Url)
    (allow_private : Bool) (h : url.host.Host Str) (h_base : HostUtf8 base_url)
    (h_host : ExtModel.urlHost target = some h)
    (h_loopback : (hostIp h).map addressClass = some AddressClass.Loopback) :
    is_allowed_metadata_url base_url target allow_private ⦃ (result : Bool) =>
      result = (isHttpUrl target && (ExtModel.urlHost base_url).any isLoopbackHost &&
        isLoopbackHost h) ⦄ := by
  have hT : isHttpUrl target = true → HostUtf8 target := by
    intro _ d hd
    rw [h_host] at hd; cases hd; simp only [hostIp, Option.map_none, reduceCtorEq] at h_loopback
  refine WP.spec_mono (is_allowed_metadata_url_spec base_url target allow_private h_base hT) ?_
  intro r hr
  rw [hr, isAllowedMetadataUrl_eq_of_addressClass_eq_loopback _ _ _ h h_host h_loopback]

/-- **A06, a `localhost` name** (premises (T), (B)): allowed exactly when the target is HTTP(S)
with a host string and the base URL's host is a loopback host. Consequence of
`is_allowed_metadata_url_spec` and `Defs.AuthMetadata.isAllowedMetadataUrl_eq_of_isLocalhostName`.
-/
theorem is_allowed_metadata_url_eq_of_isLocalhostName (base_url target : url.Url)
    (allow_private : Bool) (d : Str) (h_base : HostUtf8 base_url)
    (h_target : isHttpUrl target = true → HostUtf8 target)
    (h_host : ExtModel.urlHost target = some (url.host.Host.Domain d))
    (h_local : isLocalhostName d.val = true) :
    is_allowed_metadata_url base_url target allow_private ⦃ (result : Bool) =>
      result = (isHttpUrl target && (ExtModel.urlHost base_url).any isLoopbackHost) ⦄ := by
  refine WP.spec_mono
    (is_allowed_metadata_url_spec base_url target allow_private h_base h_target) ?_
  intro r hr
  rw [hr, Defs.AuthMetadata.isAllowedMetadataUrl_eq_of_isLocalhostName _ _ _ d h_host h_local]

/-- **A06, every other host** (premise (T)): a target whose host the guard does not reject is
allowed exactly when it is HTTP(S) with a host string (the law
`Defs.AuthMetadata.isAllowedMetadataUrl_eq_of_isDisallowedHost_eq_false`). No base premise: the
call returns at upstream line 1422 (or earlier, lines 1413–1419) without reading the base URL's
host, so this does not follow from `is_allowed_metadata_url_spec`, which assumes (B). With the
SDK's default HTTP client and no proxy, a domain is resolved later, under the resolver's
address policy (N09); with a custom HTTP client or through a proxy, nothing filters its
addresses (H16). -/
theorem is_allowed_metadata_url_eq_of_isDisallowedHost_eq_false (base_url target : url.Url)
    (allow_private : Bool) (h : url.host.Host Str)
    (h_target : isHttpUrl target = true → HostUtf8 target)
    (h_host : ExtModel.urlHost target = some h) (h_ok : isDisallowedHost h = false) :
    is_allowed_metadata_url base_url target allow_private ⦃ (result : Bool) =>
      result = isHttpUrl target ⦄ := by
  rw [is_allowed_metadata_url_eq]
  cases hh : isHttpUrl target
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
  · simp only [↓reduceIte, h_host]
    have hu : ∀ d, h = url.host.Host.Domain d → IsUtf8 d.val :=
      fun d hd => h_target hh d (h_host.trans (by rw [hd]))
    simp only [is_disallowed_metadata_host_eq h hu, h_ok, bind_ok, Bool.false_eq_true, ↓reduceIte,
      WP.spec_ok]

/-- **A07 on success: the URL is the candidate the value names.** If
`resolve_resource_metadata_url value base_url allow_private` returns `some u`, then `u` is the
trimmed value parsed, or else resolved against the base URL (`metadataCandidate`). Covers only
successful calls and does not show that the call succeeds. No premise. -/
theorem metadataCandidate_eq_of_resolve_resource_metadata_url_eq_ok_some (value : Str)
    (base_url : url.Url) (allow_private : Bool) (u : url.Url)
    (h : resolve_resource_metadata_url value base_url allow_private = ok (some u)) :
    metadataCandidate value.val base_url = some u :=
  (of_resolve_resource_metadata_url_eq_ok_some value base_url allow_private u h).1

/-- **A07 on success: the URL is HTTP(S) with a host string** (both acceptances of upstream lines
1458 and 1465 test A04). Covers only successful calls. No premise. -/
theorem isHttpUrl_of_resolve_resource_metadata_url_eq_ok_some (value : Str) (base_url : url.Url)
    (allow_private : Bool) (u : url.Url)
    (h : resolve_resource_metadata_url value base_url allow_private = ok (some u)) :
    isHttpUrl u = true := by
  rcases (of_resolve_resource_metadata_url_eq_ok_some value base_url allow_private u h).2 with
    h1 | ⟨_, h2⟩
  · simp only [Bool.and_eq_true] at h1; exact h1.1
  · exact Defs.AuthMetadata.isHttpUrl_of_isAllowedMetadataUrl _ _ _ h2

/-- **A07 on success: same origin, or allowed by the metadata URL policy.** If the call returns
`some u`, `u` is same-origin with the base URL or A06 allows it with the same `allow_private`.
With the premise-free laws `Defs.AuthMetadata.isAllowedMetadataUrl_eq_…` this gives, for a
cross-origin `u`, the consequences for each kind of host without UTF-8 premises (for example
`allow_private_eq_true_of_resolve_resource_metadata_url_eq_ok_some`). Covers only successful
calls. No premise. -/
theorem isSameOrigin_or_isAllowedMetadataUrl_of_resolve_resource_metadata_url_eq_ok_some
    (value : Str) (base_url : url.Url) (allow_private : Bool) (u : url.Url)
    (h : resolve_resource_metadata_url value base_url allow_private = ok (some u)) :
    isSameOrigin base_url u = true ∨ isAllowedMetadataUrl base_url u allow_private = true := by
  rcases (of_resolve_resource_metadata_url_eq_ok_some value base_url allow_private u h).2 with
    h1 | ⟨_, h2⟩
  · simp only [Bool.and_eq_true] at h1; exact Or.inl h1.2
  · exact Or.inr h2

/-- **A07 on success: no downgrade from `https`.** If the base URL's scheme is `https` and the
call returns `some u`, then `u`'s scheme is `https` (same origin implies the same scheme; the
check of upstream lines 1461–1464 refuses the rest). Covers only successful calls. No premise
beyond the `https` base. -/
theorem urlScheme_eq_https_of_resolve_resource_metadata_url_eq_ok_some (value : Str)
    (base_url : url.Url) (allow_private : Bool) (u : url.Url)
    (h_https : (ExtModel.urlScheme base_url).val = utf8Bytes "https")
    (h : resolve_resource_metadata_url value base_url allow_private = ok (some u)) :
    (ExtModel.urlScheme u).val = utf8Bytes "https" := by
  rcases (of_resolve_resource_metadata_url_eq_ok_some value base_url allow_private u h).2 with
    h1 | ⟨h2, _⟩
  · simp only [Bool.and_eq_true] at h1
    rw [← Defs.AuthMetadata.urlScheme_eq_of_isSameOrigin _ _ h1.2]; exact h_https
  · simp only [h_https, decide_true, Bool.true_and, Bool.not_eq_false', decide_eq_true_eq] at h2
    exact h2

/-- **A07 on success: a cross-origin `Private` literal needs `allow_private`** (H10). If the
call returns `some u`, `u` is not same-origin with the base URL and its host is an IP literal of
class `Private`, then `allow_private` holds: a private base URL does not suffice (H12), and with
`allow_private` every private literal passes, the cloud-metadata endpoints `100.100.100.200` and
`fd00:ec2::254` included (H10). Covers only successful calls. No premise. -/
theorem allow_private_eq_true_of_resolve_resource_metadata_url_eq_ok_some (value : Str)
    (base_url : url.Url) (allow_private : Bool) (u : url.Url) (h : url.host.Host Str)
    (h_ok : resolve_resource_metadata_url value base_url allow_private = ok (some u))
    (h_origin : isSameOrigin base_url u = false) (h_host : ExtModel.urlHost u = some h)
    (h_private : (hostIp h).map addressClass = some AddressClass.Private) :
    allow_private = true := by
  rcases (of_resolve_resource_metadata_url_eq_ok_some value base_url allow_private u h_ok).2 with
    h1 | ⟨_, h2⟩
  · simp only [h_origin, Bool.and_false, Bool.false_eq_true] at h1
  · rw [Defs.AuthMetadata.isAllowedMetadataUrl_eq_of_addressClass_eq_private _ _ _ h h_host
      h_private] at h2
    simp only [Bool.and_eq_true] at h2
    exact h2.2

/-- **A07 on success: a cross-origin `Loopback` literal needs a loopback base.** If the call
returns `some u`, `u` is not same-origin with the base URL and its host is an IP literal of class
`Loopback`, then the base URL's host is a loopback host (`localhost` name, `127/8` or `::1`) and
`u`'s host is `127/8` or `::1` (not an IPv6 embedding of `127/8`, H12). Covers only successful
calls. No premise. -/
theorem isLoopbackHost_of_resolve_resource_metadata_url_eq_ok_some (value : Str)
    (base_url : url.Url) (allow_private : Bool) (u : url.Url) (h : url.host.Host Str)
    (h_ok : resolve_resource_metadata_url value base_url allow_private = ok (some u))
    (h_origin : isSameOrigin base_url u = false) (h_host : ExtModel.urlHost u = some h)
    (h_loopback : (hostIp h).map addressClass = some AddressClass.Loopback) :
    (ExtModel.urlHost base_url).any isLoopbackHost = true ∧ isLoopbackHost h = true := by
  rcases (of_resolve_resource_metadata_url_eq_ok_some value base_url allow_private u h_ok).2 with
    h1 | ⟨_, h2⟩
  · simp only [h_origin, Bool.and_false, Bool.false_eq_true] at h1
  · rw [Defs.AuthMetadata.isAllowedMetadataUrl_eq_of_addressClass_eq_loopback _ _ _ h h_host
      h_loopback] at h2
    simp only [Bool.and_eq_true] at h2
    exact ⟨h2.1.2, h2.2⟩

/-- **A07, a same-origin HTTP(S) candidate is accepted**, whatever its host (also a loopback,
private or blocked literal: the base URL's own origin is trusted; upstream lines 1458–1460
return before the policy check, and no host is read). No premise: same origin with an HTTP(S)
candidate implies an `http` or `https` base URL (`urlScheme_eq_of_isSameOrigin`), so the AD8
premise (H) holds. -/
theorem resolve_resource_metadata_url_eq_some_of_isSameOrigin (value : Str) (base_url : url.Url)
    (allow_private : Bool) (u : url.Url)
    (h_candidate : metadataCandidate value.val base_url = some u)
    (h_http : isHttpUrl u = true) (h_origin : isSameOrigin base_url u = true) :
    resolve_resource_metadata_url value base_url allow_private ⦃ (result : Option url.Url) =>
      result = some u ⦄ := by
  rw [resolve_resource_metadata_url_eq, h_candidate]
  simp only [resolveTail, h_http, h_origin, Bool.and_self, ↓reduceIte, WP.spec_ok]

/-- **A07 with A06: a cross-origin `Blocked` literal is refused** (premises (H), (B); no premise
on the candidate's host, an IP literal). The call does not fail and returns `none`; that a
successful call never returns such a URL needs no premise
(`isSameOrigin_or_isAllowedMetadataUrl_of_resolve_resource_metadata_url_eq_ok_some` with
`Defs.AuthMetadata.isAllowedMetadataUrl_eq_false_of_addressClass_eq_blocked`). -/
theorem resolve_resource_metadata_url_eq_none_of_addressClass_eq_blocked (value : Str)
    (base_url : url.Url) (allow_private : Bool) (u : url.Url) (h : url.host.Host Str)
    (h_scheme : isHttpScheme (ExtModel.urlScheme base_url).val = true)
    (h_base : HostUtf8 base_url)
    (h_candidate : metadataCandidate value.val base_url = some u)
    (h_origin : isSameOrigin base_url u = false) (h_host : ExtModel.urlHost u = some h)
    (h_blocked : (hostIp h).map addressClass = some AddressClass.Blocked) :
    resolve_resource_metadata_url value base_url allow_private ⦃ (result : Option url.Url) =>
      result = none ⦄ := by
  have _ := h_scheme
  exact resolve_resource_metadata_url_eq_none_of_not_allowed value base_url u allow_private
    h_candidate h_origin
    (is_allowed_metadata_url_eq_false_of_addressClass_eq_blocked base_url u allow_private h
      h_base h_host h_blocked)

/-- **A07 with A06: a cross-origin cloud-metadata name is refused** (premises (H), (B); no
premise on the candidate's host, which is ASCII). The call does not fail and returns `none`;
that a successful call never returns such a URL needs no premise
(`isSameOrigin_or_isAllowedMetadataUrl_of_resolve_resource_metadata_url_eq_ok_some` with
`Defs.AuthMetadata.isAllowedMetadataUrl_eq_false_of_isCloudMetadataName`). -/
theorem resolve_resource_metadata_url_eq_none_of_isCloudMetadataName (value : Str)
    (base_url : url.Url) (allow_private : Bool) (u : url.Url) (d : Str)
    (h_scheme : isHttpScheme (ExtModel.urlScheme base_url).val = true)
    (h_base : HostUtf8 base_url)
    (h_candidate : metadataCandidate value.val base_url = some u)
    (h_origin : isSameOrigin base_url u = false)
    (h_host : ExtModel.urlHost u = some (url.host.Host.Domain d))
    (hc : isCloudMetadataName d.val = true) :
    resolve_resource_metadata_url value base_url allow_private ⦃ (result : Option url.Url) =>
      result = none ⦄ := by
  have _ := h_scheme
  exact resolve_resource_metadata_url_eq_none_of_not_allowed value base_url u allow_private
    h_candidate h_origin
    (is_allowed_metadata_url_eq_false_of_isCloudMetadataName base_url u allow_private d
      h_base h_host hc)

/-- **A08, RFC 9207 §2.4 end to end** (premises (S), (R)): with a recorded issuer `e` and a
received issuer `r`, the callback check returns `Ok` exactly when the bytes of `r` are those of
`e`, and otherwise `Err (AuthorizationServerMismatch e r)`. -/
theorem check_authorization_response_issuer_eq_ok_iff (stored_state : StoredAuthorizationState)
    (e : String) (r : Str) (h_expected : stored_state.expected_issuer = some e)
    (h_fits : e.utf8ByteSize ≤ Usize.max) (h_utf8 : ExtModel.IsUtf8 r.val) :
    check_authorization_response_issuer stored_state (some r)
      ⦃ (result : core.result.Result Unit IssuerError) =>
      (result = .Ok () ↔ r.val = utf8Bytes e) ∧
      (r.val ≠ utf8Bytes e → ∃ rs, utf8Bytes rs = r.val ∧
        result = .Err (.AuthorizationServerMismatch e rs)) ⦄ := by
  refine WP.spec_mono (check_authorization_response_issuer_spec stored_state (some r)
    (fun e' he' => by rw [h_expected] at he'; cases he'; exact h_fits)
    (fun _ r' _ hr' => by cases hr'; exact h_utf8)) ?_
  intro res hres
  rw [hres, h_expected]
  simp only [Option.map_some]
  refine ⟨Defs.AuthMetadata.responseIssuerCheck_some_some_eq_ok_iff e _ r.val, fun hne => ?_⟩
  refine ⟨stringOfUtf8 r.val, Defs.AuthMetadata.utf8Bytes_stringOfUtf8 _ h_utf8, ?_⟩
  simp only [responseIssuerCheck, hne, ↓reduceIte]

/-- **A09, the spec theorem without an explicit expected issuer** (premises (S), (D), (AD7)): the
check compares the metadata's `issuer` with the issuer derived from the discovery URL
(`derivedIssuer`: the RFC 8414 §3.1 path insertion `…/.well-known/oauth-authorization-server/s`
gives the issuer path `s`, `issuerPath_oauthWellKnown_append`; the OpenID Connect forms
likewise). H9: a recorded issue in this check, under private disclosure; details withheld until
it is reported. -/
theorem check_authorization_metadata_issuer_spec_none (allow_missing_issuer : Bool)
    (discovery_url : url.Url) (metadata : AuthorizationMetadata)
    (h_received : ∀ r, metadata.issuer = some r → r.utf8ByteSize ≤ Usize.max)
    (h_derived : ∀ e, derivedIssuer discovery_url = some e → e.utf8ByteSize ≤ Usize.max)
    (h_discovery : DiscoveryUrlFits discovery_url) :
    check_authorization_metadata_issuer allow_missing_issuer discovery_url none metadata
      ⦃ (result : core.result.Result Unit IssuerError) =>
      result = metadataIssuerCheck allow_missing_issuer (derivedIssuer discovery_url)
        metadata.issuer ⦄ :=
  check_authorization_metadata_issuer_spec allow_missing_issuer discovery_url none metadata
    (fun s hs => by cases hs) h_received (fun _ => h_derived) (fun _ => h_discovery)

/-- **A09, a mismatch always yields `AuthorizationServerMismatch` with both issuers** (premises
(U), (S), (D), (AD7)): if the expected issuer (explicit, or derived) is `e`, the metadata's
`issuer` is `r` and they do not match (`issuersMatch`), the result is
`Err (AuthorizationServerMismatch e r)`, whatever `allow_missing_issuer`. -/
theorem check_authorization_metadata_issuer_eq_mismatch (allow_missing_issuer : Bool)
    (discovery_url : url.Url) (expected_issuer : Option Str) (metadata : AuthorizationMetadata)
    (e r : String)
    (h_utf8 : ∀ s, expected_issuer = some s → ExtModel.IsUtf8 s.val)
    (h_received : r.utf8ByteSize ≤ Usize.max)
    (h_derived : expected_issuer = none →
      ∀ e', derivedIssuer discovery_url = some e' → e'.utf8ByteSize ≤ Usize.max)
    (h_discovery : expected_issuer = none → DiscoveryUrlFits discovery_url)
    (h_expected : expectedIssuerOf (expected_issuer.map (·.val)) discovery_url = some e)
    (h_issuer : metadata.issuer = some r)
    (h_mismatch : issuersMatch (utf8Bytes r) (utf8Bytes e) = false) :
    check_authorization_metadata_issuer allow_missing_issuer discovery_url expected_issuer
      metadata ⦃ (result : core.result.Result Unit IssuerError) =>
      result = .Err (.AuthorizationServerMismatch e r) ⦄ := by
  refine WP.spec_mono (check_authorization_metadata_issuer_spec allow_missing_issuer discovery_url
    expected_issuer metadata h_utf8
    (fun r' hr' => by rw [h_issuer] at hr'; cases hr'; exact h_received) h_derived
    h_discovery) ?_
  intro res hres
  rw [hres, h_expected, h_issuer]
  simp only [metadataIssuerCheck, h_mismatch, Bool.false_eq_true, ↓reduceIte]

/-- **A09 on success: RFC 8414 §3.3 up to a root slash.** If there is an expected issuer `e`
(explicit, or derived), the metadata names an `issuer` `r` and the check returns `Ok`, then `r`
and `e` are equal, or differ only by a final `/` after a URL whose path is empty or `/` (query
and fragment allowed; H15, recorded bug). Covers only successful calls and does not show that
the call succeeds. No premise (in particular no AD7 premise: the "on success" form needs no
domain restriction). -/
theorem eq_or_eq_append_slash_of_check_authorization_metadata_issuer_eq_ok
    (allow_missing_issuer : Bool) (discovery_url : url.Url) (expected_issuer : Option Str)
    (metadata : AuthorizationMetadata) (e r : String)
    (h_expected : expectedIssuerOf (expected_issuer.map (·.val)) discovery_url = some e)
    (h_issuer : metadata.issuer = some r)
    (h : check_authorization_metadata_issuer allow_missing_issuer discovery_url expected_issuer
      metadata = ok (.Ok ())) :
    r = e ∨ (utf8Bytes e = utf8Bytes r ++ [slashByte] ∧ isRootUrl (utf8Bytes r) = true) ∨
      (utf8Bytes r = utf8Bytes e ++ [slashByte] ∧ isRootUrl (utf8Bytes e) = true) := by
  have hu : ∀ s, expected_issuer = some s → ExtModel.IsUtf8 s.val := by
    intro s hs
    by_contra hn
    subst hs
    rw [check_authorization_metadata_issuer_fail allow_missing_issuer discovery_url s
      metadata hn] at h
    simp only [fail_not_ok] at h
  have hr : ∀ r', metadata.issuer = some r' → r'.utf8ByteSize ≤ Usize.max := by
    intro r' hr'
    by_contra hn
    cases hx : expected_issuer with
    | none =>
      subst hx
      rw [check_authorization_metadata_issuer_none_eq_fail allow_missing_issuer discovery_url
        metadata e r' h_expected hr' hn] at h
      simp only [fail_not_ok] at h
    | some s =>
      subst hx
      rw [check_authorization_metadata_issuer_fail_size allow_missing_issuer discovery_url s
        metadata r' (hu s rfl) hr' hn] at h
      simp only [fail_not_ok] at h
  have hd : expected_issuer = none →
      ∀ e', derivedIssuer discovery_url = some e' → e'.utf8ByteSize ≤ Usize.max := by
    intro hx e' he'
    by_contra hn
    subst hx
    rw [check_authorization_metadata_issuer_fail_derived allow_missing_issuer discovery_url
      metadata e' r he' hn h_issuer] at h
    simp only [fail_not_ok] at h
  rw [check_authorization_metadata_issuer_eq allow_missing_issuer discovery_url expected_issuer
    metadata hu hr hd, h_expected, h_issuer] at h
  simp only [metadataIssuerCheck, ok.injEq] at h
  have hm : issuersMatch (utf8Bytes r) (utf8Bytes e) = true := by
    by_contra hn
    simp only [hn, ↓reduceIte, reduceCtorEq] at h
  rcases Defs.AuthMetadata.eq_or_eq_append_slash_of_issuersMatch _ _ hm with h1 | h1 | h1
  · left
    exact Proofs.External.Utf8.utf8_injective h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

/-- **A10, when the resource is accepted** (premise (S)): the check returns `Ok` exactly when the
metadata names a resource that parses as a URL without fragment and is a valid identifier of the
base URL (`isResourceIdentifierValid`: equal, or same scheme, host and port with a path that
covers the base URL's path at a segment boundary; H13: query and user information are not
compared). -/
theorem check_resource_metadata_resource_eq_ok_iff (base_url : url.Url)
    (metadata : ResourceServerMetadata)
    (h_fits : ∀ r, metadata.resource = some r → r.utf8ByteSize ≤ Usize.max) :
    check_resource_metadata_resource base_url metadata
      ⦃ (result : core.result.Result Unit ProtectedResourceMetadataInvalidReason) =>
      (result = .Ok () ↔ ∃ r u, metadata.resource = some r ∧
        ExtModel.urlParse (utf8Bytes r) = .Ok u ∧ ExtModel.urlFragment u = none ∧
        isResourceIdentifierValid base_url u = true) ⦄ := by
  refine WP.spec_mono (check_resource_metadata_resource_spec base_url metadata h_fits) ?_
  intro res hres
  rw [hres]
  unfold resourceCheck
  cases hr : metadata.resource with
  | none => simp only [reduceCtorEq, false_and, exists_false]
  | some r =>
    simp only [Option.some.injEq, exists_and_left, exists_eq_left']
    cases hp : ExtModel.urlParse (utf8Bytes r) with
    | Err _ => simp only [reduceCtorEq, false_and, exists_false]
    | Ok u =>
      simp only [core.result.Result.Ok.injEq, exists_eq_left']
      cases hf : ExtModel.urlFragment u with
      | some _ => simp only [Option.isSome_some, ↓reduceIte, reduceCtorEq, false_and]
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, true_and]
        cases hv : isResourceIdentifierValid base_url u <;> simp only [Bool.false_eq_true,
          ↓reduceIte, reduceCtorEq]

end rmcp.transport.auth.AuthorizationManager
