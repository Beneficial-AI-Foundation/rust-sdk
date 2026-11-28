/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Defs
public import Proofs.Transport.AuthMetadata

@[expose] public section

/-!
# Internal spec file for the OAuth metadata URL and issuer checks of `auth.rs` (A04–A10)

These are guarantees about private associated functions of `AuthorizationManager` in
`crates/rmcp/src/transport/auth.rs` and the private helpers that translation patch 06 adds
(human decisions AD1–AD8, `formal/README.md`), kept out of `formal/specs/`, which holds only the
public API (human decision 2026-11-24; precedent `Proofs.Internal.Transport.Auth.MetadataResolver`).
Index of all guarantees: `formal/specs/README.md`.

One row per theorem below; the theorem is `Theorems.auth.AuthorizationManager.<Theorem>` for the
rows with an ID and `Theorems.auth.<Theorem>` for the `law` rows (statements about the
definitions of `Defs.AuthMetadata` only, with no Rust call), except `trimWhitespace_utf8Bytes`, a
law of the trusted model of `str::trim`, which is restated as
`Theorems.External.trimWhitespace_utf8Bytes` in `Proofs.Internal.External`. Statements appear in
the source order of the patched `auth.rs` (the translated copy; patch 06 places the helper
`is_allowed_disallowed_host` after `is_allowed_metadata_url`, and `is_resource_identifier_valid`
follows `check_resource_metadata_resource`), then the laws of `Defs.AuthMetadata` in the order of
the function they describe, then the compositions. The keys of the last column are explained
below the table.

| ID | Function | Theorem | Guarantee | Assumptions |
|---|---|---|---|---|
| A04 | `is_http_url` | `is_http_url` | never fails; `isHttpUrl` | none |
| A07 | `is_same_origin` | `is_same_origin` | never fails; `isSameOrigin` | none |
| A05 | `is_disallowed_metadata_hostname` | `is_disallowed_metadata_hostname` | never fails; `isDisallowedHostname` | none |
| A05 | `is_disallowed_metadata_host` | `is_disallowed_metadata_host` | never fails; `isDisallowedHost` (H11) | (U) |
| A05 | same | `is_disallowed_metadata_host_fail` | a domain that is not UTF-8: `undef` | none |
| A06 | `is_allowed_metadata_url` | `is_allowed_metadata_url` | never fails; `isAllowedMetadataUrl` (H12) | (T), (B) |
| A06 | same | `is_allowed_metadata_url_fail` | HTTP(S) target with a non-UTF-8 domain: `undef` | none |
| A06 | same | `is_allowed_metadata_url_fail_base` | the base domain is read and is not UTF-8: `undef` | none |
| A06 | `is_allowed_disallowed_host` | `is_allowed_disallowed_host` | never fails; `isAllowedDisallowedHost` (H10) | (U), (B) |
| A07 | `resolve_resource_metadata_url` | `resolve_resource_metadata_url` | never fails; `resolveResourceMetadataUrl` | (H), (B), (C) |
| A07 | same | `resolve_resource_metadata_url_fail` | the candidate's domain is read and is not UTF-8: `undef` | none |
| A07 | same | `resolve_resource_metadata_url_fail_base` | the base domain is read and is not UTF-8: `undef` | none |
| A08 | `check_authorization_response_issuer` | `check_authorization_response_issuer` | never fails; `responseIssuerCheck` | (S), (R) |
| A08 | same | `check_authorization_response_issuer_fail` | without (S): `maximumSizeExceeded` | none |
| A08 | same | `check_authorization_response_issuer_fail_undef` | without (R): `undef` | (S) |
| A09 | `expected_issuer_for_authorization_metadata_url` | `expected_issuer_for_authorization_metadata_url` | never fails; `derivedIssuer` (H9) | (AD7) |
| A09 | `issuer_identifiers_match` | `issuer_identifiers_match` | never fails; `issuersMatch` (H15) | (U') |
| A09 | same | `issuer_identifiers_match_fail` | without (U'): `undef` | none |
| A09 | `trim_root_slash` | `trim_root_slash` | never fails; `trimRootSlash` | (U) |
| A09 | same | `trim_root_slash_fail` | not UTF-8: `undef` | none |
| A09 | `is_root_url` | `is_root_url` | never fails; `isRootUrl` | none |
| A09 | `check_authorization_metadata_issuer` | `check_authorization_metadata_issuer` | never fails; `metadataIssuerCheck` (H9) | (U), (S), (D), (AD7) |
| A09 | same | `check_authorization_metadata_issuer_fail` | explicit issuer not UTF-8: `undef` | none |
| A09 | same | `check_authorization_metadata_issuer_fail_size` | received issuer too long: `maximumSizeExceeded` | (U) |
| A09 | same | `check_authorization_metadata_issuer_fail_derived` | derived issuer too long: `maximumSizeExceeded` | none |
| A10 | `check_resource_metadata_resource` | `check_resource_metadata_resource` | never fails; `resourceCheck` | (S) |
| A10 | same | `check_resource_metadata_resource_fail` | without (S): `maximumSizeExceeded` | none |
| A10 | `is_resource_identifier_valid` | `is_resource_identifier_valid` | never fails; `isResourceIdentifierValid` (H13) | none |
| law | A07 | `knownDefaultPort_eq_defaultPort` | the readable default-port table is the trusted one | none |
| law | A07 | `urlScheme_eq_of_isSameOrigin` | same origin implies the same scheme | none |
| law | A05 | `isDisallowedHost_domain` | a domain is rejected iff its normalized name is | none |
| law | A05 | `isDisallowedHost_iff_addressClass_ne_public` | a literal is rejected iff its class is not `Public` | none |
| law | A05 | `isLocalhostName_eq_false_of_isCloudMetadataName` | a cloud name (three names, H16) is no `localhost` name | none |
| law | A06 | `addressClass_eq_loopback_of_isLoopbackHost` | a loopback literal has class `Loopback` | none |
| law | A06 | `isHttpUrl_of_isAllowedMetadataUrl` | an allowed URL is HTTP(S) with a host | none |
| law | A06 | `isAllowedMetadataUrl_eq_false_of_isCloudMetadataName` | a cloud-metadata name: `false` | none |
| law | A06 | `isAllowedMetadataUrl_eq_false_of_addressClass_eq_blocked` | a `Blocked` literal: `false` | none |
| law | A06 | `isAllowedMetadataUrl_eq_of_addressClass_eq_private` | a `Private` literal: HTTP(S) and `allowPrivate` (H10) | none |
| law | A06 | `isAllowedMetadataUrl_eq_of_addressClass_eq_loopback` | a `Loopback` literal: HTTP(S), loopback base and `127/8`/`::1` | none |
| law | A06 | `isAllowedMetadataUrl_eq_of_isLocalhostName` | a `localhost` name: HTTP(S) and loopback base | none |
| law | A06 | `isAllowedMetadataUrl_eq_of_isDisallowedHost_eq_false` | any other host: HTTP(S) | none |
| law | A06 | `allowsHost_of_isAllowedMetadataUrl` | A06 is never looser than the resolver's host-level check (meaningful for IP-literal targets; H12) | none |
| law | A06 | `allowsHost_literalIp_self` | the resolver allows the base URL's own literal, also a `Blocked` one (H14) | none |
| law | A07 | `External.trimWhitespace_utf8Bytes` | the byte model of `trim` is the char-level trim (in `Proofs.Internal.External`) | none |
| law | A08 | `utf8Bytes_stringOfUtf8` | `stringOfUtf8` inverts `utf8Bytes` on UTF-8 | none |
| law | A08 | `responseIssuerCheck_some_some_eq_ok_iff` | RFC 9207: `Ok` iff byte-identical | none |
| law | A09 | `issuerPath_oauthWellKnown`, `issuerPath_oidcWellKnown` | the bare well-known paths give the empty issuer path | none |
| law | A09 | `issuerPath_oauthWellKnown_append` | RFC 8414 §3.1 path insertion is inverted | none |
| law | A09 | `issuerPath_oidcWellKnown_append` | OIDC path insertion is inverted | none |
| law | A09 | `issuerPath_append_oidcWellKnown` | OIDC path appending is inverted | (P) |
| law | A09 | `issuersMatch_self`, `issuersMatch_comm` | reflexive, symmetric | none |
| law | A09 | `eq_or_eq_append_slash_of_issuersMatch` | matching issuers differ at most by the `/` of a root URL (H15) | none |
| law | A10 | `pathCovers_self`, `prefix_of_pathCovers` | a path covers itself; a covering path is a prefix | none |
| law | A10 | `pathCovers_append_slash_append` | an ancestor at a segment boundary covers (H13) | none |
| law | A10 | `pathCovers_append_slash_eq_false` | the path with a final `/` added does not cover (RFC 9728 §3.3; not H13) | none |
| law | A10 | `isResourceIdentifierValid_self` | a URL is a valid identifier of itself | none |
| A06 | `is_allowed_metadata_url` | `is_allowed_metadata_url_eq_false_of_isCloudMetadataName` | a cloud-metadata name is never allowed | (B) |
| A06 | same | `is_allowed_metadata_url_eq_false_of_addressClass_eq_blocked` | a `Blocked` literal is never allowed (H14: the resolver allows the base's own) | (B) |
| A06 | same | `is_allowed_metadata_url_eq_of_addressClass_eq_private` | a `Private` literal: only with `allow_private` (H10) | (B) |
| A06 | same | `is_allowed_metadata_url_eq_of_addressClass_eq_loopback` | a `Loopback` literal: only `127/8`/`::1` from a loopback base | (B) |
| A06 | same | `is_allowed_metadata_url_eq_of_isLocalhostName` | a `localhost` name: only from a loopback base | (T), (B) |
| A06 | same | `is_allowed_metadata_url_eq_of_isDisallowedHost_eq_false` | other hosts: iff HTTP(S) | (T) |
| A07 | `resolve_resource_metadata_url` | `metadataCandidate_eq_of_resolve_resource_metadata_url_eq_ok_some` | on success: the candidate | none |
| A07 | same | `isHttpUrl_of_resolve_resource_metadata_url_eq_ok_some` | on success: HTTP(S) with a host | none |
| A07 | same | `isSameOrigin_or_isAllowedMetadataUrl_of_resolve_resource_metadata_url_eq_ok_some` | on success: same origin or allowed by A06 | none |
| A07 | same | `urlScheme_eq_https_of_resolve_resource_metadata_url_eq_ok_some` | on success: no `https` downgrade | `https` base |
| A07 | same | `allow_private_eq_true_of_resolve_resource_metadata_url_eq_ok_some` | on success, cross-origin `Private` literal: `allow_private` (H10) | none |
| A07 | same | `isLoopbackHost_of_resolve_resource_metadata_url_eq_ok_some` | on success, cross-origin `Loopback` literal: loopback base, `127/8`/`::1` | none |
| A07 | same | `resolve_resource_metadata_url_eq_some_of_isSameOrigin` | a same-origin HTTP(S) candidate is accepted | none |
| A07 | same | `resolve_resource_metadata_url_eq_none_of_addressClass_eq_blocked` | a cross-origin `Blocked` literal is refused | (H), (B) |
| A07 | same | `resolve_resource_metadata_url_eq_none_of_isCloudMetadataName` | a cross-origin cloud name is refused | (H), (B) |
| A08 | `check_authorization_response_issuer` | `check_authorization_response_issuer_eq_ok_iff` | recorded and received: `Ok` iff byte-identical | (S), (R) |
| A09 | `check_authorization_metadata_issuer` | `check_authorization_metadata_issuer_spec_none` | no explicit issuer: the derived one | (S), (D), (AD7) |
| A09 | same | `check_authorization_metadata_issuer_eq_mismatch` | a mismatch is `AuthorizationServerMismatch` with both | (U), (S), (D), (AD7) |
| A09 | same | `eq_or_eq_append_slash_of_check_authorization_metadata_issuer_eq_ok` | on success with an issuer: equal up to a root `/` (H15) | none |
| A10 | `check_resource_metadata_resource` | `check_resource_metadata_resource_eq_ok_iff` | `Ok` iff a URL without fragment, valid for the base (H13) | (S) |

Keys. (U) a `&str` argument (or the `&str` a `Host<&str>`/`Option<&str>` argument carries) is UTF-8,
`ExtModel.IsUtf8` (rule (ii)(a)); (U') the same, only when the two issuers differ (exact,
`issuer_identifiers_match_fail`); (T) if the target is HTTP(S) with a host, its domain is UTF-8
(`HostUtf8`, rule (ii)(b)); (B) the base URL's domain is UTF-8 (`HostUtf8`, rule (ii)(b)); (C) the
domain of the candidate URL is UTF-8 (`HostUtf8`, rule (ii)(b)); (S) a `String` argument field has
at most `Usize.max` bytes (every Rust `String`); (R) if an issuer is recorded, a received issuer is
UTF-8 (rule (ii)(a), weakest: needed only for the mismatch payload); (D) a derived issuer has at
most `Usize.max` bytes (a fact about the opaque `ExtModel.issuerUrl`, true of every Rust `String`);
(H) the base URL's scheme is `http` or `https` (human decision AD8; documented premise, the model of
`Url::join` does not need it); (AD7) without an explicit expected issuer, the discovery URL's
serialization has at most `u32::MAX` bytes (`DiscoveryUrlFits`, human decision AD7; documented
premise, the model of `prim::issuer_url` does not need it); (P) the path `p ++ oidcWellKnown` does
not start with one of the two path-insertion prefixes (`oauthWellKnown ++ [slashByte]`,
`oidcWellKnown ++ [slashByte]`), where the earlier branches of upstream lines 2752–2757 take
precedence.

What the premises restrict. (U), (U'), (T), (B), (C), (S), (R) and (D) hold for every value Rust
can pass (they are invariants of `&str`, `String` and `url::Url`). (H) and (AD7) are domain
restrictions: they exclude inputs on which Rust panics although the model returns a value
(human decisions AD8, AD7). They apply only to the statements that promise no failure; the "on
success" statements take neither. (P) is a premise of a law about the model, not about Rust
values. "On success" rows cover only successful calls (`… = ok r`) and do not show that a call
succeeds.

**Documented premises.** (AD7) `h_fits` of `expected_issuer_for_authorization_metadata_url`
and `h_discovery` of `check_authorization_metadata_issuer`, `…_spec_none` and `…_eq_mismatch`,
and (H) `h_scheme` of `resolve_resource_metadata_url` and of the other A07 statements that promise
no failure, are not needed by the models; the proofs consume them with `have _ := …`, so the
statement text is the signed-off one.

**Recorded bugs** (human decision 2026-11-27: the statements describe the code exactly; details
at the definitions of `Defs.AuthMetadata` and in the docstrings below):
- H9: a recorded issue in the A09 issuer check, under private disclosure; details withheld until
  it is reported. Two signed-off statements about H9 are withheld from this public version until
  H9 is reported.
- H10: with `allow_private`, the cloud-metadata endpoints in private ranges
  (`100.100.100.200`, `fd00:ec2::254`) are allowed;
  `isAllowedMetadataUrl_eq_of_addressClass_eq_private`,
  `allow_private_eq_true_of_resolve_resource_metadata_url_eq_ok_some`. The resolver does the
  same: whenever it grants `Private`, with `allowing_private_addresses` (N06) or from a
  `Private`-literal base (N04), it accepts DNS answers in these ranges (scratch probe on the
  patched copy, 2026-11-27).
- H11: `100::/64`, `192.0.0.192` and the IPv4-translated range `::ffff:0:0:0/96` (RFC 2765
  §2.1) are `Public` and allowed. The IPv4-mapped range `::ffff:0:0/96` is decided by its
  embedded IPv4 address (A01); the gap is the IPv4-translated range `::ffff:0:0:0/96` (e.g.
  `::ffff:0:a9fe:a9fe`), which carries no A01 embedding.
  `isDisallowedHost_iff_addressClass_ne_public` with the kernel-checked cases of
  `Proofs.Defs.AuthMetadata`. The resolver also accepts DNS answers in these ranges (class
  `Public`; scratch probe on the patched copy, 2026-11-27).
- H12: the bug is that A06 refuses targets that the resolver policy (N04/N07) accepts (false
  refusals): some IP literals, and a localhost name from a base that is an IPv6 embedding of
  `127/8`. For IP-literal targets A06 is never looser (`allowsHost_of_isAllowedMetadataUrl`).
  Context, not the reason: the doc of `AuthorizationManager::new` (upstream lines 1502–1510)
  gives only a necessary condition, so these refusals do not contradict it. The cases are listed
  once, in the module docstring of `Proofs.Defs.AuthMetadata`.
- H13: the resource check accepts an ancestor path, a different query and different user
  information; `pathCovers_append_slash_append`, `check_resource_metadata_resource_eq_ok_iff`.
  (Its rejection of the base path with a final `/` added, `pathCovers_append_slash_eq_false`,
  agrees with RFC 9728 §3.3 and is not part of H13.)
- H14: the resolver (N07) allows the base URL's own IP literal also when its class is `Blocked`
  (base `http://169.254.1.1:8080`, target `http://169.254.1.1:9090/`); A06 refuses it. Details
  in the module docstring of `Proofs.Defs.AuthMetadata`. `allowsHost_literalIp_self` with
  `isAllowedMetadataUrl_eq_false_of_addressClass_eq_blocked`.
- H15: `issuer_identifiers_match`, hence A09, tolerates a final `/` after a root URL, deviating
  from the "identical" of RFC 8414 §3.3; the upstream test
  `authorization_metadata_allows_only_root_trailing_slash_equivalence` (upstream lines
  5141–5151) asserts it. The `/` removed may be the last byte of a query or a fragment
  (`https://as.example?x/` matches `https://as.example?x`; scratch probe on the patched copy,
  2026-11-27). `eq_or_eq_append_slash_of_issuersMatch`,
  `eq_or_eq_append_slash_of_check_authorization_metadata_issuer_eq_ok`.
- H16: the cloud-metadata host-name list has only three names (upstream lines 39–43); for
  example `instance-data` and `metadata.goog` are not on it and A06 allows them as any public
  domain (`isAllowedMetadataUrl_eq_of_isDisallowedHost_eq_false`; kernel-checked in
  `Proofs.Defs.AuthMetadata`). With a custom HTTP client (`with_client`, upstream lines
  1696–1698) or through a proxy (`metadata_resolver.rs` lines 10–11), this name check is
  the only guard for a domain target.

**Translated configuration** (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
`--no-default-features` with the features of Phase 2 (plan Section 15), `overflow-checks=true`,
`debug-assertions=true`, through translation patch 06 (`formal/trusted/patches/
06-auth-metadata.patch`). Aeneas `nightly-2026.11.24-fb44cb4`. "upstream" line numbers refer to
`auth.rs` at `7caec76` (unmodified in the repository); "patched" to the copy with patches 01–06
(blob `dad471b`).

**Definitions used:** `Defs.AuthMetadata` (`proofs/Proofs/Defs/AuthMetadata.lean`), on
`Defs.MetadataResolver` (N01, N04, N07, N11), `Defs.Net` (A01–A03) and `Defs.utf8Bytes`.
External models: section "`auth.rs` OAuth metadata URL and issuer checks" of
`trusted/Rmcp/FunsExternal.lean` (opaque `urlScheme`, `urlPath`, `urlFragment`, `urlPort`,
`urlSerialization`, `urlJoin`, `issuerUrl`; exact `trim`, `strip_suffix`, `strip_dir_prefix`,
`trim_start_slashes`, `starts_with`, `eq_ignore_ascii_case`, `port_or_known_default`, `Url`
equality), the patch-05 `url` models (`urlParse`, `urlHost`, `urlHostStr`, `trim_end_dots`,
`ends_with`) and the string models. No statement assumes a law about an opaque `url` value; the
only facts about them are the premises (B), (C), (T), (D), (AD7), (H) above.

**Unverified glue** (AD1): the `validate_*` wrappers (`map_err(IssuerError::into_auth_error)`,
the reads of `self.allow_missing_issuer` and `self.base_url`), `IssuerError::into_auth_error`,
the bodies of the `auth::prim` functions (modelled), the tracing events (`ok ()`, stated
exception (3)).

Each statement is restated as a theorem proved by the theorem of the same name (with `_spec`
for the spec theorems) in `Proofs/Transport/AuthMetadata.lean` (namespaces
`rmcp.transport.auth.AuthorizationManager` and, for the laws, `Defs.AuthMetadata`), and followed
by the assumptions its proof depends on, checked by `#print axioms` under `#guard_msgs`. Signed
off by the human spec owner on 2026-11-27 (six spec-cycle rounds). The statement text is the
signed-off text, with one difference of form: the translated functions are written with their
full names `rmcp.transport.auth.AuthorizationManager.…` (inside
`theorem Theorems.auth.AuthorizationManager.…` a short name would resolve to the restated theorem
of that name), and some long lines are wrapped differently; each restated type was checked equal,
as a kernel term, to the signed-off one.
-/

open Aeneas Aeneas.Std Result
open rmcp
open Defs (utf8Bytes)
open Defs.AuthMetadata Defs.MetadataResolver Defs.Net
open rmcp.transport.auth.metadata_resolver (AddressClass)
open rmcp.transport.auth (IssuerError StoredAuthorizationState AuthorizationMetadata
  ResourceServerMetadata ProtectedResourceMetadataInvalidReason)

/-! ## A04 `is_http_url` (upstream lines 1330–1332; patched 1325–1327) -/

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::is_http_url`** (A04)

Never fails. `true` exactly when the URL's scheme is `http` or `https` and it has a host string
(`Defs.AuthMetadata.isHttpUrl`; `matches!(url.scheme(), "http" | "https") &&
url.host_str().is_some()`). No premise. -/
theorem Theorems.auth.AuthorizationManager.is_http_url (target : url.Url) :
    rmcp.transport.auth.AuthorizationManager.is_http_url target ⦃ (result : Bool) =>
      result = isHttpUrl target ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.is_http_url_spec target

/--
info: 'Theorems.auth.AuthorizationManager.is_http_url' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_http_url

/-! ## `is_same_origin` (callee of A07; upstream lines 1334–1341, patched 1329–1336) -/

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::is_same_origin`** (callee of
A07)

Never fails. `true` exactly when the schemes have the same bytes, both URLs have a host string
and the two are equal up to ASCII case (`str::eq_ignore_ascii_case`), and the ports or known
default ports are equal (`Defs.AuthMetadata.isSameOrigin`). No premise. -/
theorem Theorems.auth.AuthorizationManager.is_same_origin (base candidate : url.Url) :
    rmcp.transport.auth.AuthorizationManager.is_same_origin base candidate ⦃ (result : Bool) =>
      result = isSameOrigin base candidate ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.is_same_origin_spec base candidate

/--
info: 'Theorems.auth.AuthorizationManager.is_same_origin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_same_origin

/-! ## A05 `is_disallowed_metadata_host` (upstream lines 1385–1399; patched 1380–1397) -/

/-- **Spec theorem for
`rmcp::transport::auth::AuthorizationManager::is_disallowed_metadata_hostname`** (callee of A05)

Never fails. `true` exactly when the bytes are `localhost`, end in `.localhost`, or are one of
`metadata`, `metadata.google.internal`, `metadata.azure.internal`, compared byte for byte
(`Defs.AuthMetadata.isDisallowedHostname`; upstream lines 1385–1389, the constant
`CLOUD_METADATA_HOSTS` of lines 39–43 inlined by the first hunk of patch 06, hunk H1 in the
patch header). No normalization here: the only caller passes a normalized name. No premise. -/
theorem Theorems.auth.AuthorizationManager.is_disallowed_metadata_hostname (host : Str) :
    rmcp.transport.auth.AuthorizationManager.is_disallowed_metadata_hostname host
      ⦃ (result : Bool) =>
      result = isDisallowedHostname host.val ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.is_disallowed_metadata_hostname_spec host

/--
info: 'Theorems.auth.AuthorizationManager.is_disallowed_metadata_hostname' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_disallowed_metadata_hostname

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
theorem Theorems.auth.AuthorizationManager.is_disallowed_metadata_host (host : url.host.Host Str)
    (h_utf8 : ∀ d, host = url.host.Host.Domain d → ExtModel.IsUtf8 d.val) :
    rmcp.transport.auth.AuthorizationManager.is_disallowed_metadata_host host ⦃ (result : Bool) =>
      result = isDisallowedHost host ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.is_disallowed_metadata_host_spec host h_utf8

/--
info: 'Theorems.auth.AuthorizationManager.is_disallowed_metadata_host' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_disallowed_metadata_host

/-- **`is_disallowed_metadata_host`, the UTF-8 premise is the weakest**: for a domain whose bytes
are not UTF-8 (no Rust `&str`), `to_ascii_lowercase` (upstream line 1394, patched 1392) fails,
so the call fails with `undef`. -/
theorem Theorems.auth.AuthorizationManager.is_disallowed_metadata_host_fail
    (d : Str) (h : ¬ ExtModel.IsUtf8 d.val) :
    rmcp.transport.auth.AuthorizationManager.is_disallowed_metadata_host (url.host.Host.Domain d) =
      fail .undef :=
  @rmcp.transport.auth.AuthorizationManager.is_disallowed_metadata_host_fail d h

/--
info: 'Theorems.auth.AuthorizationManager.is_disallowed_metadata_host_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_disallowed_metadata_host_fail

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
theorem Theorems.auth.AuthorizationManager.is_allowed_metadata_url
    (base_url target : url.Url) (allow_private : Bool)
    (h_base : HostUtf8 base_url) (h_target : isHttpUrl target = true → HostUtf8 target) :
    rmcp.transport.auth.AuthorizationManager.is_allowed_metadata_url base_url target allow_private
      ⦃ (result : Bool) =>
      result = isAllowedMetadataUrl base_url target allow_private ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.is_allowed_metadata_url_spec base_url target
    allow_private h_base h_target

/--
info: 'Theorems.auth.AuthorizationManager.is_allowed_metadata_url' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_allowed_metadata_url

/-- **`is_allowed_metadata_url`, the target premise is the weakest**: for an HTTP(S) target with
a host string whose host is a domain that is not UTF-8, the guard (A05, upstream line 1421)
fails, so the call fails with `undef`. -/
theorem Theorems.auth.AuthorizationManager.is_allowed_metadata_url_fail
    (base_url target : url.Url) (allow_private : Bool) (d : Str)
    (h_http : isHttpUrl target = true)
    (h_host : ExtModel.urlHost target = some (url.host.Host.Domain d))
    (h : ¬ ExtModel.IsUtf8 d.val) :
    rmcp.transport.auth.AuthorizationManager.is_allowed_metadata_url base_url target allow_private =
      fail .undef :=
  @rmcp.transport.auth.AuthorizationManager.is_allowed_metadata_url_fail base_url target
    allow_private d h_http h_host h

/--
info: 'Theorems.auth.AuthorizationManager.is_allowed_metadata_url_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_allowed_metadata_url_fail

/-- **`is_allowed_metadata_url`, when the base premise is needed**: for an HTTP(S) target whose
host is rejected by the guard and not exempted as a `Private` literal with `allow_private`, the
base URL's host is read (upstream line 1434, `is_loopback_metadata_host` on it); if it is a
domain that is not UTF-8, the call fails with `undef`. No premise on the target's domain: if it
is not UTF-8, the guard (upstream line 1421) already fails with `undef`
(`is_allowed_metadata_url_fail`). -/
theorem Theorems.auth.AuthorizationManager.is_allowed_metadata_url_fail_base
    (base_url target : url.Url) (allow_private : Bool)
    (h : url.host.Host Str) (d : Str)
    (h_http : isHttpUrl target = true) (h_host : ExtModel.urlHost target = some h)
    (h_dis : isDisallowedHost h = true)
    (h_priv : ¬ (allow_private = true ∧ (hostIp h).map addressClass = some AddressClass.Private))
    (h_base_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (hd : ¬ ExtModel.IsUtf8 d.val) :
    rmcp.transport.auth.AuthorizationManager.is_allowed_metadata_url base_url target allow_private =
      fail .undef :=
  @rmcp.transport.auth.AuthorizationManager.is_allowed_metadata_url_fail_base base_url target
    allow_private h d h_http h_host h_dis h_priv h_base_host hd

/--
info: 'Theorems.auth.AuthorizationManager.is_allowed_metadata_url_fail_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_allowed_metadata_url_fail_base

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
theorem Theorems.auth.AuthorizationManager.is_allowed_disallowed_host
    (base_url : url.Url) (host : url.host.Host Str)
    (allow_private : Bool) (h_base : HostUtf8 base_url)
    (h_utf8 : ∀ d, host = url.host.Host.Domain d → ExtModel.IsUtf8 d.val) :
    rmcp.transport.auth.AuthorizationManager.is_allowed_disallowed_host base_url host allow_private
      ⦃ (result : Bool) =>
      result = isAllowedDisallowedHost (ExtModel.urlHost base_url) host allow_private ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.is_allowed_disallowed_host_spec base_url host
    allow_private h_base h_utf8

/--
info: 'Theorems.auth.AuthorizationManager.is_allowed_disallowed_host' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_allowed_disallowed_host

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
theorem Theorems.auth.AuthorizationManager.resolve_resource_metadata_url
    (value : Str) (base_url : url.Url)
    (allow_private : Bool) (h_scheme : isHttpScheme (ExtModel.urlScheme base_url).val = true)
    (h_base : HostUtf8 base_url)
    (h_candidate : ∀ u, metadataCandidate value.val base_url = some u → HostUtf8 u) :
    rmcp.transport.auth.AuthorizationManager.resolve_resource_metadata_url value base_url
      allow_private
      ⦃ (result : Option url.Url) =>
      result = resolveResourceMetadataUrl value.val base_url allow_private ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.resolve_resource_metadata_url_spec value base_url
    allow_private h_scheme h_base h_candidate

/--
info: 'Theorems.auth.AuthorizationManager.resolve_resource_metadata_url' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.resolve_resource_metadata_url

/-- **`resolve_resource_metadata_url`, when the candidate premise is needed**: for a candidate
that is HTTP(S) with a host string, not same-origin with the base URL, not a downgrade from
`https`, and whose host is a domain that is not UTF-8, A06 (upstream line 1465) fails, so the
call fails with `undef`. -/
theorem Theorems.auth.AuthorizationManager.resolve_resource_metadata_url_fail
    (value : Str) (base_url : url.Url)
    (allow_private : Bool) (u : url.Url) (d : Str)
    (h_candidate : metadataCandidate value.val base_url = some u)
    (h_http : isHttpUrl u = true) (h_origin : isSameOrigin base_url u = false)
    (h_downgrade : ¬ ((ExtModel.urlScheme base_url).val = utf8Bytes "https" ∧
      (ExtModel.urlScheme u).val ≠ utf8Bytes "https"))
    (h_host : ExtModel.urlHost u = some (url.host.Host.Domain d))
    (h : ¬ ExtModel.IsUtf8 d.val) :
    rmcp.transport.auth.AuthorizationManager.resolve_resource_metadata_url value base_url
      allow_private = fail .undef :=
  @rmcp.transport.auth.AuthorizationManager.resolve_resource_metadata_url_fail value base_url
    allow_private u d h_candidate h_http h_origin h_downgrade h_host h

/--
info: 'Theorems.auth.AuthorizationManager.resolve_resource_metadata_url_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.resolve_resource_metadata_url_fail

/-- **`resolve_resource_metadata_url`, when the base premise is needed**: for a candidate that is
HTTP(S) with a host string, not same-origin with the base URL and not a downgrade from `https`,
whose host the guard rejects and that is not exempted as a `Private` literal with
`allow_private`, A06 (upstream line 1465) reads the base URL's host (upstream line 1434); if it
is a domain that is not UTF-8, the call fails with `undef` (`is_allowed_metadata_url_fail_base`).
The same-origin check (upstream line 1458) reads only the host strings and does not fail. -/
theorem Theorems.auth.AuthorizationManager.resolve_resource_metadata_url_fail_base
    (value : Str) (base_url : url.Url)
    (allow_private : Bool) (u : url.Url) (h : url.host.Host Str) (d : Str)
    (h_candidate : metadataCandidate value.val base_url = some u)
    (h_http : isHttpUrl u = true) (h_origin : isSameOrigin base_url u = false)
    (h_downgrade : ¬ ((ExtModel.urlScheme base_url).val = utf8Bytes "https" ∧
      (ExtModel.urlScheme u).val ≠ utf8Bytes "https"))
    (h_host : ExtModel.urlHost u = some h) (h_dis : isDisallowedHost h = true)
    (h_priv : ¬ (allow_private = true ∧ (hostIp h).map addressClass = some AddressClass.Private))
    (h_base_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (hd : ¬ ExtModel.IsUtf8 d.val) :
    rmcp.transport.auth.AuthorizationManager.resolve_resource_metadata_url value base_url
      allow_private = fail .undef :=
  @rmcp.transport.auth.AuthorizationManager.resolve_resource_metadata_url_fail_base value base_url
    allow_private u h d h_candidate h_http h_origin h_downgrade h_host h_dis h_priv h_base_host hd

/--
info: 'Theorems.auth.AuthorizationManager.resolve_resource_metadata_url_fail_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.resolve_resource_metadata_url_fail_base

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
theorem Theorems.auth.AuthorizationManager.check_authorization_response_issuer
    (stored_state : StoredAuthorizationState)
    (received_issuer : Option Str)
    (h_fits : ∀ e, stored_state.expected_issuer = some e → e.utf8ByteSize ≤ Usize.max)
    (h_utf8 : ∀ e r, stored_state.expected_issuer = some e → received_issuer = some r →
      ExtModel.IsUtf8 r.val) :
    rmcp.transport.auth.AuthorizationManager.check_authorization_response_issuer stored_state
      received_issuer
      ⦃ (result : core.result.Result Unit IssuerError) =>
      result = responseIssuerCheck stored_state.expected_issuer stored_state.require_issuer
        (received_issuer.map (·.val)) ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.check_authorization_response_issuer_spec stored_state
    received_issuer h_fits h_utf8

/--
info: 'Theorems.auth.AuthorizationManager.check_authorization_response_issuer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.check_authorization_response_issuer

/-- **`check_authorization_response_issuer`, the size premise is exact for the Lean models**: a
recorded issuer of more than `Usize.max` bytes (no Rust `String`) fails `as_deref` (upstream line
2324) with `maximumSizeExceeded`. -/
theorem Theorems.auth.AuthorizationManager.check_authorization_response_issuer_fail
    (stored_state : StoredAuthorizationState)
    (received_issuer : Option Str) (e : String)
    (h_expected : stored_state.expected_issuer = some e) (h : ¬ e.utf8ByteSize ≤ Usize.max) :
    rmcp.transport.auth.AuthorizationManager.check_authorization_response_issuer stored_state
      received_issuer =
      fail .maximumSizeExceeded :=
  @rmcp.transport.auth.AuthorizationManager.check_authorization_response_issuer_fail stored_state
    received_issuer e h_expected h

/--
info: 'Theorems.auth.AuthorizationManager.check_authorization_response_issuer_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.check_authorization_response_issuer_fail

/-- **`check_authorization_response_issuer`, the UTF-8 premise is the weakest**: with a recorded
issuer that fits and a received issuer that is not UTF-8 (hence different from it), the
`to_owned` of the received issuer for the mismatch payload (upstream line 2349, patched 2371)
fails with `undef`. -/
theorem Theorems.auth.AuthorizationManager.check_authorization_response_issuer_fail_undef
    (stored_state : StoredAuthorizationState)
    (e : String) (r : Str) (h_expected : stored_state.expected_issuer = some e)
    (h_fits : e.utf8ByteSize ≤ Usize.max) (h : ¬ ExtModel.IsUtf8 r.val) :
    rmcp.transport.auth.AuthorizationManager.check_authorization_response_issuer stored_state (some
      r) = fail .undef :=
  @rmcp.transport.auth.AuthorizationManager.check_authorization_response_issuer_fail_undef
    stored_state e r h_expected h_fits h

/--
info: 'Theorems.auth.AuthorizationManager.check_authorization_response_issuer_fail_undef' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.check_authorization_response_issuer_fail_undef

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
theorem Theorems.auth.AuthorizationManager.expected_issuer_for_authorization_metadata_url
    (discovery_url : url.Url)
    (h_fits : DiscoveryUrlFits discovery_url) :
    rmcp.transport.auth.AuthorizationManager.expected_issuer_for_authorization_metadata_url
      discovery_url
      ⦃ (result : Option String) =>
      result = derivedIssuer discovery_url ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.expected_issuer_for_authorization_metadata_url_spec
    discovery_url h_fits

/--
info: 'Theorems.auth.AuthorizationManager.expected_issuer_for_authorization_metadata_url' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.expected_issuer_for_authorization_metadata_url

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
theorem Theorems.auth.AuthorizationManager.issuer_identifiers_match
    (received_issuer expected_issuer : Str)
    (h_utf8 : received_issuer.val ≠ expected_issuer.val →
      ExtModel.IsUtf8 received_issuer.val ∧ ExtModel.IsUtf8 expected_issuer.val) :
    rmcp.transport.auth.AuthorizationManager.issuer_identifiers_match received_issuer
      expected_issuer ⦃ (result : Bool) =>
      result = issuersMatch received_issuer.val expected_issuer.val ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.issuer_identifiers_match_spec received_issuer
    expected_issuer h_utf8

/--
info: 'Theorems.auth.AuthorizationManager.issuer_identifiers_match' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.issuer_identifiers_match

/-- **`issuer_identifiers_match`, the UTF-8 premise (U') is exact**: if the two issuers are not
byte-equal (the check of patched line 2791, upstream line 2777, does not return) and one of them
is not UTF-8, the comparison of patched line 2795 (upstream line 2793) calls `trim_root_slash` on
the received issuer, then on the expected one, and the first that is not UTF-8 fails with
`undef` in its `to_owned` (patched lines 2802 and 2804; `trim_root_slash_fail`). -/
theorem Theorems.auth.AuthorizationManager.issuer_identifiers_match_fail
    (received_issuer expected_issuer : Str)
    (h_ne : received_issuer.val ≠ expected_issuer.val)
    (h : ¬ (ExtModel.IsUtf8 received_issuer.val ∧ ExtModel.IsUtf8 expected_issuer.val)) :
    rmcp.transport.auth.AuthorizationManager.issuer_identifiers_match received_issuer
      expected_issuer = fail .undef :=
  @rmcp.transport.auth.AuthorizationManager.issuer_identifiers_match_fail received_issuer
    expected_issuer h_ne h

/--
info: 'Theorems.auth.AuthorizationManager.issuer_identifiers_match_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.issuer_identifiers_match_fail

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::trim_root_slash`** (patch
helper of A09; patched lines 2798–2805, the closure of upstream lines 2781–2791)

For a UTF-8 issuer (rule (ii)(a)), never fails: the issuer without its final `/` if what remains
parses as a URL whose path is empty or `/` (query and fragment allowed), otherwise unchanged
(`Defs.AuthMetadata.trimRootSlash`), as bytes. The premise is the weakest
(`trim_root_slash_fail`). -/
theorem Theorems.auth.AuthorizationManager.trim_root_slash
    (issuer : Str) (h_utf8 : ExtModel.IsUtf8 issuer.val) :
    rmcp.transport.auth.AuthorizationManager.trim_root_slash issuer ⦃ (result : String) =>
      utf8Bytes result = trimRootSlash issuer.val ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.trim_root_slash_spec issuer h_utf8

/--
info: 'Theorems.auth.AuthorizationManager.trim_root_slash' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.trim_root_slash

/-- **`trim_root_slash`, the UTF-8 premise is the weakest**: for bytes that are not UTF-8,
`to_owned` (patched lines 2802 and 2804) fails with `undef` on both branches (removing a final
`/` does not make bytes UTF-8). -/
theorem Theorems.auth.AuthorizationManager.trim_root_slash_fail
    (issuer : Str) (h : ¬ ExtModel.IsUtf8 issuer.val) :
    rmcp.transport.auth.AuthorizationManager.trim_root_slash issuer = fail .undef :=
  @rmcp.transport.auth.AuthorizationManager.trim_root_slash_fail issuer h

/--
info: 'Theorems.auth.AuthorizationManager.trim_root_slash_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.trim_root_slash_fail

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::is_root_url`** (patch
helper of A09; patched lines 2807–2812, the `filter` closure of upstream lines 2784–2788)

Never fails. `true` exactly when the bytes parse as a URL whose path is empty or `/` (query and
fragment allowed) (`Defs.AuthMetadata.isRootUrl`). No premise. -/
theorem Theorems.auth.AuthorizationManager.is_root_url (value : Str) :
    rmcp.transport.auth.AuthorizationManager.is_root_url value ⦃ (result : Bool) =>
      result = isRootUrl value.val ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.is_root_url_spec value

/--
info: 'Theorems.auth.AuthorizationManager.is_root_url' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_root_url

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
theorem Theorems.auth.AuthorizationManager.check_authorization_metadata_issuer
    (allow_missing_issuer : Bool)
    (discovery_url : url.Url) (expected_issuer : Option Str) (metadata : AuthorizationMetadata)
    (h_utf8 : ∀ s, expected_issuer = some s → ExtModel.IsUtf8 s.val)
    (h_received : ∀ r, metadata.issuer = some r → r.utf8ByteSize ≤ Usize.max)
    (h_derived : expected_issuer = none →
      ∀ e, derivedIssuer discovery_url = some e → e.utf8ByteSize ≤ Usize.max)
    (h_discovery : expected_issuer = none → DiscoveryUrlFits discovery_url) :
    rmcp.transport.auth.AuthorizationManager.check_authorization_metadata_issuer
      allow_missing_issuer discovery_url expected_issuer
      metadata ⦃ (result : core.result.Result Unit IssuerError) =>
      result = metadataIssuerCheck allow_missing_issuer
        (expectedIssuerOf (expected_issuer.map (·.val)) discovery_url) metadata.issuer ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.check_authorization_metadata_issuer_spec
    allow_missing_issuer discovery_url expected_issuer metadata h_utf8 h_received h_derived
      h_discovery

/--
info: 'Theorems.auth.AuthorizationManager.check_authorization_metadata_issuer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.check_authorization_metadata_issuer

/-- **`check_authorization_metadata_issuer`, the UTF-8 premise is the weakest**: an explicit
expected issuer that is not UTF-8 fails `to_owned` (patched line 2836, upstream 2803) with
`undef`. -/
theorem Theorems.auth.AuthorizationManager.check_authorization_metadata_issuer_fail
    (allow_missing_issuer : Bool)
    (discovery_url : url.Url) (s : Str) (metadata : AuthorizationMetadata)
    (h : ¬ ExtModel.IsUtf8 s.val) :
    rmcp.transport.auth.AuthorizationManager.check_authorization_metadata_issuer
      allow_missing_issuer discovery_url (some s) metadata =
      fail .undef :=
  @rmcp.transport.auth.AuthorizationManager.check_authorization_metadata_issuer_fail
    allow_missing_issuer discovery_url s metadata h

/--
info: 'Theorems.auth.AuthorizationManager.check_authorization_metadata_issuer_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.check_authorization_metadata_issuer_fail

/-- **`check_authorization_metadata_issuer`, when the size premise on the received issuer is
needed**: with an expected issuer (here an explicit UTF-8 one), a metadata `issuer` of
more than `Usize.max` bytes (no Rust `String`) fails `as_deref` (patched line 2842, upstream
2808) with `maximumSizeExceeded`. -/
theorem Theorems.auth.AuthorizationManager.check_authorization_metadata_issuer_fail_size
    (allow_missing_issuer : Bool)
    (discovery_url : url.Url) (s : Str) (metadata : AuthorizationMetadata) (r : String)
    (h_utf8 : ExtModel.IsUtf8 s.val) (h_issuer : metadata.issuer = some r)
    (h : ¬ r.utf8ByteSize ≤ Usize.max) :
    rmcp.transport.auth.AuthorizationManager.check_authorization_metadata_issuer
      allow_missing_issuer discovery_url (some s) metadata =
      fail .maximumSizeExceeded :=
  @rmcp.transport.auth.AuthorizationManager.check_authorization_metadata_issuer_fail_size
    allow_missing_issuer discovery_url s metadata r h_utf8 h_issuer h

/--
info: 'Theorems.auth.AuthorizationManager.check_authorization_metadata_issuer_fail_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.check_authorization_metadata_issuer_fail_size

/-- **`check_authorization_metadata_issuer`, when the size premise on the derived issuer is
needed**: without an explicit expected issuer, a derived issuer of more than `Usize.max`
bytes (no Rust `String`) fails its `deref` (patched line 2848, `&expected_issuer`; upstream
2814) with `maximumSizeExceeded` when the metadata names an `issuer` (if that `issuer` is too
long as well, its `as_deref`, patched line 2842, fails first, with the same error). No premise:
the model of `prim::issuer_url` does not fail, so the AD7 premise plays no role here. -/
theorem Theorems.auth.AuthorizationManager.check_authorization_metadata_issuer_fail_derived
    (allow_missing_issuer : Bool)
    (discovery_url : url.Url) (metadata : AuthorizationMetadata) (e r : String)
    (h_derived : derivedIssuer discovery_url = some e) (h : ¬ e.utf8ByteSize ≤ Usize.max)
    (h_issuer : metadata.issuer = some r) :
    rmcp.transport.auth.AuthorizationManager.check_authorization_metadata_issuer
      allow_missing_issuer discovery_url none metadata =
      fail .maximumSizeExceeded :=
  @rmcp.transport.auth.AuthorizationManager.check_authorization_metadata_issuer_fail_derived
    allow_missing_issuer discovery_url metadata e r h_derived h h_issuer

/--
info: 'Theorems.auth.AuthorizationManager.check_authorization_metadata_issuer_fail_derived' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.check_authorization_metadata_issuer_fail_derived

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
theorem Theorems.auth.AuthorizationManager.check_resource_metadata_resource (base_url : url.Url)
    (metadata : ResourceServerMetadata)
    (h_fits : ∀ r, metadata.resource = some r → r.utf8ByteSize ≤ Usize.max) :
    rmcp.transport.auth.AuthorizationManager.check_resource_metadata_resource base_url metadata
      ⦃ (result : core.result.Result Unit ProtectedResourceMetadataInvalidReason) =>
      result = resourceCheck base_url metadata.resource ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.check_resource_metadata_resource_spec base_url metadata
    h_fits

/--
info: 'Theorems.auth.AuthorizationManager.check_resource_metadata_resource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.check_resource_metadata_resource

/-- **`check_resource_metadata_resource`, the size premise is exact for the Lean models**: a
resource of more than `Usize.max` bytes (no Rust `String`) fails `as_deref` (upstream line 2964)
with `maximumSizeExceeded`. -/
theorem Theorems.auth.AuthorizationManager.check_resource_metadata_resource_fail
    (base_url : url.Url)
    (metadata : ResourceServerMetadata) (r : String) (h_resource : metadata.resource = some r)
    (h : ¬ r.utf8ByteSize ≤ Usize.max) :
    rmcp.transport.auth.AuthorizationManager.check_resource_metadata_resource base_url metadata =
      fail .maximumSizeExceeded :=
  @rmcp.transport.auth.AuthorizationManager.check_resource_metadata_resource_fail base_url metadata
    r h_resource h

/--
info: 'Theorems.auth.AuthorizationManager.check_resource_metadata_resource_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.check_resource_metadata_resource_fail

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
theorem Theorems.auth.AuthorizationManager.is_resource_identifier_valid (expected actual : url.Url)
    :
    rmcp.transport.auth.AuthorizationManager.is_resource_identifier_valid expected actual
      ⦃ (result : Bool) =>
      result = isResourceIdentifierValid expected actual ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.is_resource_identifier_valid_spec expected actual

/--
info: 'Theorems.auth.AuthorizationManager.is_resource_identifier_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_resource_identifier_valid

/-! ## Laws of `Defs.AuthMetadata` -/

/-- **`is_same_origin`, the readable default-port table is the trusted one**: `knownDefaultPort`
(`url-2.5.9/src/parser.rs` lines 185–192) is the function `ExtModel.defaultPort` on which the
model of `Url::port_or_known_default` is built, so `portOrKnownDefault u` is the value that model
returns. -/
theorem Theorems.auth.knownDefaultPort_eq_defaultPort : knownDefaultPort = ExtModel.defaultPort :=
  @Defs.AuthMetadata.knownDefaultPort_eq_defaultPort

/--
info: 'Theorems.auth.knownDefaultPort_eq_defaultPort' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.knownDefaultPort_eq_defaultPort

/-- **`is_same_origin`, same origin implies the same scheme** (upstream line 1335), so the
same-origin acceptance of A07 never downgrades from `https`. -/
theorem Theorems.auth.urlScheme_eq_of_isSameOrigin (base candidate : url.Url)
    (h : isSameOrigin base candidate = true) :
    (ExtModel.urlScheme base).val = (ExtModel.urlScheme candidate).val :=
  @Defs.AuthMetadata.urlScheme_eq_of_isSameOrigin base candidate h

/--
info: 'Theorems.auth.urlScheme_eq_of_isSameOrigin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.urlScheme_eq_of_isSameOrigin

/-- **A05, a domain is rejected exactly when its normalized name is** (the call of upstream lines
1393–1395: `is_disallowed_metadata_hostname` on the normalized name). -/
theorem Theorems.auth.isDisallowedHost_domain (d : Str) :
    isDisallowedHost (url.host.Host.Domain d) = isDisallowedHostname (normalizeHost d.val) :=
  @Defs.AuthMetadata.isDisallowedHost_domain d

/--
info: 'Theorems.auth.isDisallowedHost_domain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.isDisallowedHost_domain

/-- **A05 and N01, an IP literal is rejected exactly when its class is not `Public`**: the guard
(A02/A03) and the address classes of the metadata resolver agree on every IPv4 and IPv6 literal
(the loopback and private ranges lie inside the blocked lists). Which addresses are `Public` (H8
among them, and the IPv6 ranges of H11 that carry no A01 embedding, the IPv4-translated
`::ffff:0:0:0/96` and `100::/64`, and `192.0.0.192`): module docstrings of
`Proofs.Defs.MetadataResolver` and `Proofs.Defs.AuthMetadata`. -/
theorem Theorems.auth.isDisallowedHost_iff_addressClass_ne_public (h : url.host.Host Str)
    (ip : core.net.ip_addr.IpAddr) (hip : hostIp h = some ip) :
    isDisallowedHost h = true ↔ addressClass ip ≠ AddressClass.Public :=
  @Defs.AuthMetadata.isDisallowedHost_iff_addressClass_ne_public h ip hip

/--
info: 'Theorems.auth.isDisallowedHost_iff_addressClass_ne_public' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.isDisallowedHost_iff_addressClass_ne_public

/-- **A05, a cloud-metadata name is not a `localhost` name** (so the loopback exemption of A06
never applies to it). -/
theorem Theorems.auth.isLocalhostName_eq_false_of_isCloudMetadataName (d : List U8)
    (h : isCloudMetadataName d = true) : isLocalhostName d = false :=
  @Defs.AuthMetadata.isLocalhostName_eq_false_of_isCloudMetadataName d h

/--
info: 'Theorems.auth.isLocalhostName_eq_false_of_isCloudMetadataName' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.isLocalhostName_eq_false_of_isCloudMetadataName

/-- **A06, a loopback IP literal has class `Loopback`**: `127/8` and `::1` (`isLoopbackHost`) are
`Loopback` for N01; the converse fails for the IPv6 embeddings of `127/8` (such as
`::ffff:127.0.0.1`), which N01 calls `Loopback` but `Ipv6Addr::is_loopback` does not (H12). -/
theorem Theorems.auth.addressClass_eq_loopback_of_isLoopbackHost (h : url.host.Host Str)
    (ip : core.net.ip_addr.IpAddr) (hip : hostIp h = some ip) (hl : isLoopbackHost h = true) :
    addressClass ip = AddressClass.Loopback :=
  @Defs.AuthMetadata.addressClass_eq_loopback_of_isLoopbackHost h ip hip hl

/--
info: 'Theorems.auth.addressClass_eq_loopback_of_isLoopbackHost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.addressClass_eq_loopback_of_isLoopbackHost

/-- **A06, an allowed metadata URL is HTTP(S) with a host string** (A04, upstream line 1413). -/
theorem Theorems.auth.isHttpUrl_of_isAllowedMetadataUrl
    (base target : url.Url) (allowPrivate : Bool)
    (h : isAllowedMetadataUrl base target allowPrivate = true) : isHttpUrl target = true :=
  @Defs.AuthMetadata.isHttpUrl_of_isAllowedMetadataUrl base target allowPrivate h

/--
info: 'Theorems.auth.isHttpUrl_of_isAllowedMetadataUrl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.isHttpUrl_of_isAllowedMetadataUrl

/-- **A06, a cloud-metadata name is never allowed**: a target whose host is a domain that
normalizes to `metadata`, `metadata.google.internal` or `metadata.azure.internal` is refused,
whatever the base URL and `allowPrivate` (the guard rejects it, upstream lines 1388 and 1421; a
domain has no `Private` class; it is no `localhost` name). No premise. -/
theorem Theorems.auth.isAllowedMetadataUrl_eq_false_of_isCloudMetadataName (base target : url.Url)
    (allowPrivate : Bool) (d : Str)
    (h_host : ExtModel.urlHost target = some (url.host.Host.Domain d))
    (hc : isCloudMetadataName d.val = true) :
    isAllowedMetadataUrl base target allowPrivate = false :=
  @Defs.AuthMetadata.isAllowedMetadataUrl_eq_false_of_isCloudMetadataName base target allowPrivate d
    h_host hc

/--
info: 'Theorems.auth.isAllowedMetadataUrl_eq_false_of_isCloudMetadataName' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.isAllowedMetadataUrl_eq_false_of_isCloudMetadataName

/-- **A06, a `Blocked` literal is never allowed**: a target whose host is an IP literal of class
`Blocked` (link-local such as `169.254.169.254`, unspecified, broadcast, multicast, `0/8`,
`198.18/15`, Teredo, `64:ff9b:1::/48`, or an IPv6 embedding of one) is refused, whatever the
base URL and `allowPrivate`: the guard rejects it, it is not `Private` (upstream lines
1425–1432) and it is not a loopback host (line 1434). This includes the base URL's own literal,
which the resolver allows (H14, `allowsHost_literalIp_self`). No premise. -/
theorem Theorems.auth.isAllowedMetadataUrl_eq_false_of_addressClass_eq_blocked
    (base target : url.Url)
    (allowPrivate : Bool) (h : url.host.Host Str) (h_host : ExtModel.urlHost target = some h)
    (h_blocked : (hostIp h).map addressClass = some AddressClass.Blocked) :
    isAllowedMetadataUrl base target allowPrivate = false :=
  @Defs.AuthMetadata.isAllowedMetadataUrl_eq_false_of_addressClass_eq_blocked base target
    allowPrivate h h_host h_blocked

/--
info: 'Theorems.auth.isAllowedMetadataUrl_eq_false_of_addressClass_eq_blocked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.isAllowedMetadataUrl_eq_false_of_addressClass_eq_blocked

/-- **A06, a `Private` literal**: a target whose host is an IP literal of class `Private`
(`10/8`, `172.16/12`, `192.168/16`, `100.64/10`, `fc00::/7`, or an IPv6 embedding of one) is
allowed exactly when it is HTTP(S) with a host string and `allowPrivate` holds (upstream lines
1425–1432); a private base URL does not allow it by itself (unlike the resolver's
`baseClasses`, N04; H12). H10 (recorded bug): this includes the cloud-metadata endpoints
`100.100.100.200` and `fd00:ec2::254`. No premise. -/
theorem Theorems.auth.isAllowedMetadataUrl_eq_of_addressClass_eq_private (base target : url.Url)
    (allowPrivate : Bool) (h : url.host.Host Str) (h_host : ExtModel.urlHost target = some h)
    (h_private : (hostIp h).map addressClass = some AddressClass.Private) :
    isAllowedMetadataUrl base target allowPrivate = (isHttpUrl target && allowPrivate) :=
  @Defs.AuthMetadata.isAllowedMetadataUrl_eq_of_addressClass_eq_private base target allowPrivate h
    h_host h_private

/--
info: 'Theorems.auth.isAllowedMetadataUrl_eq_of_addressClass_eq_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.isAllowedMetadataUrl_eq_of_addressClass_eq_private

/-- **A06, a `Loopback` literal**: a target whose host is an IP literal of class `Loopback` is
allowed exactly when it is HTTP(S) with a host string, the base URL's host is a loopback host and
the target's host is one (`127/8` or `::1`; an IPv6 embedding of `127/8`, class `Loopback`, is
therefore never allowed, H12) (upstream lines 1434–1435); `allowPrivate` plays no role. No
premise. -/
theorem Theorems.auth.isAllowedMetadataUrl_eq_of_addressClass_eq_loopback (base target : url.Url)
    (allowPrivate : Bool) (h : url.host.Host Str) (h_host : ExtModel.urlHost target = some h)
    (h_loopback : (hostIp h).map addressClass = some AddressClass.Loopback) :
    isAllowedMetadataUrl base target allowPrivate =
      (isHttpUrl target && (ExtModel.urlHost base).any isLoopbackHost && isLoopbackHost h) :=
  @Defs.AuthMetadata.isAllowedMetadataUrl_eq_of_addressClass_eq_loopback base target allowPrivate h
    h_host h_loopback

/--
info: 'Theorems.auth.isAllowedMetadataUrl_eq_of_addressClass_eq_loopback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.isAllowedMetadataUrl_eq_of_addressClass_eq_loopback

/-- **A06, a `localhost` name**: a target whose host is `localhost` or a `.localhost` name (after
normalization) is allowed exactly when it is HTTP(S) with a host string and the base URL's host
is a loopback host (upstream lines 1434–1435). No premise. -/
theorem Theorems.auth.isAllowedMetadataUrl_eq_of_isLocalhostName
    (base target : url.Url) (allowPrivate : Bool)
    (d : Str) (h_host : ExtModel.urlHost target = some (url.host.Host.Domain d))
    (h_local : isLocalhostName d.val = true) :
    isAllowedMetadataUrl base target allowPrivate =
      (isHttpUrl target && (ExtModel.urlHost base).any isLoopbackHost) :=
  @Defs.AuthMetadata.isAllowedMetadataUrl_eq_of_isLocalhostName base target allowPrivate d h_host
    h_local

/--
info: 'Theorems.auth.isAllowedMetadataUrl_eq_of_isLocalhostName' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.isAllowedMetadataUrl_eq_of_isLocalhostName

/-- **A06, every other host**: a target whose host the guard does not reject (a `Public` literal,
by `isDisallowedHost_iff_addressClass_ne_public`, H11 among them, or a domain that is neither a
`localhost` nor a cloud-metadata name) is allowed exactly when it is HTTP(S) with a host string
(upstream lines 1421–1423). No premise. With the SDK's default HTTP client and no proxy, a domain
is resolved later, under the resolver's address policy (N09); with a custom HTTP client or
through a proxy, nothing filters its addresses (H16: `instance-data` or `metadata.goog` is such
a domain). -/
theorem Theorems.auth.isAllowedMetadataUrl_eq_of_isDisallowedHost_eq_false (base target : url.Url)
    (allowPrivate : Bool) (h : url.host.Host Str) (h_host : ExtModel.urlHost target = some h)
    (h_ok : isDisallowedHost h = false) :
    isAllowedMetadataUrl base target allowPrivate = isHttpUrl target :=
  @Defs.AuthMetadata.isAllowedMetadataUrl_eq_of_isDisallowedHost_eq_false base target allowPrivate h
    h_host h_ok

/--
info: 'Theorems.auth.isAllowedMetadataUrl_eq_of_isDisallowedHost_eq_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.isAllowedMetadataUrl_eq_of_isDisallowedHost_eq_false

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
theorem Theorems.auth.allowsHost_of_isAllowedMetadataUrl
    (base target : url.Url) (allowPrivate : Bool)
    (h : isAllowedMetadataUrl base target allowPrivate = true) :
    allowsHost (literalIp (ExtModel.urlHost base))
      (if allowPrivate then withPrivate (baseClasses (ExtModel.urlHost base))
        else baseClasses (ExtModel.urlHost base))
      (ExtModel.urlHost target) = true :=
  @Defs.AuthMetadata.allowsHost_of_isAllowedMetadataUrl base target allowPrivate h

/--
info: 'Theorems.auth.allowsHost_of_isAllowedMetadataUrl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.allowsHost_of_isAllowedMetadataUrl

/-- **The resolver allows the base URL's own IP literal, whatever its class** (H14, recorded bug
of the resolver, human decision 2026-11-27): for a base URL with host `host` (none, a domain or
an IP literal), the resolver policy (N07 `allowsHost` with the base's literal `literalIp host`,
the `self.base_ip == Some(ip)` disjunct of `metadata_resolver.rs` line 167) allows a target
with the same host, for any granted classes, so also when the literal has class `Blocked`
(base `http://169.254.1.1:8080`, target `http://169.254.1.1:9090/`). The docs this contradicts
and the doc that states it on purpose: module docstring of `Proofs.Defs.AuthMetadata`, H14. A06
refuses such a target (`isAllowedMetadataUrl_eq_false_of_addressClass_eq_blocked`;
kernel-checked host-level cases at the end of `Proofs.Defs.AuthMetadata`). No premise. -/
theorem Theorems.auth.allowsHost_literalIp_self (host : Option (url.host.Host Str))
    (classes : List AddressClass) :
    allowsHost (literalIp host) classes host = true :=
  @Defs.AuthMetadata.allowsHost_literalIp_self host classes

/--
info: 'Theorems.auth.allowsHost_literalIp_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.allowsHost_literalIp_self

/-- **A08, `stringOfUtf8` inverts `utf8Bytes` on UTF-8 bytes**: the mismatch payload is the
received issuer. -/
theorem Theorems.auth.utf8Bytes_stringOfUtf8 (l : List U8) (h : ExtModel.IsUtf8 l) :
    utf8Bytes (stringOfUtf8 l) = l :=
  @Defs.AuthMetadata.utf8Bytes_stringOfUtf8 l h

/--
info: 'Theorems.auth.utf8Bytes_stringOfUtf8' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.utf8Bytes_stringOfUtf8

/-- **A08, RFC 9207 §2.4**: with a recorded issuer `e` and a received issuer `r`, the callback
check succeeds exactly when `r` is byte-identical to `e` (no normalization, no trailing-slash
tolerance). -/
theorem Theorems.auth.responseIssuerCheck_some_some_eq_ok_iff (e : String) (requireIssuer : Bool)
    (r : List U8) :
    responseIssuerCheck (some e) requireIssuer (some r) = .Ok () ↔ r = utf8Bytes e :=
  @Defs.AuthMetadata.responseIssuerCheck_some_some_eq_ok_iff e requireIssuer r

/--
info: 'Theorems.auth.responseIssuerCheck_some_some_eq_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.responseIssuerCheck_some_some_eq_ok_iff

/-- **A09, the bare RFC 8414 well-known path gives the empty issuer path** (RFC 8414 §3.1, an
issuer without path). -/
theorem Theorems.auth.issuerPath_oauthWellKnown : issuerPath oauthWellKnown = some [] :=
  @Defs.AuthMetadata.issuerPath_oauthWellKnown

/--
info: 'Theorems.auth.issuerPath_oauthWellKnown' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.issuerPath_oauthWellKnown

/-- **A09, the bare OpenID Connect well-known path gives the empty issuer path** (OpenID Connect
Discovery 1.0 §4, an issuer without path). -/
theorem Theorems.auth.issuerPath_oidcWellKnown : issuerPath oidcWellKnown = some [] :=
  @Defs.AuthMetadata.issuerPath_oidcWellKnown

/--
info: 'Theorems.auth.issuerPath_oidcWellKnown' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.issuerPath_oidcWellKnown

/-- **A09, RFC 8414 §3.1 path insertion is inverted**: the discovery path
`/.well-known/oauth-authorization-server/` followed by `s` gives the issuer path `s`. -/
theorem Theorems.auth.issuerPath_oauthWellKnown_append (s : List U8) :
    issuerPath (oauthWellKnown ++ slashByte :: s) = some s :=
  @Defs.AuthMetadata.issuerPath_oauthWellKnown_append s

/--
info: 'Theorems.auth.issuerPath_oauthWellKnown_append' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.issuerPath_oauthWellKnown_append

/-- **A09, OpenID Connect path insertion is inverted** (the MCP compatibility form): the
discovery path `/.well-known/openid-configuration/` followed by `s` gives the issuer path `s`. -/
theorem Theorems.auth.issuerPath_oidcWellKnown_append (s : List U8) :
    issuerPath (oidcWellKnown ++ slashByte :: s) = some s :=
  @Defs.AuthMetadata.issuerPath_oidcWellKnown_append s

/--
info: 'Theorems.auth.issuerPath_oidcWellKnown_append' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.issuerPath_oidcWellKnown_append

/-- **A09, OpenID Connect path appending is inverted** (OpenID Connect Discovery 1.0 §4): a path
`p` followed by `/.well-known/openid-configuration` gives `p` without its leading `/` bytes,
unless `p ++ oidcWellKnown` starts with one of the two path-insertion prefixes (premise (P),
where the earlier branches of upstream lines 2752–2757 take precedence). -/
theorem Theorems.auth.issuerPath_append_oidcWellKnown (p : List U8)
    (h_oauth : ¬ oauthWellKnown ++ [slashByte] <+: p ++ oidcWellKnown)
    (h_oidc : ¬ oidcWellKnown ++ [slashByte] <+: p ++ oidcWellKnown) :
    issuerPath (p ++ oidcWellKnown) = some (p.dropWhile (· = slashByte)) :=
  @Defs.AuthMetadata.issuerPath_append_oidcWellKnown p h_oauth h_oidc

/--
info: 'Theorems.auth.issuerPath_append_oidcWellKnown' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.issuerPath_append_oidcWellKnown

/-- **A09, issuer matching is reflexive.** -/
theorem Theorems.auth.issuersMatch_self (l : List U8) : issuersMatch l l = true :=
  @Defs.AuthMetadata.issuersMatch_self l

/--
info: 'Theorems.auth.issuersMatch_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.issuersMatch_self

/-- **A09, issuer matching is symmetric.** -/
theorem Theorems.auth.issuersMatch_comm (r e : List U8) : issuersMatch r e = issuersMatch e r :=
  @Defs.AuthMetadata.issuersMatch_comm r e

/--
info: 'Theorems.auth.issuersMatch_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.issuersMatch_comm

/-- **A09, what the trailing-slash tolerance allows** (H15, recorded bug: RFC 8414 §3.3 requires
identical issuers; the code tolerates exactly the final `/` of a root URL, as the upstream test
`authorization_metadata_allows_only_root_trailing_slash_equivalence`, lines 5141–5151, asserts):
matching issuers are byte-equal, or one is the other followed by `/`, and the shorter one parses
as a URL whose path is empty or `/` (query and fragment allowed, so the `/` may be the last byte
of a query or a fragment: `https://as.example?x/` matches `https://as.example?x`). -/
theorem Theorems.auth.eq_or_eq_append_slash_of_issuersMatch
    (r e : List U8) (h : issuersMatch r e = true) :
    r = e ∨ (e = r ++ [slashByte] ∧ isRootUrl r = true) ∨
      (r = e ++ [slashByte] ∧ isRootUrl e = true) :=
  @Defs.AuthMetadata.eq_or_eq_append_slash_of_issuersMatch r e h

/--
info: 'Theorems.auth.eq_or_eq_append_slash_of_issuersMatch' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.eq_or_eq_append_slash_of_issuersMatch

/-- **A10, a path covers itself.** -/
theorem Theorems.auth.pathCovers_self (p : List U8) : pathCovers p p = true :=
  @Defs.AuthMetadata.pathCovers_self p

/--
info: 'Theorems.auth.pathCovers_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.pathCovers_self

/-- **A10, a covering path is a byte prefix of the expected path** (the resource identifier names
the base URL's path or a segment-aligned ancestor of it, never a descendant). -/
theorem Theorems.auth.prefix_of_pathCovers (expectedPath actualPath : List U8)
    (h : pathCovers expectedPath actualPath = true) : actualPath <+: expectedPath :=
  @Defs.AuthMetadata.prefix_of_pathCovers expectedPath actualPath h

/--
info: 'Theorems.auth.prefix_of_pathCovers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.prefix_of_pathCovers

/-- **A10, an ancestor at a segment boundary covers** (H13, recorded bug: looser than the
"identical" of RFC 9728 §3.3; deliberate per the upstream test
`resource_identifier_matching_allows_matching_host_or_parent_path`): the path `a` covers every
expected path `a ++ "/" ++ b`, for example `/mcp` covers `/mcp/tools`. -/
theorem Theorems.auth.pathCovers_append_slash_append (a b : List U8) :
    pathCovers (a ++ slashByte :: b) a = true :=
  @Defs.AuthMetadata.pathCovers_append_slash_append a b

/--
info: 'Theorems.auth.pathCovers_append_slash_append' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.pathCovers_append_slash_append

/-- **A10, the expected path with a final `/` added does not cover it**: `/mcp/` does not cover
`/mcp`. This agrees with RFC 9728 §3.3 and with the upstream test
`resource_identifier_matching_allows_matching_host_or_parent_path` (lines 7187–7190), and is not
part of the recorded bug H13; it is inconsistent with the ancestor rule
(`pathCovers_append_slash_append`: `/mcp` covers `/mcp/tools`). -/
theorem Theorems.auth.pathCovers_append_slash_eq_false (p : List U8) :
    pathCovers p (p ++ [slashByte]) = false :=
  @Defs.AuthMetadata.pathCovers_append_slash_eq_false p

/--
info: 'Theorems.auth.pathCovers_append_slash_eq_false' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.pathCovers_append_slash_eq_false

/-- **A10, a URL is a valid resource identifier of itself** (upstream line 2999). -/
theorem Theorems.auth.isResourceIdentifierValid_self (u : url.Url) : isResourceIdentifierValid u u =
    true :=
  @Defs.AuthMetadata.isResourceIdentifierValid_self u

/--
info: 'Theorems.auth.isResourceIdentifierValid_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.isResourceIdentifierValid_self

/-! ## Compositions: the security meaning end to end -/

/-- **A06 with A05: a cloud-metadata name is never allowed** (premise (B)): a target whose host is
a domain that normalizes to `metadata`, `metadata.google.internal` or `metadata.azure.internal`
is refused, whatever the base URL and `allow_private`. Consequence of
`is_allowed_metadata_url_spec` and the premise-free law
`Defs.AuthMetadata.isAllowedMetadataUrl_eq_false_of_isCloudMetadataName`. No target premise:
such a domain is ASCII, hence UTF-8 (`normalizeHost` changes only ASCII letters and trailing
dots). (B) is needed: the base URL's host is read (upstream line 1434). -/
theorem Theorems.auth.AuthorizationManager.is_allowed_metadata_url_eq_false_of_isCloudMetadataName
    (base_url target : url.Url)
    (allow_private : Bool) (d : Str) (h_base : HostUtf8 base_url)
    (h_host : ExtModel.urlHost target = some (url.host.Host.Domain d))
    (hc : isCloudMetadataName d.val = true) :
    rmcp.transport.auth.AuthorizationManager.is_allowed_metadata_url base_url target allow_private
      ⦃ (result : Bool) =>
      result = false ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.is_allowed_metadata_url_eq_false_of_isCloudMetadataName
    base_url target allow_private d h_base h_host hc

/--
info: 'Theorems.auth.AuthorizationManager.is_allowed_metadata_url_eq_false_of_isCloudMetadataName' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_allowed_metadata_url_eq_false_of_isCloudMetadataName

/-- **A06 with A05 and N01: a `Blocked` literal is never allowed** (premise (B)): a target whose
host is an IP literal of class `Blocked` is refused, whatever the base URL and `allow_private`,
also when it is the base URL's own literal (which the resolver allows, H14,
`Defs.AuthMetadata.allowsHost_literalIp_self`). Consequence of `is_allowed_metadata_url_spec`
and `Defs.AuthMetadata.isAllowedMetadataUrl_eq_false_of_addressClass_eq_blocked`. No target
premise (an IP literal has no domain). -/
theorem Theorems.auth.AuthorizationManager.is_allowed_metadata_url_eq_false_of_addressClass_eq_blocked
    (base_url target : url.Url)
    (allow_private : Bool) (h : url.host.Host Str) (h_base : HostUtf8 base_url)
    (h_host : ExtModel.urlHost target = some h)
    (h_blocked : (hostIp h).map addressClass = some AddressClass.Blocked) :
    rmcp.transport.auth.AuthorizationManager.is_allowed_metadata_url base_url target allow_private
      ⦃ (result : Bool) =>
      result = false ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.is_allowed_metadata_url_eq_false_of_addressClass_eq_blocked
    base_url target allow_private h h_base h_host h_blocked

/--
info: 'Theorems.auth.AuthorizationManager.is_allowed_metadata_url_eq_false_of_addressClass_eq_blocked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_allowed_metadata_url_eq_false_of_addressClass_eq_blocked

/-- **A06, a `Private` literal** (premise (B)): allowed exactly when the target is HTTP(S) with a
host string and `allow_private` holds (H10: the cloud-metadata endpoints in private ranges
included). Consequence of `is_allowed_metadata_url_spec` and
`Defs.AuthMetadata.isAllowedMetadataUrl_eq_of_addressClass_eq_private`. No target premise (an
IP literal has no domain). -/
theorem Theorems.auth.AuthorizationManager.is_allowed_metadata_url_eq_of_addressClass_eq_private
    (base_url target : url.Url)
    (allow_private : Bool) (h : url.host.Host Str) (h_base : HostUtf8 base_url)
    (h_host : ExtModel.urlHost target = some h)
    (h_private : (hostIp h).map addressClass = some AddressClass.Private) :
    rmcp.transport.auth.AuthorizationManager.is_allowed_metadata_url base_url target allow_private
      ⦃ (result : Bool) =>
      result = (isHttpUrl target && allow_private) ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.is_allowed_metadata_url_eq_of_addressClass_eq_private
    base_url target allow_private h h_base h_host h_private

/--
info: 'Theorems.auth.AuthorizationManager.is_allowed_metadata_url_eq_of_addressClass_eq_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_allowed_metadata_url_eq_of_addressClass_eq_private

/-- **A06, a `Loopback` literal** (premise (B)): allowed exactly when the target is HTTP(S) with a
host string, the base URL's host is a loopback host and the target's host is `127/8` or `::1`;
`allow_private` plays no role. Consequence of `is_allowed_metadata_url_spec` and
`Defs.AuthMetadata.isAllowedMetadataUrl_eq_of_addressClass_eq_loopback`. No target premise (an
IP literal has no domain). -/
theorem Theorems.auth.AuthorizationManager.is_allowed_metadata_url_eq_of_addressClass_eq_loopback
    (base_url target : url.Url)
    (allow_private : Bool) (h : url.host.Host Str) (h_base : HostUtf8 base_url)
    (h_host : ExtModel.urlHost target = some h)
    (h_loopback : (hostIp h).map addressClass = some AddressClass.Loopback) :
    rmcp.transport.auth.AuthorizationManager.is_allowed_metadata_url base_url target allow_private
      ⦃ (result : Bool) =>
      result = (isHttpUrl target && (ExtModel.urlHost base_url).any isLoopbackHost &&
        isLoopbackHost h) ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.is_allowed_metadata_url_eq_of_addressClass_eq_loopback
    base_url target allow_private h h_base h_host h_loopback

/--
info: 'Theorems.auth.AuthorizationManager.is_allowed_metadata_url_eq_of_addressClass_eq_loopback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_allowed_metadata_url_eq_of_addressClass_eq_loopback

/-- **A06, a `localhost` name** (premises (T), (B)): allowed exactly when the target is HTTP(S)
with a host string and the base URL's host is a loopback host. Consequence of
`is_allowed_metadata_url_spec` and `Defs.AuthMetadata.isAllowedMetadataUrl_eq_of_isLocalhostName`.
-/
theorem Theorems.auth.AuthorizationManager.is_allowed_metadata_url_eq_of_isLocalhostName
    (base_url target : url.Url)
    (allow_private : Bool) (d : Str) (h_base : HostUtf8 base_url)
    (h_target : isHttpUrl target = true → HostUtf8 target)
    (h_host : ExtModel.urlHost target = some (url.host.Host.Domain d))
    (h_local : isLocalhostName d.val = true) :
    rmcp.transport.auth.AuthorizationManager.is_allowed_metadata_url base_url target allow_private
      ⦃ (result : Bool) =>
      result = (isHttpUrl target && (ExtModel.urlHost base_url).any isLoopbackHost) ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.is_allowed_metadata_url_eq_of_isLocalhostName base_url
    target allow_private d h_base h_target h_host h_local

/--
info: 'Theorems.auth.AuthorizationManager.is_allowed_metadata_url_eq_of_isLocalhostName' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_allowed_metadata_url_eq_of_isLocalhostName

/-- **A06, every other host** (premise (T)): a target whose host the guard does not reject is
allowed exactly when it is HTTP(S) with a host string (the law
`Defs.AuthMetadata.isAllowedMetadataUrl_eq_of_isDisallowedHost_eq_false`). No base premise: the
call returns at upstream line 1422 (or earlier, lines 1413–1419) without reading the base URL's
host, so this does not follow from `is_allowed_metadata_url_spec`, which assumes (B). With the
SDK's default HTTP client and no proxy, a domain is resolved later, under the resolver's
address policy (N09); with a custom HTTP client or through a proxy, nothing filters its
addresses (H16). -/
theorem Theorems.auth.AuthorizationManager.is_allowed_metadata_url_eq_of_isDisallowedHost_eq_false
    (base_url target : url.Url)
    (allow_private : Bool) (h : url.host.Host Str)
    (h_target : isHttpUrl target = true → HostUtf8 target)
    (h_host : ExtModel.urlHost target = some h) (h_ok : isDisallowedHost h = false) :
    rmcp.transport.auth.AuthorizationManager.is_allowed_metadata_url base_url target allow_private
      ⦃ (result : Bool) =>
      result = isHttpUrl target ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.is_allowed_metadata_url_eq_of_isDisallowedHost_eq_false
    base_url target allow_private h h_target h_host h_ok

/--
info: 'Theorems.auth.AuthorizationManager.is_allowed_metadata_url_eq_of_isDisallowedHost_eq_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.is_allowed_metadata_url_eq_of_isDisallowedHost_eq_false

/-- **A07 on success: the URL is the candidate the value names.** If
`resolve_resource_metadata_url value base_url allow_private` returns `some u`, then `u` is the
trimmed value parsed, or else resolved against the base URL (`metadataCandidate`). Covers only
successful calls and does not show that the call succeeds. No premise. -/
theorem Theorems.auth.AuthorizationManager.metadataCandidate_eq_of_resolve_resource_metadata_url_eq_ok_some
    (value : Str)
    (base_url : url.Url) (allow_private : Bool) (u : url.Url)
    (h : rmcp.transport.auth.AuthorizationManager.resolve_resource_metadata_url value base_url
      allow_private = ok (some u)) :
    metadataCandidate value.val base_url = some u :=
  @rmcp.transport.auth.AuthorizationManager.metadataCandidate_eq_of_resolve_resource_metadata_url_eq_ok_some
    value base_url allow_private u h

/--
info: 'Theorems.auth.AuthorizationManager.metadataCandidate_eq_of_resolve_resource_metadata_url_eq_ok_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.metadataCandidate_eq_of_resolve_resource_metadata_url_eq_ok_some

/-- **A07 on success: the URL is HTTP(S) with a host string** (both acceptances of upstream lines
1458 and 1465 test A04). Covers only successful calls. No premise. -/
theorem Theorems.auth.AuthorizationManager.isHttpUrl_of_resolve_resource_metadata_url_eq_ok_some
    (value : Str) (base_url : url.Url)
    (allow_private : Bool) (u : url.Url)
    (h : rmcp.transport.auth.AuthorizationManager.resolve_resource_metadata_url value base_url
      allow_private = ok (some u)) :
    isHttpUrl u = true :=
  @rmcp.transport.auth.AuthorizationManager.isHttpUrl_of_resolve_resource_metadata_url_eq_ok_some
    value base_url allow_private u h

/--
info: 'Theorems.auth.AuthorizationManager.isHttpUrl_of_resolve_resource_metadata_url_eq_ok_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.isHttpUrl_of_resolve_resource_metadata_url_eq_ok_some

/-- **A07 on success: same origin, or allowed by the metadata URL policy.** If the call returns
`some u`, `u` is same-origin with the base URL or A06 allows it with the same `allow_private`.
With the premise-free laws `Defs.AuthMetadata.isAllowedMetadataUrl_eq_…` this gives, for a
cross-origin `u`, the consequences for each kind of host without UTF-8 premises (for example
`allow_private_eq_true_of_resolve_resource_metadata_url_eq_ok_some`). Covers only successful
calls. No premise. -/
theorem Theorems.auth.AuthorizationManager.isSameOrigin_or_isAllowedMetadataUrl_of_resolve_resource_metadata_url_eq_ok_some
    
    (value : Str) (base_url : url.Url) (allow_private : Bool) (u : url.Url)
    (h : rmcp.transport.auth.AuthorizationManager.resolve_resource_metadata_url value base_url
      allow_private = ok (some u)) :
    isSameOrigin base_url u = true ∨ isAllowedMetadataUrl base_url u allow_private = true :=
  @rmcp.transport.auth.AuthorizationManager.isSameOrigin_or_isAllowedMetadataUrl_of_resolve_resource_metadata_url_eq_ok_some
    value base_url allow_private u h

/--
info: 'Theorems.auth.AuthorizationManager.isSameOrigin_or_isAllowedMetadataUrl_of_resolve_resource_metadata_url_eq_ok_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.isSameOrigin_or_isAllowedMetadataUrl_of_resolve_resource_metadata_url_eq_ok_some

/-- **A07 on success: no downgrade from `https`.** If the base URL's scheme is `https` and the
call returns `some u`, then `u`'s scheme is `https` (same origin implies the same scheme; the
check of upstream lines 1461–1464 refuses the rest). Covers only successful calls. No premise
beyond the `https` base. -/
theorem Theorems.auth.AuthorizationManager.urlScheme_eq_https_of_resolve_resource_metadata_url_eq_ok_some
    (value : Str)
    (base_url : url.Url) (allow_private : Bool) (u : url.Url)
    (h_https : (ExtModel.urlScheme base_url).val = utf8Bytes "https")
    (h : rmcp.transport.auth.AuthorizationManager.resolve_resource_metadata_url value base_url
      allow_private = ok (some u)) :
    (ExtModel.urlScheme u).val = utf8Bytes "https" :=
  @rmcp.transport.auth.AuthorizationManager.urlScheme_eq_https_of_resolve_resource_metadata_url_eq_ok_some
    value base_url allow_private u h_https h

/--
info: 'Theorems.auth.AuthorizationManager.urlScheme_eq_https_of_resolve_resource_metadata_url_eq_ok_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.urlScheme_eq_https_of_resolve_resource_metadata_url_eq_ok_some

/-- **A07 on success: a cross-origin `Private` literal needs `allow_private`** (H10). If the
call returns `some u`, `u` is not same-origin with the base URL and its host is an IP literal of
class `Private`, then `allow_private` holds: a private base URL does not suffice (H12), and with
`allow_private` every private literal passes, the cloud-metadata endpoints `100.100.100.200` and
`fd00:ec2::254` included (H10). Covers only successful calls. No premise. -/
theorem Theorems.auth.AuthorizationManager.allow_private_eq_true_of_resolve_resource_metadata_url_eq_ok_some
    (value : Str)
    (base_url : url.Url) (allow_private : Bool) (u : url.Url) (h : url.host.Host Str)
    (h_ok : rmcp.transport.auth.AuthorizationManager.resolve_resource_metadata_url value base_url
      allow_private = ok (some u))
    (h_origin : isSameOrigin base_url u = false) (h_host : ExtModel.urlHost u = some h)
    (h_private : (hostIp h).map addressClass = some AddressClass.Private) :
    allow_private = true :=
  @rmcp.transport.auth.AuthorizationManager.allow_private_eq_true_of_resolve_resource_metadata_url_eq_ok_some
    value base_url allow_private u h h_ok h_origin h_host h_private

/--
info: 'Theorems.auth.AuthorizationManager.allow_private_eq_true_of_resolve_resource_metadata_url_eq_ok_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.allow_private_eq_true_of_resolve_resource_metadata_url_eq_ok_some

/-- **A07 on success: a cross-origin `Loopback` literal needs a loopback base.** If the call
returns `some u`, `u` is not same-origin with the base URL and its host is an IP literal of class
`Loopback`, then the base URL's host is a loopback host (`localhost` name, `127/8` or `::1`) and
`u`'s host is `127/8` or `::1` (not an IPv6 embedding of `127/8`, H12). Covers only successful
calls. No premise. -/
theorem Theorems.auth.AuthorizationManager.isLoopbackHost_of_resolve_resource_metadata_url_eq_ok_some
    (value : Str)
    (base_url : url.Url) (allow_private : Bool) (u : url.Url) (h : url.host.Host Str)
    (h_ok : rmcp.transport.auth.AuthorizationManager.resolve_resource_metadata_url value base_url
      allow_private = ok (some u))
    (h_origin : isSameOrigin base_url u = false) (h_host : ExtModel.urlHost u = some h)
    (h_loopback : (hostIp h).map addressClass = some AddressClass.Loopback) :
    (ExtModel.urlHost base_url).any isLoopbackHost = true ∧ isLoopbackHost h = true :=
  @rmcp.transport.auth.AuthorizationManager.isLoopbackHost_of_resolve_resource_metadata_url_eq_ok_some
    value base_url allow_private u h h_ok h_origin h_host h_loopback

/--
info: 'Theorems.auth.AuthorizationManager.isLoopbackHost_of_resolve_resource_metadata_url_eq_ok_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.isLoopbackHost_of_resolve_resource_metadata_url_eq_ok_some

/-- **A07, a same-origin HTTP(S) candidate is accepted**, whatever its host (also a loopback,
private or blocked literal: the base URL's own origin is trusted; upstream lines 1458–1460
return before the policy check, and no host is read). No premise: same origin with an HTTP(S)
candidate implies an `http` or `https` base URL (`urlScheme_eq_of_isSameOrigin`), so the AD8
premise (H) holds. -/
theorem Theorems.auth.AuthorizationManager.resolve_resource_metadata_url_eq_some_of_isSameOrigin
    (value : Str) (base_url : url.Url)
    (allow_private : Bool) (u : url.Url)
    (h_candidate : metadataCandidate value.val base_url = some u)
    (h_http : isHttpUrl u = true) (h_origin : isSameOrigin base_url u = true) :
    rmcp.transport.auth.AuthorizationManager.resolve_resource_metadata_url value base_url
      allow_private ⦃ (result : Option url.Url) =>
      result = some u ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.resolve_resource_metadata_url_eq_some_of_isSameOrigin
    value base_url allow_private u h_candidate h_http h_origin

/--
info: 'Theorems.auth.AuthorizationManager.resolve_resource_metadata_url_eq_some_of_isSameOrigin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.resolve_resource_metadata_url_eq_some_of_isSameOrigin

/-- **A07 with A06: a cross-origin `Blocked` literal is refused** (premises (H), (B); no premise
on the candidate's host, an IP literal). The call does not fail and returns `none`; that a
successful call never returns such a URL needs no premise
(`isSameOrigin_or_isAllowedMetadataUrl_of_resolve_resource_metadata_url_eq_ok_some` with
`Defs.AuthMetadata.isAllowedMetadataUrl_eq_false_of_addressClass_eq_blocked`). -/
theorem Theorems.auth.AuthorizationManager.resolve_resource_metadata_url_eq_none_of_addressClass_eq_blocked
    (value : Str)
    (base_url : url.Url) (allow_private : Bool) (u : url.Url) (h : url.host.Host Str)
    (h_scheme : isHttpScheme (ExtModel.urlScheme base_url).val = true)
    (h_base : HostUtf8 base_url)
    (h_candidate : metadataCandidate value.val base_url = some u)
    (h_origin : isSameOrigin base_url u = false) (h_host : ExtModel.urlHost u = some h)
    (h_blocked : (hostIp h).map addressClass = some AddressClass.Blocked) :
    rmcp.transport.auth.AuthorizationManager.resolve_resource_metadata_url value base_url
      allow_private ⦃ (result : Option url.Url) =>
      result = none ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.resolve_resource_metadata_url_eq_none_of_addressClass_eq_blocked
    value base_url allow_private u h h_scheme h_base h_candidate h_origin h_host h_blocked

/--
info: 'Theorems.auth.AuthorizationManager.resolve_resource_metadata_url_eq_none_of_addressClass_eq_blocked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.resolve_resource_metadata_url_eq_none_of_addressClass_eq_blocked

/-- **A07 with A06: a cross-origin cloud-metadata name is refused** (premises (H), (B); no
premise on the candidate's host, which is ASCII). The call does not fail and returns `none`;
that a successful call never returns such a URL needs no premise
(`isSameOrigin_or_isAllowedMetadataUrl_of_resolve_resource_metadata_url_eq_ok_some` with
`Defs.AuthMetadata.isAllowedMetadataUrl_eq_false_of_isCloudMetadataName`). -/
theorem Theorems.auth.AuthorizationManager.resolve_resource_metadata_url_eq_none_of_isCloudMetadataName
    (value : Str)
    (base_url : url.Url) (allow_private : Bool) (u : url.Url) (d : Str)
    (h_scheme : isHttpScheme (ExtModel.urlScheme base_url).val = true)
    (h_base : HostUtf8 base_url)
    (h_candidate : metadataCandidate value.val base_url = some u)
    (h_origin : isSameOrigin base_url u = false)
    (h_host : ExtModel.urlHost u = some (url.host.Host.Domain d))
    (hc : isCloudMetadataName d.val = true) :
    rmcp.transport.auth.AuthorizationManager.resolve_resource_metadata_url value base_url
      allow_private ⦃ (result : Option url.Url) =>
      result = none ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.resolve_resource_metadata_url_eq_none_of_isCloudMetadataName
    value base_url allow_private u d h_scheme h_base h_candidate h_origin h_host hc

/--
info: 'Theorems.auth.AuthorizationManager.resolve_resource_metadata_url_eq_none_of_isCloudMetadataName' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.resolve_resource_metadata_url_eq_none_of_isCloudMetadataName

/-- **A08, RFC 9207 §2.4 end to end** (premises (S), (R)): with a recorded issuer `e` and a
received issuer `r`, the callback check returns `Ok` exactly when the bytes of `r` are those of
`e`, and otherwise `Err (AuthorizationServerMismatch e r)`. -/
theorem Theorems.auth.AuthorizationManager.check_authorization_response_issuer_eq_ok_iff
    (stored_state : StoredAuthorizationState)
    (e : String) (r : Str) (h_expected : stored_state.expected_issuer = some e)
    (h_fits : e.utf8ByteSize ≤ Usize.max) (h_utf8 : ExtModel.IsUtf8 r.val) :
    rmcp.transport.auth.AuthorizationManager.check_authorization_response_issuer stored_state (some
      r)
      ⦃ (result : core.result.Result Unit IssuerError) =>
      (result = .Ok () ↔ r.val = utf8Bytes e) ∧
      (r.val ≠ utf8Bytes e → ∃ rs, utf8Bytes rs = r.val ∧
        result = .Err (.AuthorizationServerMismatch e rs)) ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.check_authorization_response_issuer_eq_ok_iff
    stored_state e r h_expected h_fits h_utf8

/--
info: 'Theorems.auth.AuthorizationManager.check_authorization_response_issuer_eq_ok_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.check_authorization_response_issuer_eq_ok_iff

/-- **A09, the spec theorem without an explicit expected issuer** (premises (S), (D), (AD7)): the
check compares the metadata's `issuer` with the issuer derived from the discovery URL
(`derivedIssuer`: the RFC 8414 §3.1 path insertion `…/.well-known/oauth-authorization-server/s`
gives the issuer path `s`, `issuerPath_oauthWellKnown_append`; the OpenID Connect forms
likewise). H9: a recorded issue in this check, under private disclosure; details withheld until
it is reported. -/
theorem Theorems.auth.AuthorizationManager.check_authorization_metadata_issuer_spec_none
    (allow_missing_issuer : Bool)
    (discovery_url : url.Url) (metadata : AuthorizationMetadata)
    (h_received : ∀ r, metadata.issuer = some r → r.utf8ByteSize ≤ Usize.max)
    (h_derived : ∀ e, derivedIssuer discovery_url = some e → e.utf8ByteSize ≤ Usize.max)
    (h_discovery : DiscoveryUrlFits discovery_url) :
    rmcp.transport.auth.AuthorizationManager.check_authorization_metadata_issuer
      allow_missing_issuer discovery_url none metadata
      ⦃ (result : core.result.Result Unit IssuerError) =>
      result = metadataIssuerCheck allow_missing_issuer (derivedIssuer discovery_url)
        metadata.issuer ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.check_authorization_metadata_issuer_spec_none
    allow_missing_issuer discovery_url metadata h_received h_derived h_discovery

/--
info: 'Theorems.auth.AuthorizationManager.check_authorization_metadata_issuer_spec_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.check_authorization_metadata_issuer_spec_none

/-- **A09, a mismatch always yields `AuthorizationServerMismatch` with both issuers** (premises
(U), (S), (D), (AD7)): if the expected issuer (explicit, or derived) is `e`, the metadata's
`issuer` is `r` and they do not match (`issuersMatch`), the result is
`Err (AuthorizationServerMismatch e r)`, whatever `allow_missing_issuer`. -/
theorem Theorems.auth.AuthorizationManager.check_authorization_metadata_issuer_eq_mismatch
    (allow_missing_issuer : Bool)
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
    rmcp.transport.auth.AuthorizationManager.check_authorization_metadata_issuer
      allow_missing_issuer discovery_url expected_issuer
      metadata ⦃ (result : core.result.Result Unit IssuerError) =>
      result = .Err (.AuthorizationServerMismatch e r) ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.check_authorization_metadata_issuer_eq_mismatch
    allow_missing_issuer discovery_url expected_issuer metadata e r h_utf8 h_received h_derived
      h_discovery h_expected h_issuer h_mismatch

/--
info: 'Theorems.auth.AuthorizationManager.check_authorization_metadata_issuer_eq_mismatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.check_authorization_metadata_issuer_eq_mismatch

/-- **A09 on success: RFC 8414 §3.3 up to a root slash.** If there is an expected issuer `e`
(explicit, or derived), the metadata names an `issuer` `r` and the check returns `Ok`, then `r`
and `e` are equal, or differ only by a final `/` after a URL whose path is empty or `/` (query
and fragment allowed; H15, recorded bug). Covers only successful calls and does not show that
the call succeeds. No premise (in particular no AD7 premise: the "on success" form needs no
domain restriction). -/
theorem Theorems.auth.AuthorizationManager.eq_or_eq_append_slash_of_check_authorization_metadata_issuer_eq_ok
    
    (allow_missing_issuer : Bool) (discovery_url : url.Url) (expected_issuer : Option Str)
    (metadata : AuthorizationMetadata) (e r : String)
    (h_expected : expectedIssuerOf (expected_issuer.map (·.val)) discovery_url = some e)
    (h_issuer : metadata.issuer = some r)
    (h : rmcp.transport.auth.AuthorizationManager.check_authorization_metadata_issuer
      allow_missing_issuer discovery_url expected_issuer
      metadata = ok (.Ok ())) :
    r = e ∨ (utf8Bytes e = utf8Bytes r ++ [slashByte] ∧ isRootUrl (utf8Bytes r) = true) ∨
      (utf8Bytes r = utf8Bytes e ++ [slashByte] ∧ isRootUrl (utf8Bytes e) = true) :=
  @rmcp.transport.auth.AuthorizationManager.eq_or_eq_append_slash_of_check_authorization_metadata_issuer_eq_ok
    allow_missing_issuer discovery_url expected_issuer metadata e r h_expected h_issuer h

/--
info: 'Theorems.auth.AuthorizationManager.eq_or_eq_append_slash_of_check_authorization_metadata_issuer_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.eq_or_eq_append_slash_of_check_authorization_metadata_issuer_eq_ok

/-- **A10, when the resource is accepted** (premise (S)): the check returns `Ok` exactly when the
metadata names a resource that parses as a URL without fragment and is a valid identifier of the
base URL (`isResourceIdentifierValid`: equal, or same scheme, host and port with a path that
covers the base URL's path at a segment boundary; H13: query and user information are not
compared). -/
theorem Theorems.auth.AuthorizationManager.check_resource_metadata_resource_eq_ok_iff
    (base_url : url.Url)
    (metadata : ResourceServerMetadata)
    (h_fits : ∀ r, metadata.resource = some r → r.utf8ByteSize ≤ Usize.max) :
    rmcp.transport.auth.AuthorizationManager.check_resource_metadata_resource base_url metadata
      ⦃ (result : core.result.Result Unit ProtectedResourceMetadataInvalidReason) =>
      (result = .Ok () ↔ ∃ r u, metadata.resource = some r ∧
        ExtModel.urlParse (utf8Bytes r) = .Ok u ∧ ExtModel.urlFragment u = none ∧
        isResourceIdentifierValid base_url u = true) ⦄ :=
  @rmcp.transport.auth.AuthorizationManager.check_resource_metadata_resource_eq_ok_iff base_url
    metadata h_fits

/--
info: 'Theorems.auth.AuthorizationManager.check_resource_metadata_resource_eq_ok_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.auth.AuthorizationManager.check_resource_metadata_resource_eq_ok_iff
