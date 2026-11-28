/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Aeneas
public import Rmcp.Types
public import Rmcp.FunsExternal
public import Defs.Bytes
public import Proofs.Defs.Net
public import Proofs.Defs.MetadataResolver

@[expose] public section

/-!
# Definitions for the OAuth metadata URL and issuer statements (A04–A10)

**Signed off by the human spec owner on 2026-11-27** with the statements that use these
definitions (proved in `Proofs.Transport.AuthMetadata`, restated in
`Proofs.Internal.Transport.Auth.AuthMetadata`). Built as part of the `Proofs` root (precedent
`Proofs.Defs.MetadataResolver`). The vocabulary of the statements about the private checks of
`crates/rmcp/src/transport/auth.rs` that translation patch 06 makes translatable (human
decisions AD1–AD8, `formal/README.md`):

- A04 `is_http_url`: `isHttpScheme`, `isHttpUrl`;
- `is_same_origin` (callee of A07): `isSameOrigin`, over `portOrKnownDefault` and
  `knownDefaultPort` (the readable copy of the trusted `ExtModel.defaultPort`; the law
  `knownDefaultPort_eq_defaultPort` is the bridge);
- A05 `is_disallowed_metadata_host` with `is_disallowed_metadata_hostname`: `cloudMetadataHosts`,
  `isCloudMetadataName`, `isDisallowedHostname`, `isDisallowedHost`;
- A06 `is_allowed_metadata_url` and its patch helper `is_allowed_disallowed_host`:
  `isAllowedDisallowedHost`, `isAllowedMetadataUrl`;
- A07 `resolve_resource_metadata_url`: `isUnicodeWhitespace`, `trimUnicodeWhitespace` (the
  readable `str::trim`), `metadataCandidate`, `resolveResourceMetadataUrl`;
- A08 `check_authorization_response_issuer`: `issuerNotRecordedMessage`, `stringOfUtf8`,
  `responseIssuerCheck`;
- A09 `check_authorization_metadata_issuer` with `expected_issuer_for_authorization_metadata_url`,
  `issuer_identifiers_match`, `trim_root_slash`, `is_root_url`: `issuerPath`, `derivedIssuer`,
  `expectedIssuerOf`, `isRootUrl`, `trimRootSlash`, `issuersMatch`, `metadataIssuerCheck`, and
  the premise `DiscoveryUrlFits` (AD7);
- A10 `check_resource_metadata_resource` with `is_resource_identifier_valid`: `pathCovers`,
  `isResourceIdentifierValid`, `resourceCheck`;
- the UTF-8 premise on the host of a URL, `HostUtf8` (rule (ii)(b) of `ExtModel.IsUtf8`).

The targets are private (`fn` without `pub` in `impl AuthorizationManager`), so these definitions
live in `Proofs/Defs/` (human decision 2026-11-24); module `Proofs.Defs.AuthMetadata`, Lean
namespace `Defs.AuthMetadata`. The definitions follow the dependency order Lean needs, which is
the Rust source order except where a callee must come first.

**Bugs the definitions describe** (human decision 2026-11-27: the definitions describe the code
exactly; each is named again at the definition concerned):
- H9 (`issuerPath`, `metadataIssuerCheck`): a recorded issue in the A09 issuer check, under
  private disclosure; details withheld until it is reported.
- H10 (`isAllowedDisallowedHost`): with `allow_private`, every `Private` literal is allowed,
  including the cloud-metadata endpoints in private ranges (`100.100.100.200` in `100.64/10`,
  `fd00:ec2::254` in `fc00::/7`). The resolver does the same: whenever it grants `Private`, with
  `allowing_private_addresses` (N06) or from a `Private`-literal base (N04), it accepts the DNS
  answers `100.100.100.200` and `fd00:ec2::254` (N09; scratch probe on the patched copy,
  2026-11-27).
- H11 (`isDisallowedHost`): `100::/64`, `192.0.0.192` and the IPv4-translated range
  `::ffff:0:0:0/96` (RFC 2765 §2.1; for example `::ffff:0:a9fe:a9fe`, `::ffff:0:7f00:1`) are not
  rejected by the guard and have class `Public`, so A06 allows them as it allows any public
  host. The IPv4-mapped range `::ffff:0:0/96` is decided by its embedded IPv4 address (A01,
  upstream lines 1359–1368 and 1371–1373: `[::ffff:8.8.8.8]` is allowed,
  `[::ffff:169.254.169.254]` refused); the gap is the IPv4-translated range `::ffff:0:0:0/96`
  (e.g. `::ffff:0:a9fe:a9fe`), which carries no A01 embedding. The resolver also accepts DNS
  answers in these ranges, since their class is `Public` (N09; scratch probe on the patched
  copy, 2026-11-27).
- H12 (`isAllowedMetadataUrl`): the bug is that A06 refuses targets that the resolver policy
  (N04/N07) accepts (false refusals): some IP literals, and a localhost name from a base that is
  an IPv6 embedding of `127/8`. Context, not the reason: the doc of `AuthorizationManager::new`
  (upstream lines 1502–1510) gives only a necessary condition ("only when") for loopback and
  private addresses, so these refusals do not contradict it. The cases (the only place they are
  listed in full):
  - an IPv6 embedding of `127/8` (IPv4-mapped `::ffff:127.0.0.1`, IPv4-compatible `::7f00:1`,
    NAT64 `64:ff9b::7f00:1`, 6to4 `2002:7f00:1::`; class `Loopback` for N01, but not a loopback
    host for `Ipv6Addr::is_loopback`) as the target, from a base that grants `Loopback` (N04: a
    localhost name, i.e. `localhost` or `*.localhost`, `127/8`, `::1`, or an IPv6 embedding of
    `127/8`);
  - such an embedding as the base, with a loopback target (`127/8`, `::1`, such an embedding,
    or a `localhost` name, which the resolver lets through and whose loopback addresses it then
    accepts);
  - a `Private`-literal base (`10/8`, `fc00::/7`, an embedding such as `::ffff:10.0.0.1`, …)
    without `allow_private`, with a `Private`-literal target (the base literal itself included):
    the resolver grants `Private` (N04), A06 does not.
  For IP-literal targets, which reqwest connects to without resolving, A06 is never looser than
  the resolver (it refuses whenever the resolver would refuse; law
  `allowsHost_of_isAllowedMetadataUrl`; scratch probes on the patched copy, 2026-11-27). For a
  domain target the comparison says nothing: the
  resolver lets every domain through at host level (`allowsHost`) and decides when the name is
  resolved (N09), and with a custom HTTP client or through a proxy nothing filters the resolved
  addresses (H16).
- H13 (`isResourceIdentifierValid`): the resource check accepts an ancestor path, a different
  query and different user information, looser than "identical" (RFC 9728 §3.3); the query rule
  is deliberate (comment at upstream line 3013), and so is the ancestor rule (test
  `resource_identifier_matching_allows_matching_host_or_parent_path`, lines 7148–7215). It
  rejects the base path with a final `/` added (`/mcp/` for `/mcp`); that agrees with RFC 9728
  §3.3 and with the same test (lines 7187–7190) and is not part of H13, but it is inconsistent
  with the ancestor rule (`/mcp` is accepted for `/mcp/tools`).
- H14 (the resolver policy, recorded at `isAllowedMetadataUrl`; human decision 2026-11-27): the
  resolver allows the base URL's own IP literal whatever its class (N07, the `baseIp = some ip`
  disjunct of `Defs.MetadataResolver.allowsHost`; `metadata_resolver.rs` lines 164–172), also a
  `Blocked` one: for the base `http://169.254.1.1:8080` it allows `http://169.254.1.1:9090/`,
  and likewise for `0.0.0.0`, `fe80::1` or `::`. The method doc of `allows_url`
  (`metadata_resolver.rs` lines 162–163, "The base URL's own literal is always allowed.") states
  the exemption on purpose: it lets the client reach the base URL itself. It contradicts the
  doc of `AuthorizationManager::new` (upstream lines 1506–1507: "Link-local and other reserved
  addresses are always rejected") and the module doc of `metadata_resolver.rs` (lines 8–9).
  A06 refuses such a target (law `isAllowedMetadataUrl_eq_false_of_addressClass_eq_blocked`);
  law `allowsHost_literalIp_self`.
- H15 (`trimRootSlash`, `issuersMatch`; human decision 2026-11-27): `issuer_identifiers_match`,
  hence A09, tolerates a final `/` after a root URL (`https://as.example/` matches
  `https://as.example`), deviating from the "identical" of RFC 8414 §3.3; the upstream test
  `authorization_metadata_allows_only_root_trailing_slash_equivalence` (lines 5141–5151) asserts
  the tolerance. The `/` removed may be the last byte of a query or a fragment:
  `issuer_identifiers_match("https://as.example?x/", "https://as.example?x")` is true, and so
  with the fragment `f/` against the fragment `f` (what remains is a root URL with a query or
  fragment; scratch probe on the patched copy, 2026-11-27). Law
  `eq_or_eq_append_slash_of_issuersMatch`.
- H16 (`cloudMetadataHosts`, `isCloudMetadataName`; human decision 2026-11-27): the list of
  cloud-metadata host names has only three names (upstream lines 39–43); other metadata names,
  for example `instance-data` or `metadata.goog`, are not on it, and A06 allows them as any
  public domain (kernel-checked at the end of the file; scratch probe on the patched copy,
  2026-11-27). With the SDK's default client and no proxy, the resolver filters their resolved
  addresses (N09); with a custom HTTP client (`with_client`, upstream lines 1696–1698: "resolved
  addresses are not filtered") or through a proxy (`metadata_resolver.rs` lines 10–11: "Configured
  proxy hosts are not filtered"; the proxy resolves the target name), this name check is the
  only guard.

**URLs.** `url::Url` is abstract. Its components enter only as the unopened opaque values of the
trusted models (human decisions 2026-11-25 and AD4): `ExtModel.urlScheme`, `urlHost`,
`urlHostStr`, `urlPath`, `urlFragment`, `urlPort`, `urlSerialization`, `urlParse`, `urlJoin`,
`issuerUrl`. No definition states a law about them or a relation between them (for example that
`urlHost` and `urlHostStr` agree).

**Strings.** A Rust `&str` or `String` is described by its UTF-8 bytes (`Defs.utf8Bytes`).
Host names reuse `Defs.MetadataResolver.normalizeHost` and `isLocalhostName` (N11, N04), and IP
literals `Defs.Net` (A01–A03) and `Defs.MetadataResolver.addressClass` (N01).

**Line citations.** "upstream" is `auth.rs` at `7caec76` (unmodified in the repository);
"patched" is the copy with translation patches 01–06 (blob `dad471b`), from which the
translation is made (the `Source:` lines of `Rmcp.Funs`). Patch 06 moves A08–A10 into the
`check_*` helpers and adds `is_allowed_disallowed_host`, `trim_root_slash` and `is_root_url`;
both line numbers are given where they differ.
-/

namespace Defs.AuthMetadata

open Aeneas.Std Defs.Net Defs.MetadataResolver
open rmcp
open rmcp.transport.auth.metadata_resolver (AddressClass)
open rmcp.transport.auth (IssuerError ProtectedResourceMetadataInvalidReason)

/-! ## URLs (A04, `is_same_origin`) -/

/-- **An `http` or `https` scheme**: the bytes are `http` or `https` (upstream line 1331,
`matches!(url.scheme(), "http" | "https")`, a byte comparison). -/
def isHttpScheme (scheme : List U8) : Bool :=
  decide (scheme = utf8Bytes "http") || decide (scheme = utf8Bytes "https")

/-- **An HTTP(S) URL with a host** (A04 `is_http_url`, upstream lines 1330–1332, patched
1325–1327): its scheme is `http` or `https` and it has a host string (`host_str().is_some()`). -/
def isHttpUrl (u : url.Url) : Bool :=
  isHttpScheme (ExtModel.urlScheme u).val && (ExtModel.urlHostStr u).isSome

/-- **The default port of a scheme known to the `url` crate** (`url-2.5.9/src/parser.rs` lines
185–192, `default_port`): 80 for `http` and `ws`, 443 for `https` and `wss`, 21 for `ftp`,
otherwise none. The same table as the trusted `ExtModel.defaultPort`, on which the model of
`Url::port_or_known_default` is built (bridge law `knownDefaultPort_eq_defaultPort`). -/
def knownDefaultPort (scheme : List U8) : Option U16 :=
  if scheme = utf8Bytes "http" ∨ scheme = utf8Bytes "ws" then some 80#u16
  else if scheme = utf8Bytes "https" ∨ scheme = utf8Bytes "wss" then some 443#u16
  else if scheme = utf8Bytes "ftp" then some 21#u16
  else none

/-- **`Url::port_or_known_default`** (`url-2.5.9/src/lib.rs` lines 1300–1302): the explicit
port, otherwise the default port of the scheme. -/
def portOrKnownDefault (u : url.Url) : Option U16 :=
  (ExtModel.urlPort u).or (knownDefaultPort (ExtModel.urlScheme u).val)

/-- **Same origin** (`is_same_origin`, upstream lines 1334–1341, patched 1329–1336): equal
scheme bytes; both URLs have a host string, and the two are equal up to ASCII case
(`str::eq_ignore_ascii_case`); and equal port or known default port. -/
def isSameOrigin (base candidate : url.Url) : Bool :=
  decide ((ExtModel.urlScheme base).val = (ExtModel.urlScheme candidate).val) &&
    (match ExtModel.urlHostStr base, ExtModel.urlHostStr candidate with
      | some b, some c => decide (b.val.map asciiToLower = c.val.map asciiToLower)
      | _, _ => false) &&
    decide (portOrKnownDefault base = portOrKnownDefault candidate)

/-- **The domain of every host the URL has is UTF-8** (UTF-8 premise, rule (ii)(b) of
`ExtModel.IsUtf8`: `Url::host` returns a `Host<&str>`, whose domain is a Rust `&str`). True of
every `url::Url`; needed because `ExtModel.urlHost` is opaque and `to_ascii_lowercase` fails on
bytes that are not UTF-8. -/
def HostUtf8 (u : url.Url) : Prop :=
  ∀ d, ExtModel.urlHost u = some (url.host.Host.Domain d) → ExtModel.IsUtf8 d.val

/-! ## The metadata host guard (A05) -/

/-- **The cloud-metadata host names** (the constant `CLOUD_METADATA_HOSTS`, upstream lines
39–43, inlined by the first hunk of patch 06 (hunk H1 in the patch header) into `matches!` at
patched lines 1383–1386): `metadata`, `metadata.google.internal`, `metadata.azure.internal`, as
bytes.

H16 (human decision 2026-11-27, recorded bug): only these three names; other metadata names,
for example `instance-data` or `metadata.goog`, are not on the list (kernel-checked at the end of
the file). With a custom HTTP client or through a proxy, the name check of A05 is the only guard
for a domain target (module docstring). -/
def cloudMetadataHosts : List (List U8) :=
  [utf8Bytes "metadata", utf8Bytes "metadata.google.internal",
    utf8Bytes "metadata.azure.internal"]

/-- **A cloud-metadata name** (the third disjunct of `is_disallowed_metadata_hostname`, upstream
line 1388, on the name `is_disallowed_metadata_host` passes, line 1394): after removing trailing
dots and lowercasing ASCII letters (`normalizeHost`), one of `cloudMetadataHosts`. H16 (recorded
bug): a name off that three-name list, such as `instance-data` or `metadata.goog`, is not one. -/
def isCloudMetadataName (domain : List U8) : Bool :=
  decide (normalizeHost domain ∈ cloudMetadataHosts)

/-- **A host name the metadata guard rejects** (`is_disallowed_metadata_hostname`, upstream lines
1385–1389, patched 1380–1387, on the bytes of its argument, which is already normalized by its
one caller): `localhost`, a name ending in `.localhost`, or a cloud-metadata name; compared
byte for byte (`matches!` and `str::ends_with` on `&str`). -/
def isDisallowedHostname (host : List U8) : Bool :=
  decide (host = utf8Bytes "localhost") || decide (utf8Bytes ".localhost" <:+ host) ||
    decide (host ∈ cloudMetadataHosts)

/-- **A host the metadata guard rejects** (A05 `is_disallowed_metadata_host`, upstream lines
1391–1399, patched 1389–1397, with `is_disallowed_metadata_hostname`, upstream 1385–1389,
patched 1380–1387): a domain that, after normalization, is `localhost`, ends in `.localhost`
(`isLocalhostName`) or is a cloud-metadata name (`isCloudMetadataName`); an IPv4 literal that
A02 blocks; an IPv6 literal that A03 blocks.

H11 (human decision 2026-11-27, recorded bug): the IPv4-translated range `::ffff:0:0:0/96`
(RFC 2765 §2.1; such as `::ffff:0:a9fe:a9fe` and `::ffff:0:7f00:1`, which carry no A01
embedding), `100::/64` and `192.0.0.192` are not rejected (and have class `Public`, N01);
kernel-checked at the end of the file. The resolver also accepts DNS answers in these ranges
(class `Public`, N09). -/
def isDisallowedHost : url.host.Host Str → Bool
  | .Domain d => isLocalhostName d.val || isCloudMetadataName d.val
  | .Ipv4 a => ipv4Disallowed (ipv4Value a.addrOctets.val)
  | .Ipv6 a => ipv6Disallowed (ipv6Value a.addrSegments.val)

/-! ## The metadata URL policy (A06) -/

/-- **A rejected host allowed all the same** (patch helper `is_allowed_disallowed_host`, patched
lines 1433–1447; upstream lines 1425–1435 of `is_allowed_metadata_url`): with `allowPrivate`, an
IP literal of class `Private` (N01; a domain has no class); otherwise, a loopback host
(`isLoopbackHost`: `localhost` name, `127/8`, `::1`) when the base URL's host is a loopback host
as well.

H10 (human decision 2026-11-27, recorded bug): with `allowPrivate`, every `Private` literal is
allowed, the cloud-metadata endpoints in private ranges included (`100.100.100.200` in
`100.64/10`, `fd00:ec2::254` in `fc00::/7`); kernel-checked at the end of the file. The resolver
does the same: whenever it grants `Private`, with `allowing_private_addresses` (N06) or from a
`Private`-literal base (N04), it accepts DNS answers in these ranges (N09). -/
def isAllowedDisallowedHost (baseHost : Option (url.host.Host Str)) (host : url.host.Host Str)
    (allowPrivate : Bool) : Bool :=
  (allowPrivate && decide ((hostIp host).map addressClass = some AddressClass.Private)) ||
    (baseHost.any isLoopbackHost && isLoopbackHost host)

/-- **Whether a metadata URL is allowed** (A06 `is_allowed_metadata_url`, upstream lines
1412–1436, patched 1410–1430): the URL is HTTP(S) with a host string (A04) and has a host; the
host is not rejected by the guard (A05), or is allowed by `isAllowedDisallowedHost`. The laws
`isAllowedMetadataUrl_eq_…` give its value for each kind of host without premises.

H12 (human decision 2026-11-27, recorded bug): for some targets (IP literals, and a localhost
name from a base that is an IPv6 embedding of `127/8`) this refuses what the resolver policy
(N04/N07) allows; for IP-literal targets it is never looser than the resolver (law
`allowsHost_of_isAllowedMetadataUrl`; kernel-checked host-level cases at the end of the file).
The cases are listed once, in the module docstring.

H14 (human decision 2026-11-27, recorded bug of the resolver): the resolver allows the base
URL's own IP literal even when its class is `Blocked`; this function refuses it (the guard
rejects it, it is not `Private` and not a loopback host). Details in the module docstring;
kernel-checked at the end of the file for `169.254.1.1` and `0.0.0.0`.
-/
def isAllowedMetadataUrl (base target : url.Url) (allowPrivate : Bool) : Bool :=
  isHttpUrl target &&
    match ExtModel.urlHost target with
    | none => false
    | some h =>
      !isDisallowedHost h || isAllowedDisallowedHost (ExtModel.urlHost base) h allowPrivate

/-! ## Resource metadata URLs (A07) -/

/-- **A Unicode `White_Space` character** (`char::is_whitespace`, `core/src/char/methods.rs`
lines 1088–1094, Unicode 17.0.0 `PropList.txt`): U+0009–U+000D, U+0020, U+0085, U+00A0, U+1680,
U+2000–U+200A, U+2028, U+2029, U+202F, U+205F, U+3000. -/
def isUnicodeWhitespace (c : Char) : Bool :=
  decide (c.toNat ∈ [0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x20, 0x85, 0xA0, 0x1680, 0x2000, 0x2001,
    0x2002, 0x2003, 0x2004, 0x2005, 0x2006, 0x2007, 0x2008, 0x2009, 0x200A, 0x2028, 0x2029,
    0x202F, 0x205F, 0x3000])

/-- **`str::trim`** on a string (`core/src/str/mod.rs` lines 2186–2188): without its leading and
trailing `White_Space` characters (`isUnicodeWhitespace`). The trusted model
`ExtModel.trimWhitespace` computes it on the UTF-8 bytes (law `trimWhitespace_utf8Bytes` of
`Proofs.External.Auth`). -/
def trimUnicodeWhitespace (s : String) : String :=
  String.ofList ((s.toList.dropWhile isUnicodeWhitespace).rdropWhile isUnicodeWhitespace)

/-- **The URL a `resource_metadata` value names** (A07, upstream lines 1444–1456; patched
1456–1471): the value is trimmed (`ExtModel.trimWhitespace`, the model of `str::trim` on bytes,
which needs no UTF-8 premise); an empty value names none (line 1445); otherwise the value parsed
as an absolute URL, or, if that fails, resolved against `base` (`Url::join`), or none if both
fail. -/
def metadataCandidate (value : List U8) (base : url.Url) : Option url.Url :=
  let v := ExtModel.trimWhitespace value
  if v = [] then none
  else
    match ExtModel.urlParse v with
    | .Ok u => some u
    | .Err _ =>
      match ExtModel.urlJoin base v with
      | .Ok u => some u
      | .Err _ => none

/-- **The resource metadata URL accepted** (A07 `resolve_resource_metadata_url`, upstream lines
1439–1473, patched 1451–1486): the candidate (`metadataCandidate`) if it is HTTP(S) with a host
and same-origin with the base URL (upstream lines 1458–1460); otherwise none if the base URL is
`https` and the candidate's scheme is not (lines 1461–1464, the downgrade check); otherwise the
candidate if the metadata URL policy allows it (A06, lines 1465–1472), else none. -/
def resolveResourceMetadataUrl (value : List U8) (base : url.Url) (allowPrivate : Bool) :
    Option url.Url :=
  (metadataCandidate value base).bind fun u =>
    if isHttpUrl u && isSameOrigin base u then some u
    else if decide ((ExtModel.urlScheme base).val = utf8Bytes "https") &&
        !decide ((ExtModel.urlScheme u).val = utf8Bytes "https") then none
    else if isAllowedMetadataUrl base u allowPrivate then some u
    else none

/-! ## The callback issuer (A08) -/

/-- The message of `AuthorizationFailed` (upstream line 2327). -/
def issuerNotRecordedMessage : String :=
  "Authorization callback issuer cannot be validated because expected issuer was not recorded"

/-- **The string with the UTF-8 bytes `l`** (`str::to_owned` of a `&str`, the trusted model
`Str.Insts.AllocBorrowToOwnedString.to_owned`); the empty string, a junk value, if `l` is not
UTF-8. The junk value never occurs under the premises of the statements: a Rust `&str` is
UTF-8, and each statement whose conclusion depends on the value of `stringOfUtf8 l` either
assumes `l` is UTF-8 (premises (U), (R)) or covers only successful calls, which imply it. -/
def stringOfUtf8 (l : List U8) : String :=
  (ExtModel.strOfBytes? l).getD ""

/-- **The result of the callback issuer check** (A08 `check_authorization_response_issuer`,
patched lines 2342–2375; the body of `validate_authorization_response_issuer`, upstream lines
2320–2353), for the recorded expected issuer, `require_issuer` and the bytes of the received
`iss`, in the Rust order of checks: without a recorded issuer, `AuthorizationFailed` if an issuer
was received or one is required (upstream lines 2324–2330), otherwise `Ok` (line 2334); without
a received issuer, `AuthorizationServerMissingIssuer` if one is required (lines 2336–2341),
otherwise `Ok` (line 2344); otherwise `Ok` exactly when the received bytes are those of the
expected issuer (RFC 9207 §2.4, simple string comparison), else
`AuthorizationServerMismatch` with both issuers (lines 2346–2351). -/
def responseIssuerCheck (expected : Option String) (requireIssuer : Bool)
    (received : Option (List U8)) : core.result.Result Unit IssuerError :=
  match expected, received with
  | none, received =>
    if received.isSome || requireIssuer then
      .Err (.AuthorizationFailed issuerNotRecordedMessage)
    else .Ok ()
  | some e, none =>
    if requireIssuer then .Err (.AuthorizationServerMissingIssuer e) else .Ok ()
  | some e, some r =>
    if r = utf8Bytes e then .Ok ()
    else .Err (.AuthorizationServerMismatch e (stringOfUtf8 r))

/-! ## The metadata issuer (A09) -/

/-- The RFC 8414 well-known path `/.well-known/oauth-authorization-server` (upstream line 2747). -/
def oauthWellKnown : List U8 := utf8Bytes "/.well-known/oauth-authorization-server"

/-- The OpenID Connect discovery path `/.well-known/openid-configuration` (upstream line 2748). -/
def oidcWellKnown : List U8 := utf8Bytes "/.well-known/openid-configuration"

/-- The byte `/` (47). -/
def slashByte : U8 := 47#u8

/-- **The issuer path of a discovery path** (`expected_issuer_for_authorization_metadata_url`,
upstream lines 2746–2763, patched 2768–2783): `[]` for exactly the RFC 8414 or the OpenID
Connect well-known path; the rest after `oauthWellKnown ++ "/"` (RFC 8414 §3.1 path insertion);
the rest after `oidcWellKnown ++ "/"` (the MCP path-insertion form of OpenID Connect); the part
before a final `oidcWellKnown` without its leading `/` bytes (OpenID Connect Discovery 1.0 §4,
path appended); otherwise none (no derivable issuer).

H9: a recorded issue in this check, under private disclosure; details withheld until it is
reported. -/
def issuerPath (path : List U8) : Option (List U8) :=
  if path = oauthWellKnown ∨ path = oidcWellKnown then some []
  else if oauthWellKnown ++ [slashByte] <+: path then some (path.drop (oauthWellKnown.length + 1))
  else if oidcWellKnown ++ [slashByte] <+: path then some (path.drop (oidcWellKnown.length + 1))
  else if oidcWellKnown <:+ path then
    some ((path.take (path.length - oidcWellKnown.length)).dropWhile (· = slashByte))
  else none

/-- **The issuer derived from a discovery URL** (`expected_issuer_for_authorization_metadata_url`,
upstream lines 2745–2774, patched 2767–2788): none without an issuer path (`issuerPath`);
otherwise `ExtModel.issuerUrl u p` for the issuer path `p`, the opaque value of
`prim::issuer_url` (patched lines 4567–4577; see the docstring of `ExtModel.issuerUrl`): a copy
of the discovery URL without query and fragment whose path is set by `Url::set_path`
(url-2.5.9 `src/lib.rs` lines 1766–1789) to the empty string if `p` is empty, otherwise to `/`
followed by `p`, then serialized. The setter parses the new path as the parser does
(`src/parser.rs` lines 1133–1170, `parse_path_start`): for a special scheme such as `https` an
empty path is written as `/` (line 1148), so `https://as.example/.well-known/openid-configuration`
gives `https://as.example/`, while for a non-special scheme it stays empty (`foo://h`); and the
leading `/` is added to `p` as it is, so the issuer path `/x` (discovery path
`/.well-known/oauth-authorization-server//x`) gives `https://as.example//x` (scratch probes on
the patched copy, url 2.5.9, 2026-11-27). -/
def derivedIssuer (discoveryUrl : url.Url) : Option String :=
  (issuerPath (ExtModel.urlPath discoveryUrl).val).map (ExtModel.issuerUrl discoveryUrl)

/-- **The expected issuer of the metadata check** (patched lines 2835–2838; upstream 2802–2804):
the explicit expected issuer if given (as a string; `str::to_owned`), otherwise the issuer
derived from the discovery URL. -/
def expectedIssuerOf (explicit : Option (List U8)) (discoveryUrl : url.Url) : Option String :=
  match explicit with
  | some s => some (stringOfUtf8 s)
  | none => derivedIssuer discoveryUrl

/-- **A root URL** (patch helper `is_root_url`, patched lines 2807–2812; the `filter` closure of
upstream lines 2784–2788): the bytes parse as a URL whose path is empty or `/` (query and
fragment allowed). -/
def isRootUrl (v : List U8) : Bool :=
  match ExtModel.urlParse v with
  | .Ok p =>
    decide ((ExtModel.urlPath p).val = []) || decide ((ExtModel.urlPath p).val = [slashByte])
  | .Err _ => false

/-- **An issuer without the slash of a root URL** (patch helper `trim_root_slash`, patched lines
2798–2805; the closure of upstream lines 2781–2791): the issuer without its final `/` if what
remains is a root URL (`isRootUrl`), otherwise unchanged. The `/` removed may be the last byte
of a query or a fragment: `https://as.example?x/` gives `https://as.example?x` (H15; not
kernel-checkable, `isRootUrl` reaches the opaque `ExtModel.urlParse`; scratch probe on the
patched copy, 2026-11-27). -/
def trimRootSlash (issuer : List U8) : List U8 :=
  if [slashByte] <:+ issuer ∧ isRootUrl issuer.dropLast = true then issuer.dropLast else issuer

/-- **Matching issuer identifiers** (`issuer_identifiers_match`, upstream lines 2776–2794, patched
2790–2796): equal bytes, or equal after `trimRootSlash` on both, which removes a final `/` when
what remains parses as a URL whose path is empty or `/` (query and fragment allowed).

H15 (human decision 2026-11-27, recorded bug): the tolerance of a root `/` deviates from the
"identical" of RFC 8414 §3.3; the upstream test
`authorization_metadata_allows_only_root_trailing_slash_equivalence` (lines 5141–5151) asserts
it (`https://auth.example.com/` matches `https://auth.example.com`). The `/` removed may end a
query or a fragment: `issuer_identifiers_match("https://as.example?x/", "https://as.example?x")`
is true, and so with the fragment `f/` against `f` (scratch probe on the patched copy,
2026-11-27; not kernel-checkable, `isRootUrl` reaches the opaque `ExtModel.urlParse`). Law
`eq_or_eq_append_slash_of_issuersMatch`. -/
def issuersMatch (received expected : List U8) : Bool :=
  decide (received = expected) || decide (trimRootSlash received = trimRootSlash expected)

/-- **The result of the metadata issuer check** (A09 `check_authorization_metadata_issuer`,
patched lines 2829–2855; the body of `validate_authorization_metadata_issuer`, upstream lines
2796–2821), for `allow_missing_issuer`, the expected issuer (`expectedIssuerOf`) and the
metadata's `issuer`, in the Rust order of checks: `Ok` without an expected issuer (upstream
line 2806); without a received issuer, `Ok` if `allowMissingIssuer` (line 2810), otherwise
`AuthorizationServerMissingIssuer` (line 2812); otherwise `Ok` if the issuers match
(`issuersMatch`), else `AuthorizationServerMismatch` with both (lines 2814–2818).

H9: a recorded issue in this check, under private disclosure; details withheld until it is
reported. -/
def metadataIssuerCheck (allowMissingIssuer : Bool) (expected : Option String)
    (received : Option String) : core.result.Result Unit IssuerError :=
  match expected, received with
  | none, _ => .Ok ()
  | some e, none =>
    if allowMissingIssuer then .Ok () else .Err (.AuthorizationServerMissingIssuer e)
  | some e, some r =>
    if issuersMatch (utf8Bytes r) (utf8Bytes e) then .Ok ()
    else .Err (.AuthorizationServerMismatch e r)

/-- **The discovery URL fits the issuer rewriting** (AD7 premise; stated exception of the model
`transport.auth.prim.issuer_url`): its serialization has at most `u32::MAX` bytes. For a longer
discovery URL without query and fragment, Rust panics in `Url::set_path`
(`to_u32(..).unwrap()`, url-2.5.9 `src/lib.rs` line 1768) and the model returns `ok`; the
statements of A09 that promise no failure take this premise (human decision AD7) although the
model does not need it.

The premise is stronger than the exact panic condition, which is: no explicit expected issuer,
an issuer path exists (`issuerPath ≠ none`, so `prim::issuer_url` runs), the discovery URL has
neither query nor fragment, and its serialization is longer than `u32::MAX` bytes. A discovery
URL with a query or fragment, or without an issuer path, never panics whatever its length; the
premise excludes those long URLs too (human decision 2026-11-27: the simple bound is accepted).
-/
def DiscoveryUrlFits (discoveryUrl : url.Url) : Prop :=
  (ExtModel.urlSerialization discoveryUrl).utf8ByteSize ≤ U32.max

/-! ## The resource identifier (A10) -/

/-- **The actual path covers the expected path** (the path part of
`is_resource_identifier_valid`, upstream lines 3010–3021, patched 3052–3062): equal bytes, or
the actual path is a byte prefix of the expected path ending at a segment boundary: it ends in
`/`, or the expected path has `/` right after it. -/
def pathCovers (expectedPath actualPath : List U8) : Bool :=
  decide (expectedPath = actualPath) ||
    (decide (actualPath <+: expectedPath) &&
      (decide ([slashByte] <:+ actualPath) ||
        decide (expectedPath[actualPath.length]? = some slashByte)))

/-- **A valid resource identifier** (`is_resource_identifier_valid`, upstream lines 2998–3021,
patched 3040–3063): equal serializations (`Url` equality, upstream line 2999); otherwise equal
scheme bytes, equal host strings (both absent or the same bytes), equal port or known default
port, and an actual path that covers the expected path (`pathCovers`). Query, fragment and user
information are not compared.

H13 (human decision 2026-11-27, recorded bug): this accepts an actual identifier with an
ancestor path, a different query or different user information, looser than the "identical"
of RFC 9728 §3.3; the query rule is deliberate (comment at upstream line 3013), and so is the
ancestor rule (test `resource_identifier_matching_allows_matching_host_or_parent_path`, upstream
lines 7148–7215). Not part of H13: it rejects the expected path with a final `/` added (`/mcp/`
for `/mcp`), which agrees with RFC 9728 §3.3 and with the same test (lines 7187–7190) but is
inconsistent with the ancestor rule. -/
def isResourceIdentifierValid (expected actual : url.Url) : Bool :=
  decide (ExtModel.urlSerialization expected = ExtModel.urlSerialization actual) ||
    (decide ((ExtModel.urlScheme expected).val = (ExtModel.urlScheme actual).val) &&
      decide ((ExtModel.urlHostStr expected).map (·.val) =
        (ExtModel.urlHostStr actual).map (·.val)) &&
      decide (portOrKnownDefault expected = portOrKnownDefault actual) &&
      pathCovers (ExtModel.urlPath expected).val (ExtModel.urlPath actual).val)

/-- **The result of the resource check** (A10 `check_resource_metadata_resource`, patched lines
3001–3037; the body of `validate_resource_metadata_resource`, upstream lines 2960–2996), for the
base URL and the metadata's `resource`, in the Rust order of checks: `MissingResource` without a
resource (upstream lines 2964–2967); `ResourceNotAUrl` with the resource if it does not parse
(lines 2970–2975); `ResourceHasFragment` with the parsed URL if it has a fragment (lines
2978–2983, RFC 8707 §2); `ResourceMismatch` with the base URL and the parsed URL if it is not a
valid identifier of the base URL (lines 2986–2992); otherwise `Ok` (line 2995). -/
def resourceCheck (base : url.Url) (resource : Option String) :
    core.result.Result Unit ProtectedResourceMetadataInvalidReason :=
  match resource with
  | none => .Err .MissingResource
  | some r =>
    match ExtModel.urlParse (utf8Bytes r) with
    | .Err _ => .Err (.ResourceNotAUrl r)
    | .Ok u =>
      if (ExtModel.urlFragment u).isSome then .Err (.ResourceHasFragment u)
      else if isResourceIdentifierValid base u then .Ok ()
      else .Err (.ResourceMismatch base u)

/-! ## Regression checks

Kernel-checked evaluations of the definitions that do not reach an opaque value, on boundary
cases (plan Section 22 style). -/

/-- The IPv4 literal host `a.b.c.d` (used only by the checks). -/
private def v4Host (a b c d : Nat) : url.host.Host Str :=
  .Ipv4 ⟨Array.make 4#usize ([a, b, c, d].map (fun n => ⟨BitVec.ofNat 8 n⟩))⟩

/-- The IPv6 literal host with segments `s` (used only by the checks). -/
private def v6Host (s₀ s₁ s₂ s₃ s₄ s₅ s₆ s₇ : Nat) : url.host.Host Str :=
  .Ipv6 ⟨Array.make 8#usize
    ([s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇].map (fun n => ⟨BitVec.ofNat 16 n⟩))⟩

-- A05, names: case, trailing dots, `localhost` names and the three cloud names are rejected;
-- `metadata.goog`, `instance-data` and a subdomain of a cloud name are not (H16, recorded bug:
-- the list has only three names).
example : [isDisallowedHost (.Domain (toStr "METADATA.")),
    isDisallowedHost (.Domain (toStr "metadata.google.internal..")),
    isDisallowedHost (.Domain (toStr "Metadata.Azure.Internal")),
    isDisallowedHost (.Domain (toStr "localhost.")),
    isDisallowedHost (.Domain (toStr "a.localhost")),
    isDisallowedHost (.Domain (toStr "metadata.goog")),
    isDisallowedHost (.Domain (toStr "instance-data")),
    isDisallowedHost (.Domain (toStr "foo.metadata.google.internal")),
    isDisallowedHost (.Domain (toStr "auth.example.com"))] =
    [true, true, true, true, true, false, false, false, false] := by
  decide +kernel

-- A05, literals: `169.254.169.254`, `100.100.100.200`, `127.0.0.1`, `10.0.0.9` and the IPv6
-- literals `::ffff:169.254.169.254`, `64:ff9b::a9fe:a9fe`, `fd00:ec2::254`, `fe80::a9fe:a9fe`
-- are rejected; `93.184.216.34`, `240.0.0.1` (H8) and the IPv4-translated form
-- `::ffff:0:a9fe:a9fe` (not an A01 embedding) are not.
example : [isDisallowedHost (v4Host 169 254 169 254), isDisallowedHost (v4Host 100 100 100 200),
    isDisallowedHost (v4Host 127 0 0 1), isDisallowedHost (v4Host 10 0 0 9),
    isDisallowedHost (v6Host 0 0 0 0 0 0xffff 0xa9fe 0xa9fe),
    isDisallowedHost (v6Host 0x64 0xff9b 0 0 0 0 0xa9fe 0xa9fe),
    isDisallowedHost (v6Host 0xfd00 0xec2 0 0 0 0 0 0x254),
    isDisallowedHost (v6Host 0xfe80 0 0 0 0 0 0xa9fe 0xa9fe),
    isDisallowedHost (v4Host 93 184 216 34), isDisallowedHost (v4Host 240 0 0 1),
    isDisallowedHost (v6Host 0 0 0 0 0xffff 0 0xa9fe 0xa9fe)] =
    [true, true, true, true, true, true, true, true, false, false, false] := by
  decide +kernel

-- A06 helper: with `allowPrivate`, the private literals `10.0.0.9`, `100.100.100.200` and
-- `fd00:ec2::254` pass; `169.254.169.254` and a cloud name never do; a loopback target passes
-- only from a loopback base, and `::ffff:127.0.0.1` (class `Loopback`, not `::1`) never does.
example :
    let pub : Option (url.host.Host Str) := some (.Domain (toStr "mcp.example.com"))
    let lo : Option (url.host.Host Str) := some (.Domain (toStr "localhost"))
    [isAllowedDisallowedHost pub (v4Host 10 0 0 9) true,
     isAllowedDisallowedHost pub (v4Host 100 100 100 200) true,
     isAllowedDisallowedHost pub (v6Host 0xfd00 0xec2 0 0 0 0 0 0x254) true,
     isAllowedDisallowedHost pub (v4Host 10 0 0 9) false,
     isAllowedDisallowedHost lo (v4Host 169 254 169 254) true,
     isAllowedDisallowedHost lo (.Domain (toStr "metadata")) true,
     isAllowedDisallowedHost lo (v4Host 127 0 0 1) false,
     isAllowedDisallowedHost pub (v4Host 127 0 0 1) true,
     isAllowedDisallowedHost lo (v6Host 0 0 0 0 0 0xffff 0x7f00 1) true] =
    [true, true, true, false, false, false, true, false, false] := by
  decide +kernel

-- H10 and H11 (recorded bugs): `100.100.100.200` and `fd00:ec2::254` have class `Private`, so
-- `isAllowedDisallowedHost` allows them with `allowPrivate` (above); `::ffff:0:a9fe:a9fe`,
-- `::ffff:0:7f00:1`, `100::1` and `192.0.0.192` have class `Public` and are not rejected.
example :
    [(hostIp (v4Host 100 100 100 200)).map addressClass,
     (hostIp (v6Host 0xfd00 0xec2 0 0 0 0 0 0x254)).map addressClass,
     (hostIp (v6Host 0 0 0 0 0xffff 0 0xa9fe 0xa9fe)).map addressClass,
     (hostIp (v6Host 0 0 0 0 0xffff 0 0x7f00 1)).map addressClass,
     (hostIp (v6Host 0x100 0 0 0 0 0 0 1)).map addressClass,
     (hostIp (v4Host 192 0 0 192)).map addressClass] =
    [some .Private, some .Private, some .Public, some .Public, some .Public, some .Public] ∧
    [isDisallowedHost (v6Host 0 0 0 0 0xffff 0 0x7f00 1),
     isDisallowedHost (v6Host 0x100 0 0 0 0 0 0 1), isDisallowedHost (v4Host 192 0 0 192)] =
    [false, false, false] := by
  decide +kernel

-- H12 (recorded bug), at the level of hosts: the A06 exemption of a rejected literal and the
-- resolver policy (`allowsHost`, N07, with the classes of N04) differ for an IPv6 embedding of
-- `127.0.0.1` (IPv4-mapped `::ffff:127.0.0.1`, IPv4-compatible `::7f00:1`, NAT64
-- `64:ff9b::7f00:1`, 6to4 `2002:7f00:1::`) as the target from a `localhost` base and as the
-- base with a `127.0.0.1` target, and for a `10.0.0.2` or `fd00::1` target from a `10.0.0.1` or
-- `::ffff:10.0.0.1` base without `allowPrivate`: the guard rejects the target, A06 refuses, the
-- resolver allows.
example :
    let lo : Option (url.host.Host Str) := some (.Domain (toStr "localhost"))
    let embeddings : List (url.host.Host Str) :=
      [v6Host 0 0 0 0 0 0xffff 0x7f00 1, v6Host 0 0 0 0 0 0 0x7f00 1,
       v6Host 0x64 0xff9b 0 0 0 0 0x7f00 1, v6Host 0x2002 0x7f00 1 0 0 0 0 0]
    embeddings.all (fun e =>
      isDisallowedHost e && !isAllowedDisallowedHost lo e false &&
        !isAllowedDisallowedHost (some e) (v4Host 127 0 0 1) false &&
        allowsHost (literalIp lo) (baseClasses lo) (some e) &&
        allowsHost (literalIp (some e)) (baseClasses (some e)) (some (v4Host 127 0 0 1))) =
      true := by
  decide +kernel

example :
    let privs : List (url.host.Host Str) := [v4Host 10 0 0 1, v6Host 0 0 0 0 0 0xffff 0x0a00 1]
    let targets : List (url.host.Host Str) := [v4Host 10 0 0 2, v6Host 0xfd00 0 0 0 0 0 0 1]
    (privs.all fun b => targets.all fun t =>
      isDisallowedHost t && !isAllowedDisallowedHost (some b) t false &&
        allowsHost (literalIp (some b)) (baseClasses (some b)) (some t)) = true := by
  decide +kernel

-- H14 (recorded bug of the resolver): for a `Blocked` base literal (`169.254.1.1`, `0.0.0.0`),
-- the resolver allows the same literal as a target (the `baseIp = some ip` disjunct of
-- `allowsHost`), with or without `Private`; the guard rejects it and the A06 exemption refuses
-- it whatever `allowPrivate`.
example :
    let blocked : List (url.host.Host Str) := [v4Host 169 254 1 1, v4Host 0 0 0 0]
    (blocked.all fun b =>
      decide ((hostIp b).map addressClass = some .Blocked) && isDisallowedHost b &&
        !isAllowedDisallowedHost (some b) b false && !isAllowedDisallowedHost (some b) b true &&
        allowsHost (literalIp (some b)) (baseClasses (some b)) (some b) &&
        allowsHost (literalIp (some b)) (withPrivate (baseClasses (some b))) (some b)) =
      true := by
  decide +kernel

-- A07, `str::trim`: ASCII and Unicode white space at both ends (U+00A0, U+3000, U+2028), the
-- inner space kept; U+200B (zero width space) is not White_Space and is kept.
example : trimUnicodeWhitespace " \t a b\u00A0\u3000\n" = "a b" ∧
    trimUnicodeWhitespace " \u2028 " = "" ∧
    trimUnicodeWhitespace "\u200Bx" = "\u200Bx" := by
  decide +kernel

-- A08: the outcomes of RFC 9207 checking (no recorded issuer: an error if one is received;
-- a recorded issuer: missing only if required, equal bytes accepted).
example : responseIssuerCheck none false none = .Ok () := rfl

example : responseIssuerCheck none false (some (utf8Bytes "https://as")) =
    .Err (.AuthorizationFailed issuerNotRecordedMessage) := rfl

example : responseIssuerCheck (some "https://as") true none =
    .Err (.AuthorizationServerMissingIssuer "https://as") := rfl

example : responseIssuerCheck (some "https://as") false none = .Ok () := rfl

example :
    responseIssuerCheck (some "https://as") true (some (utf8Bytes "https://as")) = .Ok () := by
  rw [responseIssuerCheck, ite_eq_left rfl]

-- A09, the issuer path of the four discovery forms.
example :
    issuerPath (utf8Bytes "/.well-known/oauth-authorization-server") = some [] ∧
    issuerPath (utf8Bytes "/.well-known/openid-configuration") = some [] ∧
    issuerPath (utf8Bytes "/.well-known/oauth-authorization-server/") = some [] ∧
    issuerPath (utf8Bytes "/.well-known/oauth-authorization-server/t1") = some (utf8Bytes "t1") ∧
    issuerPath (utf8Bytes "/.well-known/oauth-authorization-server/t/") = some (utf8Bytes "t/") ∧
    issuerPath (utf8Bytes "/.well-known/openid-configuration/t1") = some (utf8Bytes "t1") ∧
    issuerPath (utf8Bytes "/t1/.well-known/openid-configuration") = some (utf8Bytes "t1") ∧
    issuerPath (utf8Bytes "//x/.well-known/openid-configuration") = some (utf8Bytes "x") := by
  decide +kernel

-- A10, `pathCovers`: equal paths, `/` covers every path, `/mcp` covers `/mcp/sub`; `/mc` does
-- not cover `/mcp`, `/mcp/` does not cover `/mcp`, and the empty path covers `/mcp`.
example :
    [pathCovers (utf8Bytes "/mcp") (utf8Bytes "/mcp"),
     pathCovers (utf8Bytes "/mcp") (utf8Bytes "/"),
     pathCovers (utf8Bytes "/mcp/sub") (utf8Bytes "/mcp"),
     pathCovers (utf8Bytes "/mcp") (utf8Bytes "/mc"),
     pathCovers (utf8Bytes "/mcp") (utf8Bytes "/mcp/"), pathCovers (utf8Bytes "/mcp") []] =
    [true, true, true, false, false, true] := by
  decide +kernel

end Defs.AuthMetadata
