/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Proofs.Defs.AuthMetadata
public import Proofs.External.Auth
public import Proofs.Transport.MetadataResolver

@[expose] public section

/-!
# Helper lemmas for the OAuth metadata URL and issuer checks (A04–A10)

Equations and inversion lemmas for the translated private checks of `AuthorizationManager` in
`crates/rmcp/src/transport/auth.rs` (translation patch 06), used by the spec theorems in
`Proofs.Transport.AuthMetadata`:

- A04/A05: `is_http_url`, `is_disallowed_metadata_hostname` and `is_disallowed_metadata_host` as
  equations on `Defs.AuthMetadata` (a domain through `normalizeHost`, failing with `undef` when
  the normalized bytes are not UTF-8);
- A06: `is_allowed_disallowed_host` and `is_allowed_metadata_url` as equations, and the
  classification facts `ipv4Class_ne_public_iff`, `ipv6Class_ne_public_iff` (A02/A03 against N01);
- A07: `is_same_origin` (with the `Option` and `u16` equality instances and
  `port_or_known_default`) and `resolve_resource_metadata_url` as a match on `metadataCandidate`
  followed by `resolveTail`;
- A08/A09: `to_owned`, `is_root_url`, `trim_root_slash`, `issuer_identifiers_match`,
  `expected_issuer_for_authorization_metadata_url` and `check_authorization_metadata_issuer` as
  equations, with their failures (`undef` on bytes that are not UTF-8, `maximumSizeExceeded` on a
  `String` longer than `Usize.max`);
- A10: `is_resource_identifier_valid` and `check_resource_metadata_resource` as equations;
- the inversion of successful calls (`… = ok true`, `… = ok (some u)`), used by the "on success"
  compositions, which take no UTF-8 premise.

Two lemmas here are statements of `Proofs.Transport.AuthMetadata`
(`knownDefaultPort_eq_defaultPort`, `trim_root_slash_fail`): other lemmas need them before the
statement theorems, so they are proved here and the statement theorems are proved by them
(precedent `Proofs.Transport.MetadataResolver.Common`).

Source: "crates/rmcp/src/transport/auth.rs" (patched copy with patches 01–06, lines 1325–1486,
2342–2375 and 2767–3063; upstream `7caec76` lines 1330–1473 and 2320–2996)
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

set_option autoImplicit false

namespace Proofs.Transport.AuthMetadata

open rmcp.transport.auth.AuthorizationManager
open rmcp.transport.auth.AuthorizationManager.is_allowed_disallowed_host.closure.Insts
open rmcp.transport.auth.AuthorizationManager.is_same_origin.closure.Insts

/-! ## A04 `is_http_url` and A05 `is_disallowed_metadata_host` -/

theorem is_http_url_eq (target : url.Url) :
    is_http_url target = ok (isHttpUrl target) := by
  unfold is_http_url isHttpUrl isHttpScheme
  simp only [url.Url.scheme, bind_ok, Str.Insts.CoreCmpPartialEqStr.eq, url.Url.host_str]
  have h1 : ∀ h, (toStr "http" h).val = utf8Bytes "http" := fun h => toStr_val _ h
  have h2 : ∀ h, (toStr "https" h).val = utf8Bytes "https" := fun h => toStr_val _ h
  simp only [h1, h2]
  by_cases a : (urlScheme target).val = utf8Bytes "http" <;>
    by_cases b : (urlScheme target).val = utf8Bytes "https" <;> simp only [a, decide_true,
      ↓reduceIte, core.option.Option.is_some, bind_ok, Bool.true_or, Bool.true_and, b,
      decide_eq_true_eq, ite_self, Bool.or_true, decide_false, Bool.false_eq_true, Bool.or_self,
      Bool.false_and]

theorem is_disallowed_metadata_hostname_eq (host : Str) :
    is_disallowed_metadata_hostname host = ok (isDisallowedHostname host.val) := by
  unfold is_disallowed_metadata_hostname isDisallowedHostname cloudMetadataHosts
  simp only [Str.Insts.CoreCmpPartialEqStr.eq, transport.auth.metadata_resolver.prim.ends_with,
    toStr_val, ← utf8Bytes_eq_utf8]
  by_cases a : host.val = utf8Bytes "localhost" <;> simp only [a, decide_true, decide_false] <;>
    simp only [bind_ok, decide_eq_true_eq, ↓reduceIte, Bool.true_or, List.mem_cons,
      List.not_mem_nil, or_false, Bool.decide_or, Bool.false_eq_true, Bool.false_or]
  by_cases b : utf8Bytes ".localhost" <:+ host.val <;> simp only [b, ↓reduceIte, decide_true,
    Bool.true_or, decide_false, Bool.false_or]
  by_cases c : host.val = utf8Bytes "metadata" <;> simp only [c, ↓reduceIte, decide_true,
    Bool.true_or, decide_false, Bool.false_or]
  by_cases d : host.val = utf8Bytes "metadata.google.internal" <;> simp only [d, ↓reduceIte,
    decide_true, Bool.true_or, decide_false, Bool.false_or]
  by_cases e : host.val = utf8Bytes "metadata.azure.internal" <;> simp only [e, ↓reduceIte,
    decide_true, decide_false]

theorem is_disallowed_metadata_host_domain_eq (d : Str) :
    is_disallowed_metadata_host (url.host.Host.Domain d) =
      match strOfBytes? (normalizeHost d.val) with
      | some _ => ok (isDisallowedHost (url.host.Host.Domain d))
      | none => fail .undef := by
  unfold is_disallowed_metadata_host
  simp only [transport.auth.metadata_resolver.prim.trim_end_dots]
  rw [bind_ok_str]
  simp only [alloc.str.Str.to_ascii_lowercase, Slice.from_val,
    ← normalizeHost_eq_map_dropTrailingDots]
  cases hs : strOfBytes? (normalizeHost d.val) with
  | none => dsimp only; rw [bind_fail]
  | some u =>
    rw [strOfBytes?_eq_some_iff] at hs
    have hlen : u.utf8ByteSize ≤ Usize.max := by
      rw [← length_utf8, ← hs]; exact le_trans (length_normalizeHost_le _) d.property
    simp only [bind_ok]
    rw [deref_eq u hlen, bind_ok_str]
    refine (is_disallowed_metadata_hostname_eq _).trans ?_
    simp only [Slice.from_val, ← hs, isDisallowedHost, isLocalhostName, isCloudMetadataName,
      isDisallowedHostname]

theorem exists_strOfBytes?_normalizeHost_eq_some_of_isUtf8 {l : List U8} (h : IsUtf8 l) :
    ∃ u, strOfBytes? (normalizeHost l) = some u := by
  have hu := isUtf8_map_asciiLowercase (isUtf8_dropTrailingDots h)
  rw [← normalizeHost_eq_map_dropTrailingDots] at hu
  obtain ⟨u, hu⟩ := hu
  exact ⟨u, by rw [hu, strOfBytes?_utf8]⟩

theorem is_disallowed_metadata_host_eq (host : url.host.Host Str)
    (h_utf8 : ∀ d, host = url.host.Host.Domain d → ExtModel.IsUtf8 d.val) :
    is_disallowed_metadata_host host = ok (isDisallowedHost host) := by
  cases host with
  | Domain d =>
    rw [is_disallowed_metadata_host_domain_eq]
    obtain ⟨u, hu⟩ := exists_strOfBytes?_normalizeHost_eq_some_of_isUtf8 (h_utf8 d rfl)
    rw [hu]
  | Ipv4 a =>
    obtain ⟨r, hr, hrv⟩ := exists_ok_of_spec (is_disallowed_metadata_ipv4_spec a)
    unfold is_disallowed_metadata_host; dsimp only; rw [hr, hrv]; rfl
  | Ipv6 a =>
    obtain ⟨r, hr, hrv⟩ := exists_ok_of_spec (is_disallowed_metadata_ipv6_spec a)
    unfold is_disallowed_metadata_host; dsimp only; rw [hr, hrv]; rfl

theorem is_some_and_urlHost_eq (base_url : url.Url) (h_base : HostUtf8 base_url) :
    core.option.Option.is_some_and
      CoreOpsFunctionFnOnceTupleHostShared0StrBool
      (ExtModel.urlHost base_url) () = ok ((ExtModel.urlHost base_url).any isLoopbackHost) := by
  cases hb : ExtModel.urlHost base_url with
  | none => rfl
  | some bh =>
    simp only [core.option.Option.is_some_and,
      CoreOpsFunctionFnOnceTupleHostShared0StrBool.call_once, Option.any_some]
    exact is_loopback_metadata_host_eq bh (fun d hd => h_base d (hb.trans (by rw [hd])))

/-! ## A06 `is_allowed_metadata_url` and `is_allowed_disallowed_host` -/

/-- `is_allowed_disallowed_host` once `is_loopback_metadata_host` is known to return
`isLoopbackHost` on the host. -/
theorem is_allowed_disallowed_host_eq_of_is_loopback_metadata_host_eq (base_url : url.Url)
    (host : url.host.Host Str) (allow_private : Bool) (h_base : HostUtf8 base_url)
    (hl : is_loopback_metadata_host host = ok (isLoopbackHost host)) :
    is_allowed_disallowed_host base_url host allow_private =
      ok (isAllowedDisallowedHost (ExtModel.urlHost base_url) host allow_private) := by
  have key : ∀ c : Option AddressClass, c = (hostIp host).map addressClass →
      (if allow_private = true then do
          let b ← core.option.Option.Insts.CoreCmpPartialEqOption.eq
            AddressClass.Insts.CoreCmpPartialEqAddressClass c (some AddressClass.Private)
          if b = true then ok true
            else do
              let o ← url.Url.host base_url
              let b1 ← core.option.Option.is_some_and
                CoreOpsFunctionFnOnceTupleHostShared0StrBool o ()
              if b1 = true then is_loopback_metadata_host host else ok false
        else do
          let o ← url.Url.host base_url
          let b ← core.option.Option.is_some_and
            CoreOpsFunctionFnOnceTupleHostShared0StrBool o ()
          if b = true then is_loopback_metadata_host host else ok false) =
      ok (isAllowedDisallowedHost (ExtModel.urlHost base_url) host allow_private) := by
    intro c hc
    simp only [bind_ok, url.Url.host]
    rw [is_some_and_urlHost_eq base_url h_base]
    cases allow_private with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, isAllowedDisallowedHost, Bool.false_and,
        Bool.false_or]
      cases (ExtModel.urlHost base_url).any isLoopbackHost <;> simp only [Bool.false_eq_true,
        ↓reduceIte, Bool.false_and, hl, Bool.true_and]
    | true =>
      simp only [↓reduceIte, isAllowedDisallowedHost, Bool.true_and, ← hc]
      cases c with
      | none =>
        simp only [core.option.Option.Insts.CoreCmpPartialEqOption.eq, bind_ok]
        cases (ExtModel.urlHost base_url).any isLoopbackHost <;> simp only [Bool.false_eq_true,
          ↓reduceIte, reduceCtorEq, decide_false, Bool.false_and, Bool.or_self, hl, Bool.true_and,
          Bool.false_or]
      | some c =>
        simp only [core.option.Option.Insts.CoreCmpPartialEqOption.eq]
        rw [addressClass_eq_eq]
        by_cases hp : c = AddressClass.Private
        · subst hp; simp only [decide_true, bind_ok, ↓reduceIte, Bool.true_or]
        · simp only [hp, decide_false, bind_ok, Bool.false_eq_true, ↓reduceIte,
            Option.some.injEq]
          cases (ExtModel.urlHost base_url).any isLoopbackHost <;> simp only [Bool.false_eq_true,
            ↓reduceIte, Bool.false_and, Bool.or_self, hl, Bool.true_and, Bool.false_or]
  unfold is_allowed_disallowed_host
  cases host with
  | Domain d => dsimp only; rw [bind_ok]; exact key none rfl
  | Ipv4 a => simp only [Proofs.Transport.MetadataResolver.of_eq, bind_ok]; exact key _ rfl
  | Ipv6 a => simp only [Proofs.Transport.MetadataResolver.of_eq, bind_ok]; exact key _ rfl

theorem is_allowed_disallowed_host_eq (base_url : url.Url) (host : url.host.Host Str)
    (allow_private : Bool) (h_base : HostUtf8 base_url)
    (h_utf8 : ∀ d, host = url.host.Host.Domain d → ExtModel.IsUtf8 d.val) :
    is_allowed_disallowed_host base_url host allow_private =
      ok (isAllowedDisallowedHost (ExtModel.urlHost base_url) host allow_private) :=
  is_allowed_disallowed_host_eq_of_is_loopback_metadata_host_eq base_url host allow_private h_base
    (is_loopback_metadata_host_eq host h_utf8)

/-- The body of `is_allowed_metadata_url` once A04 is evaluated. -/
theorem is_allowed_metadata_url_eq (base_url target : url.Url) (allow_private : Bool) :
    is_allowed_metadata_url base_url target allow_private =
      if isHttpUrl target then
        match ExtModel.urlHost target with
        | none => ok false
        | some host => do
          let b1 ← is_disallowed_metadata_host host
          if b1 then is_allowed_disallowed_host base_url host allow_private else ok true
      else ok false := by
  unfold is_allowed_metadata_url
  rw [is_http_url_eq]
  simp only [bind_ok, url.Url.host]
  cases isHttpUrl target <;> simp only [Bool.false_eq_true, ↓reduceIte]
  cases ExtModel.urlHost target <;> rfl

theorem ipv4Class_ne_public_iff (v : Nat) :
    ipv4Class v ≠ .Public ↔ ipv4Disallowed v = true := by
  unfold ipv4Class
  split_ifs with h1 h2 h3
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
    exact List.any_eq_true.mpr ⟨_, by simp only [ipv4DisallowedPrefixes, ipv4LoopbackPrefix,
      List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], h1⟩
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
    obtain ⟨p, hp, hpv⟩ := List.any_eq_true.mp h2
    refine List.any_eq_true.mpr ⟨p, ?_, hpv⟩
    simp only [ipv4PrivatePrefixes, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp only [ipv4DisallowedPrefixes, List.mem_cons,
      List.not_mem_nil, or_false, true_or, or_true]
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true, h3]
  · simp only [ne_eq, not_true_eq_false, h3, Bool.false_eq_true]

theorem ipv6Class_ne_public_iff (v : Nat) :
    ipv6Class v ≠ .Public ↔ ipv6Disallowed v = true := by
  unfold ipv6Class ipv6Disallowed
  cases embeddedIpv4 v with
  | some w => exact ipv4Class_ne_public_iff w
  | none =>
    dsimp only
    split_ifs with h1 h2 h3
    · simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
      exact List.any_eq_true.mpr ⟨_, by simp only [ipv6DisallowedPrefixes, List.mem_cons,
        List.not_mem_nil, or_false, true_or], h1⟩
    · simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
      exact List.any_eq_true.mpr ⟨_, by simp only [ipv6DisallowedPrefixes, List.mem_cons,
        List.not_mem_nil, or_false, true_or, or_true], h2⟩
    · simp only [ne_eq, reduceCtorEq, not_false_eq_true, h3]
    · simp only [ne_eq, not_true_eq_false, h3, Bool.false_eq_true]

theorem exists_strOfBytes?_normalizeHost_eq_some_of_isCloudMetadataName (d : Str)
    (hc : isCloudMetadataName d.val = true) :
    ∃ u, strOfBytes? (normalizeHost d.val) = some u := by
  unfold isCloudMetadataName at hc
  simp only [cloudMetadataHosts, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h <;> rw [h, utf8Bytes_eq_utf8, strOfBytes?_utf8] <;> exact ⟨_, rfl⟩

/-! ## A07 `is_same_origin` and `resolve_resource_metadata_url` -/

/-- Statement of `Proofs.Transport.AuthMetadata`
(`Defs.AuthMetadata.knownDefaultPort_eq_defaultPort`), needed here by
`port_or_known_default_eq`. -/
theorem knownDefaultPort_eq_defaultPort : knownDefaultPort = ExtModel.defaultPort := by
  funext s; rfl

theorem port_or_known_default_eq (u : url.Url) :
    url.Url.port_or_known_default u = ok (portOrKnownDefault u) := by
  unfold url.Url.port_or_known_default portOrKnownDefault
  rw [knownDefaultPort_eq_defaultPort]
  cases urlPort u <;> rfl

theorem partialEqOptionU16_eq (a b : Option U16) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq core.cmp.PartialEqU16 a b =
      ok (decide (a = b)) := by
  cases a <;> cases b <;> simp only [core.option.Option.Insts.CoreCmpPartialEqOption.eq,
    decide_true, reduceCtorEq, decide_false, liftFun2, core.cmp.impls.PartialEqU16.eq,
    Option.some.injEq]

theorem is_same_origin_eq (base candidate : url.Url) :
    is_same_origin base candidate = ok (isSameOrigin base candidate) := by
  unfold is_same_origin isSameOrigin
  simp only [url.Url.scheme, bind_ok, Str.Insts.CoreCmpPartialEqStr.eq, url.Url.host_str]
  by_cases hs : (urlScheme base).val = (urlScheme candidate).val
  · simp only [hs, decide_true, ↓reduceIte, Bool.true_and]
    cases hb : urlHostStr base <;> cases hc : urlHostStr candidate <;>
      simp only [core.option.Option.zip, core.option.Option.is_some_and,
        CoreOpsFunctionFnOnceTuplePairShared0StrShared1StrBool.call_once,
        core.str.Str.eq_ignore_ascii_case, port_or_known_default_eq, partialEqOptionU16_eq, bind_ok,
        Bool.false_eq_true, ↓reduceIte, Bool.false_and, uncurry_apply_pair, decide_eq_true_eq]
    rename_i b c
    have e : asciiToLower = asciiLowercase := by funext x; rfl
    rw [e]
    by_cases hh : List.map asciiLowercase b.val = List.map asciiLowercase c.val <;> simp only [hh,
      ↓reduceIte, decide_true, Bool.true_and, decide_false, Bool.false_and]
  · simp only [hs, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.false_and]

/-- The part of `resolve_resource_metadata_url` after the candidate URL `u` is found (upstream
lines 1458–1473): accept a same-origin HTTP(S) candidate, refuse an `https` downgrade, otherwise
ask `is_allowed_metadata_url`. -/
def resolveTail (base u : url.Url) (ap : Bool) : Result (Option url.Url) :=
  if isHttpUrl u && isSameOrigin base u then ok (some u)
  else if decide ((ExtModel.urlScheme base).val = utf8Bytes "https") &&
      !decide ((ExtModel.urlScheme u).val = utf8Bytes "https") then ok none
  else do
    let b ← is_allowed_metadata_url base u ap
    if b then ok (some u) else ok none

theorem resolve_resource_metadata_url_eq (value : Str) (base_url : url.Url) (ap : Bool) :
    resolve_resource_metadata_url value base_url ap =
      match metadataCandidate value.val base_url with
      | none => ok none
      | some u => resolveTail base_url u ap := by
  unfold resolve_resource_metadata_url metadataCandidate resolveTail
  simp only [transport.auth.prim.trim, core.str.Str.is_empty, url.Url.parse, url.Url.join, bind_ok,
    transport.auth.prim.debug_empty_resource_metadata,
    transport.auth.prim.debug_unparsable_resource_metadata,
    transport.auth.prim.warn_downgraded_resource_metadata,
    transport.auth.prim.warn_disallowed_resource_metadata, url.Url.scheme,
    Str.Insts.CoreCmpPartialEqStr.eq, toStr_val, ← utf8Bytes_eq_utf8]
  rw [bind_ok_str]
  simp only [Slice.from_val]
  by_cases he : trimWhitespace value.val = []
  · simp only [he, List.isEmpty_nil, ↓reduceIte]
  · simp only [he, List.isEmpty_iff, ↓reduceIte]
    have tail : ∀ u : url.Url,
        (do
          let b1 ← is_http_url u
          if b1 = true then do
            let b2 ← is_same_origin base_url u
            if b2 = true then ok (some u)
            else if decide ((urlScheme base_url).val = utf8Bytes "https") = true then
              if decide ((urlScheme u).val = utf8Bytes "https") = true then do
                let b5 ← is_allowed_metadata_url base_url u ap
                if b5 = true then ok (some u) else ok none
              else ok none
            else do
              let b4 ← is_allowed_metadata_url base_url u ap
              if b4 = true then ok (some u) else ok none
          else if decide ((urlScheme base_url).val = utf8Bytes "https") = true then
            if decide ((urlScheme u).val = utf8Bytes "https") = true then do
              let b4 ← is_allowed_metadata_url base_url u ap
              if b4 = true then ok (some u) else ok none
            else ok none
          else do
            let b3 ← is_allowed_metadata_url base_url u ap
            if b3 = true then ok (some u) else ok none : Result (Option url.Url)) =
        (if isHttpUrl u && isSameOrigin base_url u then ok (some u)
          else if decide ((ExtModel.urlScheme base_url).val = utf8Bytes "https") &&
              !decide ((ExtModel.urlScheme u).val = utf8Bytes "https") then ok none
          else do
            let b ← is_allowed_metadata_url base_url u ap
            if b then ok (some u) else ok none) := by
      intro u
      rw [is_http_url_eq, bind_ok, is_same_origin_eq]
      cases isHttpUrl u <;> cases isSameOrigin base_url u <;>
        cases decide ((urlScheme base_url).val = utf8Bytes "https") <;>
        cases decide ((urlScheme u).val = utf8Bytes "https") <;> simp only [Bool.false_eq_true,
          ↓reduceIte, Bool.and_self, Bool.not_false, Bool.and_true, Bool.not_true, Bool.and_false,
          bind_ok]
    cases hp : urlParse (trimWhitespace value.val) with
    | Ok u => dsimp only; exact tail u
    | Err _ =>
      dsimp only
      cases hj : urlJoin base_url (trimWhitespace value.val) with
      | Ok u => dsimp only; exact tail u
      | Err _ => rfl

theorem resolve_resource_metadata_url_eq_none_of_not_allowed (value : Str) (base_url u : url.Url)
    (ap : Bool)
    (h_candidate : metadataCandidate value.val base_url = some u)
    (h_origin : isSameOrigin base_url u = false)
    (h_a : is_allowed_metadata_url base_url u ap ⦃ (result : Bool) => result = false ⦄) :
    resolve_resource_metadata_url value base_url ap ⦃ (result : Option url.Url) =>
      result = none ⦄ := by
  rw [resolve_resource_metadata_url_eq, h_candidate]
  simp only [resolveTail, h_origin, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  split
  · simp only [WP.spec_ok]
  · obtain ⟨b, hb, hbv⟩ := exists_ok_of_spec h_a
    rw [hb, bind_ok, hbv]; simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]

/-! ## A08 and A09: owned strings, `trim_root_slash`, `issuer_identifiers_match` and the
derived issuer -/

theorem to_owned_eq_ok_of_val_eq_utf8 (s : Str) (t : String) (h : s.val = utf8 t) :
    Str.Insts.AllocBorrowToOwnedString.to_owned s = ok t := by
  simp only [Str.Insts.AllocBorrowToOwnedString.to_owned, h, strOfBytes?_utf8]

theorem to_owned_issuerNotRecordedMessage (h) :
    Str.Insts.AllocBorrowToOwnedString.to_owned (toStr
      "Authorization callback issuer cannot be validated because expected issuer was not recorded"
      h)
      = ok issuerNotRecordedMessage := to_owned_eq_ok_of_val_eq_utf8 _ _ (toStr_val _ h)

theorem isUtf8_of_isUtf8_append_slash {l : List U8} (h : IsUtf8 (l ++ [slashByte])) :
    IsUtf8 l := by
  obtain ⟨t, ht⟩ := h
  rw [← String.ofList_toList (s := t)] at ht
  generalize t.toList = cs at ht
  induction cs using List.reverseRecOn with
  | nil =>
    rw [utf8_ofList, List.flatMap_nil] at ht
    exact absurd ht.symm (by simp only [List.nil_eq, List.append_eq_nil_iff, List.cons_ne_self,
      and_false, not_false_eq_true])
  | append_singleton cs c _ =>
    have happ : utf8 (String.ofList (cs ++ [c])) =
        utf8 (String.ofList cs) ++ utf8 (String.ofList [c]) := by
      rw [utf8_ofList, utf8_ofList, utf8_ofList, List.flatMap_append]
    rw [happ] at ht
    by_cases hlt : c.toNat < 128
    · rw [utf8_ofList_singleton_ascii c hlt] at ht
      have := List.append_inj' ht rfl
      exact ⟨_, this.1⟩
    · exfalso
      have hne : utf8 (String.ofList [c]) ≠ [] := by
        rw [utf8_ofList, List.flatMap_cons, List.flatMap_nil, List.append_nil, ne_eq,
          List.map_eq_nil_iff]
        exact String.utf8EncodeChar_ne_nil
      have hlast : (l ++ [slashByte]).getLast? = (utf8 (String.ofList [c])).getLast? := by
        rw [ht, List.getLast?_append_of_ne_nil _ hne]
      rw [List.getLast?_append, List.getLast?_singleton] at hlast
      simp only [Option.some_or] at hlast
      have hmem : slashByte ∈ utf8 (String.ofList [c]) := List.mem_of_getLast? hlast.symm
      have := le_val_of_mem_utf8_ofList_singleton (Nat.not_lt.1 hlt) _ hmem
      simp only [slashByte, UScalar.ofNatCore_val_eq, Nat.reduceLeDiff] at this

theorem utf8_slash : utf8 "/" = [slashByte] := by decide +kernel

theorem is_root_url_eq (value : Str) : is_root_url value = ok (isRootUrl value.val) := by
  unfold is_root_url isRootUrl
  simp only [url.Url.parse, bind_ok]
  cases urlParse value.val with
  | Err _ => rfl
  | Ok p =>
    simp only [url.Url.path, bind_ok, core.str.Str.is_empty, Str.Insts.CoreCmpPartialEqStr.eq,
      toStr_val]
    rw [utf8_slash]
    cases hp : (urlPath p).val <;> simp only [List.isEmpty_nil, ↓reduceIte, decide_true,
      List.ne_cons_self, decide_false, Bool.or_false, List.isEmpty_cons, Bool.false_eq_true,
      List.cons.injEq, Bool.decide_and, reduceCtorEq, Bool.false_or]

theorem exists_trim_root_slash_eq_ok (issuer : Str) (h_utf8 : IsUtf8 issuer.val) :
    ∃ r, trim_root_slash issuer = ok r ∧ utf8Bytes r = trimRootSlash issuer.val := by
  unfold trim_root_slash trimRootSlash
  simp only [transport.auth.prim.strip_suffix, toStr_val]
  simp only [utf8_slash, List.length_singleton]
  obtain ⟨t, ht⟩ := h_utf8
  by_cases hs : [slashByte] <:+ issuer.val
  · simp only [hs, ↓reduceIte, bind_ok, true_and]
    have hd : issuer.val.take (issuer.val.length - 1) = issuer.val.dropLast := by
      rw [List.dropLast_eq_take]
    have hsplit : issuer.val = issuer.val.dropLast ++ [slashByte] := by
      obtain ⟨p, hp⟩ := hs
      rw [← hp, List.dropLast_concat]
    have hu : IsUtf8 issuer.val.dropLast :=
      isUtf8_of_isUtf8_append_slash (by rw [← hsplit]; exact ⟨t, ht⟩)
    obtain ⟨t', ht'⟩ := hu
    have hroot : is_root_url (Slice.from (issuer.val.take (issuer.val.length - 1))
        (ExtModel.length_take_le_max issuer _)) = ok (isRootUrl issuer.val.dropLast) := by
      refine (is_root_url_eq _).trans ?_
      simp only [hd, Slice.from_val]
    rw [hroot, bind_ok]
    cases isRootUrl issuer.val.dropLast
    · exact ⟨t, to_owned_eq_ok_of_val_eq_utf8 _ _ ht, ht.symm⟩
    · exact ⟨t', to_owned_eq_ok_of_val_eq_utf8 _ _ (by simp only [hd, ht',
        Slice.from_val]), ht'.symm⟩
  · simp only [hs, ↓reduceIte, bind_ok, false_and]
    exact ⟨t, to_owned_eq_ok_of_val_eq_utf8 _ _ ht, ht.symm⟩

theorem issuer_identifiers_match_eq (received_issuer expected_issuer : Str)
    (h_utf8 : received_issuer.val ≠ expected_issuer.val →
      ExtModel.IsUtf8 received_issuer.val ∧ ExtModel.IsUtf8 expected_issuer.val) :
    issuer_identifiers_match received_issuer expected_issuer =
      ok (issuersMatch received_issuer.val expected_issuer.val) := by
  unfold issuer_identifiers_match issuersMatch
  simp only [Str.Insts.CoreCmpPartialEqStr.eq]
  by_cases he : received_issuer.val = expected_issuer.val
  · simp only [he, decide_true, bind_ok, ↓reduceIte, Bool.or_self]
  · simp only [he, decide_false, Bool.false_or]
    obtain ⟨u1, u2⟩ := h_utf8 he
    obtain ⟨r, hr, hrv⟩ := exists_trim_root_slash_eq_ok _ u1
    obtain ⟨s, hs, hsv⟩ := exists_trim_root_slash_eq_ok _ u2
    rw [hr, bind_ok, hs, bind_ok]
    simp only [alloc.string.String.Insts.CoreCmpPartialEqString.eq, ← hrv, ← hsv, bind_ok,
      Bool.false_eq_true, ↓reduceIte]
    have : (r = s) ↔ (utf8Bytes r = utf8Bytes s) :=
      ⟨fun h => by rw [h], fun h => utf8_injective h⟩
    simp only [this]

theorem expected_issuer_for_authorization_metadata_url_eq (discovery_url : url.Url) :
    expected_issuer_for_authorization_metadata_url discovery_url =
      ok (derivedIssuer discovery_url) := by
  unfold expected_issuer_for_authorization_metadata_url derivedIssuer issuerPath
  simp only [url.Url.path, bind_ok, Str.Insts.CoreCmpPartialEqStr.eq, toStr_val,
    transport.auth.prim.issuer_url, transport.auth.prim.strip_dir_prefix,
    transport.auth.prim.strip_suffix, transport.auth.prim.trim_start_slashes]
  have e0 : utf8 "" = [] := by decide +kernel
  have e1 : utf8 "/.well-known/oauth-authorization-server" = oauthWellKnown := rfl
  have e2 : utf8 "/.well-known/openid-configuration" = oidcWellKnown := rfl
  have e3 : (47#u8 : U8) = slashByte := rfl
  have hp : (fun b : U8 => decide (b.val = 47)) = (fun b => decide (b = slashByte)) := by
    funext b; unfold slashByte; simp only [decide_eq_decide]
    constructor
    · intro h; apply UScalar.eq_of_val_eq; rw [h]; rfl
    · intro h; rw [h]; rfl
  simp only [e0, e1, e2, e3, hp]
  by_cases a : (urlPath discovery_url).val = oauthWellKnown
  · simp only [a, decide_true, ↓reduceIte, true_or, Option.map_some]
  by_cases b : (urlPath discovery_url).val = oidcWellKnown
  · simp only [b, decide_eq_true_eq, decide_true, ↓reduceIte, ite_self, or_true, Option.map_some]
  by_cases c : oauthWellKnown ++ [slashByte] <+: (urlPath discovery_url).val
  · simp only [a, decide_false, Bool.false_eq_true, ↓reduceIte, b, c, bind_ok, Slice.from_val,
      or_self, Option.map_some]
  by_cases d : oidcWellKnown ++ [slashByte] <+: (urlPath discovery_url).val
  · simp only [a, decide_false, Bool.false_eq_true, ↓reduceIte, b, c, d, bind_ok, Slice.from_val,
      or_self, Option.map_some]
  by_cases f : oidcWellKnown <:+ (urlPath discovery_url).val
  · simp only [a, b, c, d, f, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok, or_self,
      Option.map_some]
    rw [bind_ok_str]; simp only [Slice.from_val]
  · simp only [a, decide_false, Bool.false_eq_true, ↓reduceIte, b, c, d, f, bind_ok, or_self,
      Option.map_none]

theorem deref_eq_fail_of_not_le (p : String) (h : ¬ p.utf8ByteSize ≤ Usize.max) :
    alloc.string.String.Insts.CoreOpsDerefDerefStr.deref p = fail .maximumSizeExceeded := by
  have : ¬ (utf8 p).length ≤ Usize.max := by rw [length_utf8]; exact h
  simp only [alloc.string.String.Insts.CoreOpsDerefDerefStr.deref, alloc.string.String.as_bytes,
    this, ↓reduceDIte]
  rfl

theorem isUtf8_append_slash {l : List U8} (h : IsUtf8 l) : IsUtf8 (l ++ [slashByte]) := by
  obtain ⟨t, rfl⟩ := h
  refine ⟨t.push '/', ?_⟩
  rw [utf8_push_ascii t '/' (by decide)]
  rfl

theorem to_owned_eq_fail_of_not_isUtf8 (s : Str) (h : ¬ IsUtf8 s.val) :
    Str.Insts.AllocBorrowToOwnedString.to_owned s = fail .undef := by
  have : strOfBytes? s.val = none := (strOfBytes?_eq_none_iff _).2 (fun t ht => h ⟨t, ht⟩)
  simp only [Str.Insts.AllocBorrowToOwnedString.to_owned, this]

/-- Statement of `Proofs.Transport.AuthMetadata` (`AuthorizationManager.trim_root_slash_fail`),
needed there before its own place by `issuer_identifiers_match_fail`. -/
theorem trim_root_slash_fail (issuer : Str) (h : ¬ ExtModel.IsUtf8 issuer.val) :
    trim_root_slash issuer = fail .undef := by
  unfold trim_root_slash
  simp only [transport.auth.prim.strip_suffix, toStr_val, utf8_slash, List.length_singleton]
  by_cases hs : [slashByte] <:+ issuer.val
  · simp only [hs, ↓reduceIte, bind_ok]
    have hd : issuer.val.take (issuer.val.length - 1) = issuer.val.dropLast := by
      rw [List.dropLast_eq_take]
    have hsplit : issuer.val = issuer.val.dropLast ++ [slashByte] := by
      obtain ⟨p, hp⟩ := hs
      rw [← hp, List.dropLast_concat]
    have hr := is_root_url_eq (Slice.from (issuer.val.take (issuer.val.length - 1))
      (ExtModel.length_take_le_max issuer _))
    rw [hr, bind_ok]
    split
    · apply to_owned_eq_fail_of_not_isUtf8
      simp only [Slice.from_val, hd]
      intro hu; apply h; rw [hsplit]; exact isUtf8_append_slash hu
    · exact to_owned_eq_fail_of_not_isUtf8 issuer h
  · simp only [hs, ↓reduceIte, bind_ok]
    exact to_owned_eq_fail_of_not_isUtf8 issuer h

/-! ## A10 `is_resource_identifier_valid` and `check_resource_metadata_resource` -/

theorem partialEqOptionStr_eq (a b : Option Str) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq
      (core.cmp.PartialEqShared Str.Insts.CoreCmpPartialEqStr) a b =
      ok (decide (a.map (·.val) = b.map (·.val))) := by
  cases a <;> cases b <;>
    simp only [core.option.Option.Insts.CoreCmpPartialEqOption.eq, Option.map_none, decide_true,
      Option.map_some, reduceCtorEq, decide_false, core.cmp.impls.PartialEqShared.eq,
      Str.Insts.CoreCmpPartialEqStr.eq, Option.some.injEq]

theorem partialEqOptionU8_eq (a b : Option U8) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq
      (core.cmp.PartialEqShared core.cmp.PartialEqU8) a b = ok (decide (a = b)) := by
  cases a <;> cases b <;>
    simp only [core.option.Option.Insts.CoreCmpPartialEqOption.eq, decide_true, reduceCtorEq,
      decide_false, core.cmp.impls.PartialEqShared.eq, liftFun2, core.cmp.impls.PartialEqU8.eq,
      Option.some.injEq]

theorem bind_ok_slice {β : Type} (x : Str) (f : Slice U8 → Result β) :
    Aeneas.Std.bind (ok (α := Slice U8) x) f = f x :=
  bind_ok x f

theorem is_resource_identifier_valid_eq (e a : url.Url) :
    is_resource_identifier_valid e a = ok (isResourceIdentifierValid e a) := by
  unfold is_resource_identifier_valid isResourceIdentifierValid pathCovers
  simp only [url.Url.Insts.CoreCmpPartialEqUrl.eq, bind_ok, url.Url.scheme,
    Str.Insts.CoreCmpPartialEqStr.eq, url.Url.host_str, partialEqOptionStr_eq,
    port_or_known_default_eq, partialEqOptionU16_eq, url.Url.path, transport.auth.prim.starts_with,
    transport.auth.metadata_resolver.prim.ends_with, toStr_val, utf8_slash, core.str.Str.as_bytes,
    core.str.Str.len, core.slice.Slice.get, partialEqOptionU8_eq, bind_ok_slice,
    Slice.getElem?_Usize_eq]
  by_cases h1 : urlSerialization e = urlSerialization a
  · simp only [h1, decide_true, ↓reduceIte, Bool.true_or]
  by_cases h2 : (urlScheme e).val = (urlScheme a).val
  swap
  · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte, h2, Bool.false_and,
      Bool.or_self]
  by_cases h3 : (urlHostStr e).map (·.val) = (urlHostStr a).map (·.val)
  swap
  · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte, h2, decide_true, h3,
      Bool.and_false, Bool.false_and, Bool.or_self]
  by_cases h4 : portOrKnownDefault e = portOrKnownDefault a
  swap
  · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte, h2, decide_true, h3, h4,
      Bool.and_self, Bool.and_false, Bool.false_and, Bool.or_self]
  by_cases h5 : (urlPath e).val = (urlPath a).val
  · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte, h2, decide_true, h3, h4, h5,
      Bool.and_self, List.prefix_rfl, lt_self_iff_false, not_false_eq_true, getElem?_neg,
      reduceCtorEq, Bool.or_false, Bool.true_and, Bool.true_or, Bool.or_true]
  by_cases h6 : (urlPath a).val <+: (urlPath e).val
  swap
  · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte, h2, decide_true, h3, h4, h5, h6,
      Bool.and_self, Bool.false_and, Bool.or_self, Bool.and_false]
  by_cases h7 : [47#u8] <:+ (urlPath a).val
  · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte, h2, decide_true, h3, h4, h5, h6,
      slashByte, h7, Bool.and_self, Bool.true_or, Bool.or_true]
  · simp only [h1, h2, h3, h4, h5, h6, h7, slashByte, decide_true, decide_false, Bool.false_or,
      Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    rfl

theorem check_resource_metadata_resource_eq (base_url : url.Url) (metadata : ResourceServerMetadata)
    (h_fits : ∀ r, metadata.resource = some r → r.utf8ByteSize ≤ Usize.max) :
    check_resource_metadata_resource base_url metadata =
      ok (resourceCheck base_url metadata.resource) := by
  unfold check_resource_metadata_resource resourceCheck
  cases hr : metadata.resource with
  | none => simp only [core.option.Option.as_deref, core.option.Option.is_some, bind_ok]
  | some r =>
    simp only [core.option.Option.as_deref]
    rw [deref_eq r (h_fits r hr), bind_ok_str, bind_ok]
    simp only [url.Url.parse, bind_ok, Slice.from_val, utf8Bytes_eq_utf8]
    cases hp : urlParse (utf8 r) with
    | Err _ =>
      simp only [to_owned_eq_ok_of_val_eq_utf8 _ r (Slice.from_val _ _), bind_ok]
    | Ok u =>
      simp only [url.Url.fragment, bind_ok, core.option.Option.is_some,
        is_resource_identifier_valid_eq, url.Url.Insts.CoreCloneClone.clone]
      cases urlFragment u <;> simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        Option.isSome_some]
      split <;> simp_all only [Option.some.injEq, forall_eq', Bool.not_eq_true]

/-! ## Inversion of successful calls (A05–A07) -/

theorem eq_isLoopbackHost_of_eq_ok (h : url.host.Host Str) (b : Bool)
    (hb : is_loopback_metadata_host h = ok b) : b = isLoopbackHost h := by
  cases h with
  | Domain d =>
    rw [is_loopback_metadata_host_domain_eq] at hb
    split at hb
    · simp only [ok.injEq] at hb; rw [← hb]; rfl
    · simp only [fail_not_ok] at hb
  | Ipv4 a =>
    rw [is_loopback_metadata_host_eq _ (by intro _ h; cases h)] at hb
    simp only [ok.injEq] at hb; rw [← hb]
  | Ipv6 a =>
    rw [is_loopback_metadata_host_eq _ (by intro _ h; cases h)] at hb
    simp only [ok.injEq] at hb; rw [← hb]

theorem eq_isDisallowedHost_of_eq_ok (h : url.host.Host Str) (b : Bool)
    (hb : is_disallowed_metadata_host h = ok b) : b = isDisallowedHost h := by
  cases h with
  | Domain d =>
    rw [is_disallowed_metadata_host_domain_eq] at hb
    split at hb
    · simp only [ok.injEq] at hb; rw [← hb]
    · simp only [fail_not_ok] at hb
  | Ipv4 a =>
    rw [is_disallowed_metadata_host_eq _ (by intro _ h; cases h)] at hb
    simp only [ok.injEq] at hb; rw [← hb]
  | Ipv6 a =>
    rw [is_disallowed_metadata_host_eq _ (by intro _ h; cases h)] at hb
    simp only [ok.injEq] at hb; rw [← hb]

theorem any_isLoopbackHost_of_is_some_and_eq_ok_true (o : Option (url.host.Host Str))
    (hb : core.option.Option.is_some_and
      CoreOpsFunctionFnOnceTupleHostShared0StrBool
      o () = ok true) : o.any isLoopbackHost = true := by
  cases o with
  | none => simp only [core.option.Option.is_some_and, ok.injEq, Bool.false_eq_true] at hb
  | some bh =>
    simp only [core.option.Option.is_some_and,
      CoreOpsFunctionFnOnceTupleHostShared0StrBool.call_once] at hb
    simp only [Option.any_some, ← eq_isLoopbackHost_of_eq_ok bh true hb]

theorem isAllowedDisallowedHost_of_eq_ok_true (base_url : url.Url) (host : url.host.Host Str)
    (ap : Bool)
    (hb : is_allowed_disallowed_host base_url host ap = ok true) :
    isAllowedDisallowedHost (ExtModel.urlHost base_url) host ap = true := by
  have key : ∀ c : Option AddressClass, c = (hostIp host).map addressClass →
      (if ap = true then do
          let b ← core.option.Option.Insts.CoreCmpPartialEqOption.eq
            AddressClass.Insts.CoreCmpPartialEqAddressClass c (some AddressClass.Private)
          if b = true then ok true
            else do
              let o ← url.Url.host base_url
              let b1 ← core.option.Option.is_some_and
                CoreOpsFunctionFnOnceTupleHostShared0StrBool o ()
              if b1 = true then is_loopback_metadata_host host else ok false
        else do
          let o ← url.Url.host base_url
          let b ← core.option.Option.is_some_and
            CoreOpsFunctionFnOnceTupleHostShared0StrBool o ()
          if b = true then is_loopback_metadata_host host else ok false) = ok true →
      isAllowedDisallowedHost (ExtModel.urlHost base_url) host ap = true := by
    intro c hc hk
    have tail : (do
          let o ← url.Url.host base_url
          let b ← core.option.Option.is_some_and
            CoreOpsFunctionFnOnceTupleHostShared0StrBool o ()
          if b = true then is_loopback_metadata_host host else ok false) = ok true →
        ((ExtModel.urlHost base_url).any isLoopbackHost && isLoopbackHost host) = true := by
      intro ht
      simp only [url.Url.host, bind_ok] at ht
      rw [bind_eq_ok_iff] at ht
      obtain ⟨b, hb1, hb2⟩ := ht
      cases b with
      | false => simp only [Bool.false_eq_true, ↓reduceIte, ok.injEq] at hb2
      | true =>
        simp only [↓reduceIte] at hb2
        rw [any_isLoopbackHost_of_is_some_and_eq_ok_true _ hb1,
          ← eq_isLoopbackHost_of_eq_ok host true hb2]
        rfl
    unfold isAllowedDisallowedHost
    cases ap with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hk
      simp only [Option.map_eq_some_iff, Bool.false_and, tail hk, Bool.or_true]
    | true =>
      simp only [↓reduceIte] at hk
      rw [bind_eq_ok_iff] at hk
      obtain ⟨b, hb1, hb2⟩ := hk
      cases b with
      | true =>
        cases c with
        | none => simp only [core.option.Option.Insts.CoreCmpPartialEqOption.eq, ok.injEq,
          Bool.false_eq_true] at hb1
        | some c =>
          simp only [core.option.Option.Insts.CoreCmpPartialEqOption.eq] at hb1
          rw [addressClass_eq_eq] at hb1
          simp only [ok.injEq, decide_eq_true_eq] at hb1
          subst hb1
          simp only [← hc, decide_true, Bool.and_self, Bool.true_or]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hb2
        simp only [Option.map_eq_some_iff, Bool.true_and, tail hb2, Bool.or_true]
  unfold is_allowed_disallowed_host at hb
  cases host with
  | Domain d => simp only [bind_ok] at hb; exact key none rfl hb
  | Ipv4 a => simp only [Proofs.Transport.MetadataResolver.of_eq, bind_ok] at hb; exact key _ rfl hb
  | Ipv6 a => simp only [Proofs.Transport.MetadataResolver.of_eq, bind_ok] at hb; exact key _ rfl hb

theorem isAllowedMetadataUrl_of_eq_ok_true (base_url target : url.Url) (ap : Bool)
    (h : is_allowed_metadata_url base_url target ap = ok true) :
    isAllowedMetadataUrl base_url target ap = true := by
  rw [is_allowed_metadata_url_eq] at h
  unfold isAllowedMetadataUrl
  cases hh : isHttpUrl target
  · simp only [hh, Bool.false_eq_true, ↓reduceIte, ok.injEq] at h
  · simp only [hh, ↓reduceIte] at h
    cases ht : ExtModel.urlHost target with
    | none => simp only [ht, ok.injEq, Bool.false_eq_true] at h
    | some host =>
      simp only [ht] at h
      rw [bind_eq_ok_iff] at h
      obtain ⟨b, hb1, hb2⟩ := h
      have := eq_isDisallowedHost_of_eq_ok host b hb1
      subst this
      cases hd : isDisallowedHost host
      · simp only [hd, Bool.not_false, Bool.true_or, Bool.and_self]
      · simp only [hd, ↓reduceIte] at hb2
        simp only [isAllowedDisallowedHost_of_eq_ok_true base_url host ap hb2,
          Bool.or_true, Bool.and_self]

theorem of_resolve_resource_metadata_url_eq_ok_some (value : Str) (base_url : url.Url) (ap : Bool)
    (u : url.Url)
    (h : resolve_resource_metadata_url value base_url ap = ok (some u)) :
    metadataCandidate value.val base_url = some u ∧
      ((isHttpUrl u && isSameOrigin base_url u) = true ∨
        ((decide ((ExtModel.urlScheme base_url).val = utf8Bytes "https") &&
          !decide ((ExtModel.urlScheme u).val = utf8Bytes "https")) = false ∧
          isAllowedMetadataUrl base_url u ap = true)) := by
  rw [resolve_resource_metadata_url_eq] at h
  cases hc : metadataCandidate value.val base_url with
  | none => rw [hc] at h; simp only [ok.injEq, reduceCtorEq] at h
  | some u' =>
    rw [hc] at h
    simp only [resolveTail] at h
    split_ifs at h with h1 h2
    · simp only [ok.injEq, Option.some.injEq] at h; subst h; exact ⟨rfl, Or.inl h1⟩
    · simp only [ok.injEq, reduceCtorEq] at h
    · rw [bind_eq_ok_iff] at h
      obtain ⟨b, hb1, hb2⟩ := h
      cases b with
      | false => simp only [Bool.false_eq_true, ↓reduceIte, ok.injEq, reduceCtorEq] at hb2
      | true =>
        simp only [↓reduceIte, ok.injEq, Option.some.injEq] at hb2
        subst hb2
        refine ⟨rfl, Or.inr ⟨?_, isAllowedMetadataUrl_of_eq_ok_true _ _ _ hb1⟩⟩
        simpa only [Bool.and_eq_false_imp, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_false,
          Bool.and_eq_true, Bool.not_true, decide_eq_false_iff_not, not_and,
          Decidable.not_not] using h2

/-! ## A09 `check_authorization_metadata_issuer` -/

theorem length_oauthWellKnown : oauthWellKnown.length = 39 := by decide +kernel

theorem length_oidcWellKnown : oidcWellKnown.length = 33 := by decide +kernel

theorem not_oidcWellKnown_slash_prefix_oauthWellKnown_slash :
    ¬ oidcWellKnown ++ [slashByte] <+: oauthWellKnown ++ [slashByte] := by
  decide +kernel

theorem not_oidcWellKnown_suffix_oauthWellKnown : ¬ oidcWellKnown <:+ oauthWellKnown := by
  decide +kernel

theorem eq_dropLast_append_slash_of_suffix {l : List U8} (h : [slashByte] <:+ l) :
    l = l.dropLast ++ [slashByte] := by
  obtain ⟨p, hp⟩ := h
  rw [← hp, List.dropLast_concat]

theorem check_authorization_metadata_issuer_eq (allow_missing_issuer : Bool)
    (discovery_url : url.Url) (expected_issuer : Option Str) (metadata : AuthorizationMetadata)
    (h_utf8 : ∀ s, expected_issuer = some s → ExtModel.IsUtf8 s.val)
    (h_received : ∀ r, metadata.issuer = some r → r.utf8ByteSize ≤ Usize.max)
    (h_derived : expected_issuer = none →
      ∀ e, derivedIssuer discovery_url = some e → e.utf8ByteSize ≤ Usize.max) :
    check_authorization_metadata_issuer allow_missing_issuer discovery_url expected_issuer
      metadata = ok (metadataIssuerCheck allow_missing_issuer
        (expectedIssuerOf (expected_issuer.map (·.val)) discovery_url) metadata.issuer) := by
  unfold check_authorization_metadata_issuer
  cases hx : expected_issuer with
  | none =>
    dsimp only
    rw [expected_issuer_for_authorization_metadata_url_eq, bind_ok]
    simp only [Option.map_none, expectedIssuerOf]
    cases hd : derivedIssuer discovery_url with
    | none => simp only [metadataIssuerCheck]
    | some e =>
      dsimp only
      have he := h_derived hx e hd
      cases hi : metadata.issuer with
      | none =>
        simp only [core.option.Option.as_deref, bind_ok, metadataIssuerCheck]
        cases allow_missing_issuer <;> simp only [Bool.false_eq_true, ↓reduceIte]
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
        · simp only [hm, ↓reduceIte]
        · simp only [hm, Bool.false_eq_true, ↓reduceIte]
          rw [to_owned_eq_ok_of_val_eq_utf8 _ r (Slice.from_val _ _), bind_ok]
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
      cases allow_missing_issuer <;> simp only [Bool.false_eq_true, ↓reduceIte]
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
      · simp only [hm, ↓reduceIte]
      · simp only [hm, Bool.false_eq_true, ↓reduceIte]
        rw [to_owned_eq_ok_of_val_eq_utf8 _ r (Slice.from_val _ _), bind_ok]

/-- With no explicit issuer and a derived one, a received issuer too long fails. -/
theorem check_authorization_metadata_issuer_none_eq_fail (allow_missing_issuer : Bool)
    (discovery_url : url.Url) (metadata : AuthorizationMetadata) (e r : String)
    (h_derived : derivedIssuer discovery_url = some e) (h_issuer : metadata.issuer = some r)
    (h : ¬ r.utf8ByteSize ≤ Usize.max) :
    check_authorization_metadata_issuer allow_missing_issuer discovery_url none metadata =
      fail .maximumSizeExceeded := by
  unfold check_authorization_metadata_issuer
  dsimp only
  rw [expected_issuer_for_authorization_metadata_url_eq, bind_ok, h_derived]
  dsimp only
  simp only [h_issuer, core.option.Option.as_deref]
  rw [deref_eq_fail_of_not_le r h, bind_fail, bind_fail]

end Proofs.Transport.AuthMetadata
