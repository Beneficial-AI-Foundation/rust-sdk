/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Proofs.Defs.MetadataResolver
public import Proofs.External.MetadataResolver
public import Proofs.External.Net
public import Proofs.External.Std
public import Proofs.External.String
public import Proofs.External.WP
public import Proofs.Transport.Auth

@[expose] public section

/-!
# Helper lemmas for the OAuth metadata address policy (N01, N03–N11)

Equations and inversion lemmas for the translated functions of
`crates/rmcp/src/transport/auth/metadata_resolver.rs` (patch 05) and their callee
`AuthorizationManager::is_loopback_metadata_host` (`auth.rs`), used by the spec theorems in
`Proofs.Transport.MetadataResolver`:

- N11 `normalize_host` as one equation on `normalizeHost` (`normalize_host_eq`), with its
  failure on bytes that are not UTF-8 through the converse UTF-8 lemmas of
  `Proofs.External.MetadataResolver`;
- `proxy_host` (helper of N05) as `proxyHostTail` of the URL text `proxyUrl` once the value
  fits (`proxy_host_eq_proxyHostTail`), and the inversion of a successful call;
- the `with_proxy_hosts` loop (N05) on an iterator built from a list (`mkIntoIter`), by
  induction on the list, in both directions (`with_proxy_hosts_loop_of_eq_ok`,
  `exists_with_proxy_hosts_loop_eq_ok`);
- the steps of the laws of `normalizeHost` (`trimTrailingDots_map_asciiToLower`,
  `asciiToLower_idem`);
- N01 `AddressClass::of` by octets and segments (`of_v4_eq`,
  `of_v6_eq_of_embedded_ipv4_eq_ok_none`), with the range lemmas of `Proofs.Transport.Auth`;
- `slice::contains` on address classes and strings, `is_allowed`, `literal_ip` and
  `AddressClass::of` as equations;
- `is_loopback_metadata_host`, `with_base_url` (N04) and `new` (N03), and the
  `allowed_addresses` loop (N09) and `allowing_private_addresses` (N06).

Several lemmas here are statements of `Proofs.Transport.MetadataResolver` (`new_eq_bind`, the
`…_eq_fail` lemmas, `of_v6_eq_of_embedded_ipv4_eq_ok_some`): the other lemmas of this file need
them, so they are proved here and the statement theorems are proved by them.

The generic facts about `Result` and `Vec` used here (`bind_eq_ok_iff`, `anyM_eq_ok`,
`push_eq_ok`, ...) are in `Proofs.External.WP`; `ok_not_fail` is the Aeneas lemma.

Source: "crates/rmcp/src/transport/auth/metadata_resolver.rs" (patched copy, patch 05; upstream
`7caec76` lines 33–225)
-/

open Aeneas Aeneas.Std Result
open rmcp
open Defs.MetadataResolver Defs.Net
open transport.auth.metadata_resolver
open ExtModel Proofs.External.Utf8 Proofs.External.WP Proofs.Transport.Auth
open Proofs.External.MetadataResolver

namespace Proofs.Transport.MetadataResolver

/-- The tail of `proxy_host` after the URL text is built: parse it, take the host string and
normalize it (`none` if it does not parse or has no host). -/
def proxyHostTail (bytes : List U8) : Result (Option String) :=
  match ExtModel.urlParse bytes with
  | .Ok u =>
    match ExtModel.urlHostStr u with
    | some h => do let x ← normalize_host h; ok (some x)
    | none => ok none
  | .Err _ => ok none

/-- `String::deref` of a string that fits a slice, as an equation: the signed-off spec theorem
`alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec` (`Proofs.External.String`) through
`exists_ok_of_spec`. The bind that follows a call is rewritten by `bind_ok_str` (the slice is a
`Slice U8` returned as a `Str`). -/
theorem deref_eq (p : String) (h : p.utf8ByteSize ≤ Usize.max) :
    alloc.string.String.Insts.CoreOpsDerefDerefStr.deref p =
      ok (α := Str) (Slice.from (utf8 p) (by rw [length_utf8]; exact h)) := by
  obtain ⟨y, hy, hv⟩ :=
    exists_ok_of_spec (alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec p h)
  rw [hy]
  exact congrArg (ok (α := Str)) (Slice.ext y _ (hv.trans (Slice.from_val _ _).symm))

theorem proxy_host_eq_proxyHostTail (p : String) (hf : ProxyFits p) :
    proxy_host p = proxyHostTail (proxyUrl (Defs.utf8Bytes p)) := by
  obtain ⟨h1, h2⟩ := hf
  unfold proxy_host
  rw [deref_eq p h1, bind_ok_str]
  simp only [prim.contains, bind_ok, toStr_val, Slice.from_val]
  simp only [proxyUrl, utf8Bytes_eq_utf8]
  by_cases hc : utf8 "://" <:+: utf8 p
  · -- the value is the URL text
    simp only [hc, decide_true, ↓reduceIte, bind_ok]
    generalize hq : p = q at h1
    subst hq
    -- the common tail, below
    rw [deref_eq _ h1, bind_ok_str]
    simp only [url.Url.parse, bind_ok, Slice.from_val, core.result.Result.ok,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch, proxyHostTail]
    split <;> rename_i heq <;> simp only [heq, bind_ok, url.Url.host_str,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
    split <;> rename_i hh <;> rw [hh] <;> rfl
  · -- `http://` followed by the value
    have hlen := h2 (by rwa [utf8Bytes_eq_utf8, utf8Bytes_eq_utf8])
    rw [utf8Bytes_eq_utf8, utf8Bytes_eq_utf8, ← utf8_append, length_utf8] at hlen
    simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte,
      Str.Insts.AllocBorrowToOwnedString.to_owned, toStr_val, strOfBytes?_utf8, bind_ok,
      alloc.string.String.push_str, Slice.from_val, growString, hlen, ↓reduceIte]
    rw [← utf8_append, deref_eq _ (le_trans hlen maxStringBytes_le_usize_max), bind_ok_str]
    simp only [url.Url.parse, bind_ok, Slice.from_val, core.result.Result.ok,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch, proxyHostTail]
    split <;> rename_i heq <;> simp only [heq, bind_ok, url.Url.host_str,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
    split <;> rename_i hh <;> rw [hh] <;> rfl

theorem normalizeHost_eq_map_dropTrailingDots (l : List U8) :
    normalizeHost l = (dropTrailingDots l).map asciiLowercase := by
  unfold normalizeHost trimTrailingDots dropTrailingDots List.rdropWhile
  have hp : (fun b : U8 => decide (b = dotByte)) = (fun b => decide (b.val = 46)) := by
    funext b; unfold dotByte; simp only [decide_eq_decide]
    constructor
    · intro h; rw [h]; rfl
    · intro h; apply UScalar.eq_of_val_eq; rw [h]; rfl
  have hf : asciiToLower = asciiLowercase := by
    funext b; unfold asciiToLower asciiLowercase; rfl
  rw [hp, hf]

theorem normalize_host_eq (h : Str) :
    normalize_host h = match strOfBytes? (normalizeHost h.val) with
      | some s => ok s
      | none => fail .undef := by
  unfold normalize_host prim.trim_end_dots
  rw [bind_ok_str]
  simp only [alloc.str.Str.to_ascii_lowercase, Slice.from_val,
      normalizeHost_eq_map_dropTrailingDots]
  rfl

theorem normalize_host_eq_fail (host : Str) (h : ¬ ExtModel.IsUtf8 host.val) :
    normalize_host host = fail .undef := by
  rw [normalize_host_eq]
  cases hs : strOfBytes? (normalizeHost host.val) with
  | none => rfl
  | some s =>
    exfalso; apply h
    rw [strOfBytes?_eq_some_iff, normalizeHost_eq_map_dropTrailingDots] at hs
    exact isUtf8_of_isUtf8_dropTrailingDots (isUtf8_of_isUtf8_map_asciiLowercase ⟨s, hs⟩)

theorem normalize_host_of_eq_ok {h : Str} {x : String} (hx : normalize_host h = ok x) :
    utf8 x = normalizeHost h.val ∧ IsUtf8 h.val := by
  rw [normalize_host_eq] at hx
  cases hs : strOfBytes? (normalizeHost h.val) with
  | none => rw [hs] at hx; exact absurd hx.symm ok_not_fail
  | some s =>
    rw [hs] at hx; simp only [ok.injEq] at hx; subst hx
    rw [strOfBytes?_eq_some_iff] at hs
    refine ⟨hs.symm, ?_⟩
    rw [normalizeHost_eq_map_dropTrailingDots] at hs
    exact isUtf8_of_isUtf8_dropTrailingDots (isUtf8_of_isUtf8_map_asciiLowercase ⟨s, hs⟩)

theorem proxy_host_eq_fail (proxy : String) (h : ¬ ProxyFits proxy) :
    proxy_host proxy =
      fail (if proxy.utf8ByteSize ≤ Usize.max then .panic else .maximumSizeExceeded) := by
  unfold ProxyFits at h
  by_cases h1 : proxy.utf8ByteSize ≤ Usize.max
  · rw [ite_eq_left h1]
    have h2 : ¬ Defs.utf8Bytes "://" <:+: Defs.utf8Bytes proxy ∧
        ¬ (Defs.utf8Bytes "http://" ++ Defs.utf8Bytes proxy).length ≤ maxStringBytes := by
      by_contra hc; apply h; refine ⟨h1, fun hn => ?_⟩
      by_contra hl; exact hc ⟨hn, hl⟩
    rw [utf8Bytes_eq_utf8, utf8Bytes_eq_utf8,
      utf8Bytes_eq_utf8, ← utf8_append, length_utf8] at h2
    unfold proxy_host
    rw [deref_eq proxy h1, bind_ok_str]
    simp only [prim.contains, bind_ok, toStr_val, Slice.from_val, h2.1, decide_false,
      Bool.false_eq_true, ↓reduceIte]
    have hhttp : Str.Insts.AllocBorrowToOwnedString.to_owned (toStr "http://") = ok "http://" := by
      simp only [Str.Insts.AllocBorrowToOwnedString.to_owned, toStr_val, strOfBytes?_utf8]
    have hpush : alloc.string.String.push_str "http://"
        (Slice.from (utf8 proxy) (by rw [length_utf8]; exact h1)) = fail .panic := by
      simp only [alloc.string.String.push_str, Slice.from_val, strOfBytes?_utf8, growString, h2.2,
        ↓reduceIte]
    simp only [hhttp, bind_ok, hpush, bind_fail]
  · rw [ite_eq_right h1]
    unfold proxy_host
    rw [alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_fail proxy (by omega), bind_fail]

theorem proxyHostTail_of_eq_ok {b : List U8} {o : Option String} (h : proxyHostTail b = ok o) :
    o.map utf8 = (match ExtModel.urlParse b with
      | .Ok u => (ExtModel.urlHostStr u).map (fun h => normalizeHost h.val)
      | .Err _ => none) ∧
    ∀ u hs, ExtModel.urlParse b = .Ok u → ExtModel.urlHostStr u = some hs →
      IsUtf8 hs.val := by
  unfold proxyHostTail at h
  cases hp : ExtModel.urlParse b with
  | Err e =>
    simp only [hp, ok.injEq] at h; subst h
    exact ⟨rfl, fun u hs hu => by cases hu⟩
  | Ok u =>
    cases hh : ExtModel.urlHostStr u with
    | none =>
      simp only [hp, hh, ok.injEq] at h; subst h
      refine ⟨by simp [hh], fun u' hs hu' hs' => ?_⟩
      cases hu'; rw [hh] at hs'; cases hs'
    | some hs =>
      simp only [hp, hh] at h
      obtain ⟨x, hn, h⟩ := bind_eq_ok_iff.1 h
      rw [ok.injEq] at h; subst h
      obtain ⟨h1, h2⟩ := normalize_host_of_eq_ok hn
      refine ⟨by simp [h1, hh], fun u' hs' hu' hs'' => ?_⟩
      cases hu'; rw [hh] at hs''; cases hs''; exact h2

theorem proxy_host_of_eq_ok {p : String} {o : Option String} (h : proxy_host p = ok o) :
    o.map Defs.utf8Bytes = proxyHost (Defs.utf8Bytes p) ∧ ProxyFits p ∧ ProxyHostUtf8 p := by
  have hf : ProxyFits p := by
    by_contra hn; rw [proxy_host_eq_fail p hn] at h; exact ok_not_fail h.symm
  rw [proxy_host_eq_proxyHostTail p hf] at h
  obtain ⟨h1, h2⟩ := proxyHostTail_of_eq_ok h
  refine ⟨?_, hf, fun u hs hu hs' => h2 u hs hu hs'⟩
  rw [proxyHost]
  have : o.map Defs.utf8Bytes = o.map utf8 := rfl
  rw [this, h1]; rfl

/-- The `Vec` iterator over the strings `l` (the `into_iter` of a `Vec` holding `l`). -/
def mkIntoIter (l : List String) (h : l.length ≤ Usize.max) :
    alloc.vec.into_iter.IntoIter String :=
  alloc.vec.Vec.from l h

theorem next_mkIntoIter_nil (hps : ([] : List String).length ≤ Usize.max) :
    alloc.vec.into_iter.IteratorIntoIter.next
      (mkIntoIter [] hps) =
      ok (none, (mkIntoIter [] hps)) := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next mkIntoIter
  split
  · rfl
  · rename_i h; simp [alloc.vec.Vec.from_val] at h

theorem next_mkIntoIter_cons (p : String) (ps : List String)
    (hps : (p :: ps).length ≤ Usize.max) :
    alloc.vec.into_iter.IteratorIntoIter.next
      (mkIntoIter (p :: ps) hps) =
      ok (some p, mkIntoIter ps (by rw [List.length_cons] at hps; omega)) := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next mkIntoIter
  split
  · rename_i h; simp [alloc.vec.Vec.from_val] at h
  · rename_i hd tl h
    simp only [alloc.vec.Vec.from_val, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

theorem with_proxy_hosts_loop_of_eq_ok : ∀ (ps : List String) (hps : ps.length ≤ Usize.max)
    (acc res : alloc.vec.Vec String),
    MetadataAddressResolver.with_proxy_hosts_loop (core.iter.traits.collect.IntoIteratorVec String)
      (mkIntoIter ps hps) acc = ok res →
    res.val.map Defs.utf8Bytes = acc.val.map Defs.utf8Bytes ++
        ps.filterMap (fun p => proxyHost (Defs.utf8Bytes p)) ∧
      ∀ p ∈ ps, ProxyFits p ∧ ProxyHostUtf8 p
  | [], hps, acc, res, h => by
    unfold MetadataAddressResolver.with_proxy_hosts_loop at h
    rw [loop] at h
    simp only [MetadataAddressResolver.with_proxy_hosts_loop.body] at h
    rw [next_mkIntoIter_nil, bind_ok] at h
    simp only [uncurry, bind_ok, ok.injEq] at h
    subst h
    simp
  | p :: ps, hps, acc, res, h => by
    unfold MetadataAddressResolver.with_proxy_hosts_loop at h
    rw [loop] at h
    simp only [MetadataAddressResolver.with_proxy_hosts_loop.body] at h
    rw [next_mkIntoIter_cons, bind_ok] at h
    simp only [uncurry] at h
    obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.1 h
    obtain ⟨o, hp, hc⟩ := bind_eq_ok_iff.1 hc
    obtain ⟨ho, hf, hu⟩ := proxy_host_of_eq_ok hp
    have hmem : ∀ q ∈ p :: ps, (q ∈ ps → ProxyFits q ∧ ProxyHostUtf8 q) →
        ProxyFits q ∧ ProxyHostUtf8 q := fun q hq hps' =>
      (List.mem_cons.1 hq).elim (fun e => e ▸ ⟨hf, hu⟩) hps'
    cases o with
    | none =>
      rw [ok.injEq] at hc; subst hc
      obtain ⟨ih1, ih2⟩ := with_proxy_hosts_loop_of_eq_ok ps _ acc res h
      refine ⟨?_, fun q hq => hmem q hq (ih2 q)⟩
      rw [ih1, List.filterMap_cons, ← ho]; rfl
    | some host =>
      obtain ⟨acc', hq, hc⟩ := bind_eq_ok_iff.1 hc
      rw [ok.injEq] at hc; subst hc
      obtain ⟨ih1, ih2⟩ := with_proxy_hosts_loop_of_eq_ok ps _ acc' res h
      refine ⟨?_, fun q hq => hmem q hq (ih2 q)⟩
      rw [ih1, List.filterMap_cons, ← ho, val_eq_of_push_eq_ok hq]
      simp

/-- `into_iter` of a `Vec` of strings is the iterator `mkIntoIter` of its list. -/
theorem into_iter_eq_mkIntoIter (proxies : alloc.vec.Vec String) :
    alloc.vec.IntoIteratorVec.into_iter proxies = ok (mkIntoIter proxies.val proxies.property) := by
  unfold alloc.vec.IntoIteratorVec.into_iter mkIntoIter
  congr 1
  exact alloc.vec.Vec.ext _ _ (by rw [alloc.vec.Vec.from_val])

theorem to_vec_string (s : Slice String) :
    alloc.slice.Slice.to_vec alloc.string.String.Insts.CoreCloneClone s = ok ⟨s⟩ := by
  obtain ⟨v, hv, hvv⟩ := Proofs.External.WP.exists_ok_of_spec
    (alloc.slice.Slice.to_vec_spec alloc.string.String.Insts.CoreCloneClone s (fun x _ => rfl))
  rw [hv]; cases v; simp_all

theorem with_proxy_hosts_of_eq_ok_and_premises (self r : MetadataAddressResolver)
    (proxies : alloc.vec.Vec String)
    (h : MetadataAddressResolver.with_proxy_hosts
      (core.iter.traits.collect.IntoIteratorVec String) self proxies = ok r) :
    (r.unfiltered_hosts.data.val.map Defs.utf8Bytes =
        self.unfiltered_hosts.data.val.map Defs.utf8Bytes ++
          proxies.val.filterMap (fun p => proxyHost (Defs.utf8Bytes p)) ∧
      r.base_ip = self.base_ip ∧ r.base_classes = self.base_classes ∧
      r.lookup = self.lookup) ∧ ∀ p ∈ proxies.val, ProxyFits p ∧ ProxyHostUtf8 p := by
  unfold MetadataAddressResolver.with_proxy_hosts at h
  simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, bind_ok, to_vec_string] at h
  rw [into_iter_eq_mkIntoIter, bind_ok] at h
  obtain ⟨v, hl, h⟩ := bind_eq_ok_iff.1 h
  simp only [core.convert.IntoFrom.into, alloc.sync.ArcSlice.Insts.CoreConvertFromVec.from,
    bind_ok, ok.injEq] at h
  subst h
  obtain ⟨h1, h2⟩ := with_proxy_hosts_loop_of_eq_ok _ _ _ _ hl
  refine ⟨⟨?_, rfl, rfl, rfl⟩, h2⟩
  simp only [alloc.vec.Vec.deref, Slice.from_val]
  exact h1

/-- A generic `List` fact (`rdropWhile` commutes with `map`), kept here because no shared file of
`List` lemmas is in the scope of these proofs. -/
theorem rdropWhile_map {α β} (p : β → Bool) (f : α → β) (l : List α) :
    List.rdropWhile p (l.map f) = (List.rdropWhile (p ∘ f) l).map f := by
  induction l using List.reverseRecOn with
  | nil => simp [List.rdropWhile]
  | append_singleton l x ih =>
    rw [List.map_append, List.map_singleton, List.rdropWhile_concat, List.rdropWhile_concat]
    simp only [Function.comp]
    split <;> simp_all

theorem decide_asciiToLower_eq_dotByte (b : U8) :
    decide (asciiToLower b = dotByte) = decide (b = dotByte) := by
  unfold asciiToLower dotByte
  split
  · rename_i h
    have h1 : b ≠ 46#u8 := by intro e; subst e; exact absurd h (by decide)
    have h2 : (⟨BitVec.ofNat 8 (b.val + 32)⟩ : U8) ≠ 46#u8 := by
      intro e
      have := congrArg UScalar.val e
      change (ExtModel.byte (b.val + 32)).val = (46#u8).val at this
      rw [Proofs.External.Byte.byte_val] at this
      have h46 : (46#u8 : U8).val = 46 := rfl
      rw [h46] at this
      omega
    simp [h1, h2]
  · rfl

theorem asciiToLower_idem (b : U8) : asciiToLower (asciiToLower b) = asciiToLower b := by
  unfold asciiToLower
  split
  · rename_i h
    have hv : (ExtModel.byte (b.val + 32)).val = b.val + 32 := by
      rw [Proofs.External.Byte.byte_val]; omega
    change (if 65 ≤ (ExtModel.byte (b.val + 32)).val ∧ (ExtModel.byte (b.val + 32)).val ≤ 90
      then _ else _) = _
    rw [hv, ite_eq_right (by omega)]
  · rfl

theorem trimTrailingDots_map_asciiToLower (l : List U8) :
    trimTrailingDots (l.map asciiToLower) = (trimTrailingDots l).map asciiToLower := by
  unfold trimTrailingDots
  rw [rdropWhile_map]
  congr 2
  funext b
  exact decide_asciiToLower_eq_dotByte b

theorem fields_of_with_proxy_hosts_eq_ok (self r : MetadataAddressResolver)
    (proxies : alloc.vec.Vec String)
    (h : MetadataAddressResolver.with_proxy_hosts
      (core.iter.traits.collect.IntoIteratorVec String) self proxies = ok r) :
    r.unfiltered_hosts.data.val.map Defs.utf8Bytes =
        self.unfiltered_hosts.data.val.map Defs.utf8Bytes ++
          proxies.val.filterMap (fun p => proxyHost (Defs.utf8Bytes p)) ∧
      r.base_ip = self.base_ip ∧ r.base_classes = self.base_classes ∧
      r.lookup = self.lookup := (with_proxy_hosts_of_eq_ok_and_premises self r proxies h).1

theorem length_normalizeHost_le (l : List U8) : (normalizeHost l).length ≤ l.length := by
  unfold normalizeHost trimTrailingDots
  rw [List.length_map]
  exact (List.rdropWhile_prefix (p := fun b => decide (b = dotByte)) (l := l)).length_le

theorem ipv4Class_eq_octets (o0 o1 o2 o3 : Nat) (h0 : o0 < 256) (h1 : o1 < 256)
    (h2 : o2 < 256) (h3 : o3 < 256) (V : Nat)
    (hV : V = o0 * 2^24 + o1 * 2^16 + o2 * 2^8 + o3) :
    ipv4Class V =
      if ipv4Disallowed V = false then .Public
      else if o0 = 127 then .Loopback
      else if (o0 = 10 ∨ (o0 = 172 ∧ o1 / 16 = 1) ∨ (o0 = 192 ∧ o1 = 168)) ∨
          (o0 = 100 ∧ 64 ≤ o1 ∧ o1 ≤ 127) then .Private
      else .Blocked := by
  have hd := ipv4Disallowed_eq_octets o0 o1 o2 o3 h0 h1 h2 h3 V hV
  have e4 := inPrefix_ipv4Prefix_eq_decide 127 0 0 0 8 V (o0 = 127) (by omega)
  have e1 := inPrefix_ipv4Prefix_eq_decide 10 0 0 0 8 V (o0 = 10) (by omega)
  have e2 := inPrefix_ipv4Prefix_eq_decide 172 16 0 0 12 V (o0 = 172 ∧ o1 / 16 = 1) (by omega)
  have e3 := inPrefix_ipv4Prefix_eq_decide 192 168 0 0 16 V (o0 = 192 ∧ o1 = 168) (by omega)
  have e10 := inPrefix_ipv4Prefix_eq_decide 100 64 0 0 10 V (o0 = 100 ∧ o1 / 64 = 1) (by omega)
  unfold ipv4Class ipv4LoopbackPrefix ipv4PrivatePrefixes
  simp only [List.any_cons, List.any_nil, Bool.or_false, e1, e2, e3, e4, e10]
  rw [hd]
  by_cases a127 : o0 = 127
  · simp [a127]
  by_cases p1 : o0 = 10
  · simp [p1]
  by_cases p2 : o0 = 172 ∧ o1 / 16 = 1
  · simp [p2]
  by_cases p3 : o0 = 192 ∧ o1 = 168
  · simp [p3]
  by_cases p4 : o0 = 100 ∧ o1 / 64 = 1
  · have : o0 = 100 ∧ 64 ≤ o1 ∧ o1 ≤ 127 := by omega
    simp [p4, this]
  simp only [a127, p1, p2, p3, p4, decide_false, Bool.false_or, Bool.or_false, ↓reduceIte]
  have q2 : ¬ (o0 = 100 ∧ 64 ≤ o1 ∧ o1 ≤ 127) := by omega
  simp only [q2, Bool.false_eq_true, ↓reduceIte, or_false, false_or, Bool.decide_or,
    Bool.or_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  -- the two conditions are negations of each other (no `omega` over the disjunction: 1.2 s)
  simp only [not_false_eq_true, true_and, ← not_or, ite_not]

theorem of_v4_eq (a : core.net.ip_addr.Ipv4Addr) :
    AddressClass.of (.V4 a) = ok (addressClass (.V4 a)) := by
  suffices h : AddressClass.of (.V4 a) ⦃ (result : AddressClass) =>
      result = addressClass (.V4 a) ⦄ by
    obtain ⟨c, hc, hcv⟩ := exists_ok_of_spec h
    rw [hc, hcv]
  obtain ⟨o0, o1, o2, o3, ho⟩ := a.exists_octets
  obtain ⟨d, hd, hdv⟩ := exists_ok_of_spec
    (transport.auth.AuthorizationManager.is_disallowed_metadata_ipv4_spec a)
  obtain ⟨lb, hlb, hlbv⟩ := exists_ok_of_spec
    (core.net.ip_addr.Ipv4Addr.is_loopback_spec a o0 o1 o2 o3 ho)
  obtain ⟨pb, hpb, hpbv⟩ := exists_ok_of_spec
    (core.net.ip_addr.Ipv4Addr.is_private_spec a o0 o1 o2 o3 ho)
  have hV : ipv4Value a.addrOctets.val =
      o0.val * 2^24 + o1.val * 2^16 + o2.val * 2^8 + o3.val := by
    rw [ho]; simp only [ipv4Value, ofBigEndianDigits, List.map, List.foldl]; ring
  have hcls := ipv4Class_eq_octets o0.val o1.val o2.val o3.val (u8_val_lt o0) (u8_val_lt o1)
    (u8_val_lt o2) (u8_val_lt o3) _ hV
  rw [hV] at hdv
  unfold AddressClass.of addressClass
  simp only [bind_ok, core.net.ip_addr.Ipv4Addr.octets, hd, hlb, hpb]
  rw [hcls, hV, ← hdv]
  have hi0 : a.addrOctets.index_usize 0#usize = ok o0 := by
    obtain ⟨x, hx, hxv⟩ :=
      exists_ok_of_spec (Array.index_usize_spec a.addrOctets 0#usize (by simp))
    rw [hx, hxv]; simp [ho]
  have hi1 : a.addrOctets.index_usize 1#usize = ok o1 := by
    obtain ⟨x, hx, hxv⟩ :=
      exists_ok_of_spec (Array.index_usize_spec a.addrOctets 1#usize (by simp))
    rw [hx, hxv]; simp [ho]
  cases d
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
  · simp only [↓reduceIte, Bool.true_eq_false]
    by_cases h127 : o0.val = 127
    · rw [(hlbv.2 h127)]; simp [h127]
    · have hlbf : lb = false := by
        cases lb
        · rfl
        · exact absurd (hlbv.1 rfl) h127
      rw [hlbf]
      by_cases hp :
          o0.val = 10 ∨ o0.val = 172 ∧ o1.val / 16 = 1 ∨ o0.val = 192 ∧ o1.val = 168
      · rw [hpbv.2 hp]; simp [h127, hp]
      · have hpbf : pb = false := by
          cases pb
          · rfl
          · exact absurd (hpbv.1 rfl) hp
        rw [hpbf]
        simp only [Bool.false_eq_true, ↓reduceIte, hi0, bind_ok, h127, hp, false_or]
        by_cases h100 : o0 = 100#u8
        · have h100v : o0.val = 100 := by rw [h100]; rfl
          rw [ite_eq_left h100]
          simp only [core.ops.range.RangeInclusive.new, bind_ok, hi1]
          obtain ⟨c, hc, hcv⟩ := exists_ok_of_spec
            (core.ops.range.RangeInclusive.contains_u8_spec ⟨64#u8, 127#u8, false⟩ o1)
          rw [hc, bind_ok]
          simp only [Bool.false_eq_true, ↓reduceIte] at hcv
          have h64 : (64#u8 : U8).val = 64 := rfl
          have h127' : (127#u8 : U8).val = 127 := rfl
          rw [h64, h127'] at hcv
          cases c
          · have : ¬ (64 ≤ o1.val ∧ o1.val ≤ 127) := fun hh => Bool.false_ne_true (hcv.2 hh)
            simp [h100v, this]
          · simp [h100v, hcv.1 rfl]
        · have h100v : o0.val ≠ 100 := by
            intro e; apply h100; apply UScalar.eq_of_val_eq; rw [e]; rfl
          rw [ite_eq_right h100]
          simp [h100v]

/-- The statement `AddressClass.of_v6_eq_of_embedded_ipv4_eq_ok_some` of
`Proofs.Transport.MetadataResolver`, which is proved by this lemma; needed here, before it, by
`of_eq`. -/
theorem of_v6_eq_of_embedded_ipv4_eq_ok_some (a : core.net.ip_addr.Ipv6Addr)
    (w : core.net.ip_addr.Ipv4Addr)
    (h : transport.auth.AuthorizationManager.embedded_ipv4 a = ok (some w)) :
    AddressClass.of (.V6 a) = AddressClass.of (.V4 w) := by
  conv_lhs => unfold AddressClass.of
  conv_rhs => unfold AddressClass.of
  simp only [h, bind_ok, core.option.Option.map_or,
    P.Insts.CoreOpsFunctionFnOnceTupleIpv4AddrIpAddr.call_once,
    core.net.ip_addr.IpAddr.V4.constructor]

theorem of_v6_eq_of_embedded_ipv4_eq_ok_none (a : core.net.ip_addr.Ipv6Addr)
    (h : transport.auth.AuthorizationManager.embedded_ipv4 a = ok none) :
    AddressClass.of (.V6 a) = ok (addressClass (.V6 a)) := by
  suffices h : AddressClass.of (.V6 a) ⦃ (result : AddressClass) =>
      result = addressClass (.V6 a) ⦄ by
    obtain ⟨c, hc, hcv⟩ := exists_ok_of_spec h
    rw [hc, hcv]
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, hs⟩ := a.exists_segments
  have hE := transport.auth.AuthorizationManager.embedded_ipv4_spec a
  rw [h, WP.spec_ok, Option.map_none] at hE
  obtain ⟨d, hd, hdv⟩ := exists_ok_of_spec
    (transport.auth.AuthorizationManager.is_disallowed_metadata_ipv6_spec a)
  obtain ⟨lb, hlb, hlbv⟩ := exists_ok_of_spec
    (core.net.ip_addr.Ipv6Addr.is_loopback_spec a s0 s1 s2 s3 s4 s5 s6 s7 hs)
  have hV : ipv6Value a.addrSegments.val = s0.val * 2^112 + s1.val * 2^96 + s2.val * 2^80 +
      s3.val * 2^64 + s4.val * 2^48 + s5.val * 2^32 + s6.val * 2^16 + s7.val := by
    rw [hs, ipv6Value_eight_segments]
  have b0 := u16_val_lt s0; have b1 := u16_val_lt s1; have b2 := u16_val_lt s2
  have b3 := u16_val_lt s3; have b4 := u16_val_lt s4; have b5 := u16_val_lt s5
  have b6 := u16_val_lt s6; have b7 := u16_val_lt s7
  have hany := ipv6DisallowedPrefixes_any_eq_decide _ _ _ _ _ _ _ _
      (u16_val_lt s0) (u16_val_lt s1) (u16_val_lt s2) (u16_val_lt s3) (u16_val_lt s4)
      (u16_val_lt s5) (u16_val_lt s6) (u16_val_lt s7) _ hV
  have hlo : inPrefix ipv6Loopback (ipv6Value a.addrSegments.val) = decide (s0.val = 0 ∧
      s1.val = 0 ∧ s2.val = 0 ∧ s3.val = 0 ∧ s4.val = 0 ∧ s5.val = 0 ∧ s6.val = 0 ∧
      s7.val = 1) :=
    inPrefix_ipv6Prefix_eq_decide [0, 0, 0, 0, 0, 0, 0, 1] 128 0 0 0 0 0 0 0 1 rfl
    (ipv6Value a.addrSegments.val)
    (s0.val = 0 ∧ s1.val = 0 ∧ s2.val = 0 ∧ s3.val = 0 ∧ s4.val = 0 ∧ s5.val = 0 ∧
      s6.val = 0 ∧ s7.val = 1) (by rw [hV]; omega)
  have hul : inPrefix ipv6UniqueLocal (ipv6Value a.addrSegments.val) =
      decide (s0.val / 512 = 126) :=
    inPrefix_ipv6Prefix_eq_decide [0xfc00] 7 0xfc00 0 0 0 0 0 0 0 rfl
    (ipv6Value a.addrSegments.val) (s0.val / 512 = 126) (by rw [hV]; omega)
  have hdis : ipv6Disallowed (ipv6Value a.addrSegments.val) =
      ipv6DisallowedPrefixes.any (fun p => inPrefix p (ipv6Value a.addrSegments.val)) := by
    unfold ipv6Disallowed; rw [← hE]
  unfold AddressClass.of addressClass ipv6Class
  dsimp only
  rw [← hE]
  simp only [h, bind_ok, core.option.Option.map_or, hd, hlb]
  rw [hlo, hul]
  rw [hdis, hany] at hdv
  cases d
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    have hdv' := hdv.symm
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hdv'
    obtain ⟨n1, _, _, _, n5, _⟩ := hdv'
    simp only [n1, n5, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [hdis, hany, ← hdv]; rfl
  · simp only [↓reduceIte]
    cases lb
    · have hl : ¬ (s0.val = 0 ∧ s1.val = 0 ∧ s2.val = 0 ∧ s3.val = 0 ∧ s4.val = 0 ∧
          s5.val = 0 ∧ s6.val = 0 ∧ s7.val = 1) := fun hh => Bool.false_ne_true (hlbv.2 hh)
      simp only [Bool.false_eq_true, ↓reduceIte, hl, decide_false,
        core.net.ip_addr.Ipv6Addr.segments, bind_ok]
      have hi0 : a.addrSegments.index_usize 0#usize = ok s0 := by
        obtain ⟨x, hx,
            hxv⟩ := exists_ok_of_spec (Array.index_usize_spec a.addrSegments 0#usize (by simp))
        rw [hx, hxv]; simp [hs]
      simp only [hi0, bind_ok, lift]
      by_cases hu : s0.val / 512 = 126
      · rw [ite_eq_left ((and_65024_eq_64512_iff s0).2 hu)]; simp [hu]
      · rw [ite_eq_right (fun hh => hu ((and_65024_eq_64512_iff s0).1 hh))]
        simp only [hu, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        rw [hdis, hany, ← hdv]; rfl
    · simp [hlbv.1 rfl]

theorem addressClass_eq_eq (a b : AddressClass) :
    AddressClass.Insts.CoreCmpPartialEqAddressClass.eq a b = ok (decide (a = b)) := by
  cases a <;> cases b <;> simp [AddressClass.Insts.CoreCmpPartialEqAddressClass.eq,
      AddressClass.read_discriminant]

theorem contains_addressClass (s : Slice AddressClass) (c : AddressClass) :
    core.slice.Slice.contains AddressClass.Insts.CoreCmpPartialEqAddressClass s c =
      ok (decide (c ∈ s.val)) := by
  unfold core.slice.Slice.contains
  rw [anyM_eq_ok _ (fun x => decide (c = x)) (fun x => addressClass_eq_eq c x)]
  congr 1
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨x, hx, hcx⟩; rw [decide_eq_true_iff] at hcx; subst hcx; exact hx
  · intro hc; exact ⟨c, hc, decide_eq_true rfl⟩

theorem contains_string (s : Slice String) (c : String) :
    core.slice.Slice.contains alloc.string.String.Insts.CoreCmpPartialEqString s c =
      ok (decide (c ∈ s.val)) := by
  unfold core.slice.Slice.contains
  rw [anyM_eq_ok (alloc.string.String.Insts.CoreCmpPartialEqString.eq c) (fun x => decide (c = x))
      (fun x => rfl)]
  congr 1
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨x, hx, hcx⟩; rw [decide_eq_true_iff] at hcx; subst hcx; exact hx
  · intro hc; exact ⟨c, hc, decide_eq_true rfl⟩

theorem is_allowed_eq («class» : AddressClass) (base_classes : Slice AddressClass) :
    MetadataAddressResolver.is_allowed «class» base_classes =
      ok (isAllowed «class» base_classes.val) := by
  cases «class» <;> simp [MetadataAddressResolver.is_allowed, contains_addressClass, isAllowed]

theorem literal_ip_eq (target : url.Url) :
    literal_ip target = ok (literalIp (ExtModel.urlHost target)) := by
  unfold literal_ip
  simp only [url.Url.host, bind_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch]
  cases h : ExtModel.urlHost target with
  | none => simp [literalIp,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
  | some host => cases host <;> simp [literalIp, hostIp]

theorem of_eq (addr : core.net.ip_addr.IpAddr) :
    AddressClass.of addr = ok (addressClass addr) := by
  cases addr with
  | V4 a => exact of_v4_eq a
  | V6 a =>
    obtain ⟨o, ho, hov⟩ :=
      exists_ok_of_spec (transport.auth.AuthorizationManager.embedded_ipv4_spec a)
    cases o with
    | none => exact of_v6_eq_of_embedded_ipv4_eq_ok_none a ho
    | some w =>
      rw [of_v6_eq_of_embedded_ipv4_eq_ok_some a w ho, of_v4_eq]
      simp only [addressClass, ipv6Class, ← hov, Option.map_some]

/-- The domain arm of `is_loopback_metadata_host`, as one equation. -/
theorem is_loopback_metadata_host_domain_eq (d : Str) :
    transport.auth.AuthorizationManager.is_loopback_metadata_host (url.host.Host.Domain d) =
      match strOfBytes? (normalizeHost d.val) with
      | some _ => ok (isLocalhostName d.val)
      | none => fail .undef := by
  unfold transport.auth.AuthorizationManager.is_loopback_metadata_host
  simp only [prim.trim_end_dots]
  rw [bind_ok_str]
  simp only [alloc.str.Str.to_ascii_lowercase, Slice.from_val, ←
      normalizeHost_eq_map_dropTrailingDots]
  cases hs : strOfBytes? (normalizeHost d.val) with
  | none =>
    dsimp only
    rw [bind_fail]
  | some u =>
    rw [strOfBytes?_eq_some_iff] at hs
    simp only [bind_ok, alloc.string.String.Insts.CoreCmpPartialEqShared0Str.eq]
    have hlen : u.utf8ByteSize ≤ Usize.max := by
      rw [← length_utf8, ← hs]; exact le_trans (length_normalizeHost_le _) d.property
    have hl : ∀ h, (toStr "localhost" h).val = utf8 "localhost" := fun h => toStr_val _ h
    have hdl : ∀ h, (toStr ".localhost" h).val = utf8 ".localhost" := fun h => toStr_val _ h
    unfold isLocalhostName
    rw [utf8Bytes_eq_utf8, utf8Bytes_eq_utf8, hs]
    by_cases h1 : utf8 u = utf8 "localhost"
    · simp [h1, hl]
    · simp only [hl, h1, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
      rw [deref_eq u hlen, bind_ok_str]
      simp only [prim.ends_with, Slice.from_val, hdl]

theorem is_loopback_metadata_host_domain_eq_fail (d : Str) (h : ¬ ExtModel.IsUtf8 d.val) :
    transport.auth.AuthorizationManager.is_loopback_metadata_host (url.host.Host.Domain d) =
      fail .undef := by
  rw [is_loopback_metadata_host_domain_eq]
  cases hs : strOfBytes? (normalizeHost d.val) with
  | none => rfl
  | some s =>
    exfalso; apply h
    rw [strOfBytes?_eq_some_iff, normalizeHost_eq_map_dropTrailingDots] at hs
    exact isUtf8_of_isUtf8_dropTrailingDots (isUtf8_of_isUtf8_map_asciiLowercase ⟨s, hs⟩)

theorem is_loopback_metadata_host_eq (host : url.host.Host Str)
    (h_utf8 : ∀ d, host = url.host.Host.Domain d → ExtModel.IsUtf8 d.val) :
    transport.auth.AuthorizationManager.is_loopback_metadata_host host =
      ok (isLoopbackHost host) := by
  cases host with
  | Domain d =>
    rw [is_loopback_metadata_host_domain_eq]
    have hu := Proofs.External.MetadataResolver.isUtf8_map_asciiLowercase
      (Proofs.External.MetadataResolver.isUtf8_dropTrailingDots (h_utf8 d rfl))
    rw [← normalizeHost_eq_map_dropTrailingDots] at hu
    obtain ⟨u, hu⟩ := hu
    rw [hu, strOfBytes?_utf8]
    rfl
  | Ipv4 a =>
    obtain ⟨o0, o1, o2, o3, ho⟩ := a.exists_octets
    obtain ⟨r, hr, hrv⟩ :=
      exists_ok_of_spec (core.net.ip_addr.Ipv4Addr.is_loopback_spec a o0 o1 o2 o3 ho)
    unfold transport.auth.AuthorizationManager.is_loopback_metadata_host
    dsimp only
    rw [hr]
    have hV : ipv4Value a.addrOctets.val =
        o0.val * 2^24 + o1.val * 2^16 + o2.val * 2^8 + o3.val := by
      rw [ho]; simp only [ipv4Value, ofBigEndianDigits, List.map, List.foldl]; ring
    have := u8_val_lt o0; have := u8_val_lt o1; have := u8_val_lt o2; have := u8_val_lt o3
    have e := inPrefix_ipv4Prefix_eq_decide 127 0 0 0 8 (ipv4Value a.addrOctets.val) (o0.val = 127)
      (by rw [hV]; omega)
    simp only [isLoopbackHost, ipv4LoopbackPrefix, e]
    cases r <;> simp_all
  | Ipv6 a =>
    obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, hs⟩ := a.exists_segments
    obtain ⟨r, hr, hrv⟩ := exists_ok_of_spec
      (core.net.ip_addr.Ipv6Addr.is_loopback_spec a s0 s1 s2 s3 s4 s5 s6 s7 hs)
    unfold transport.auth.AuthorizationManager.is_loopback_metadata_host
    dsimp only
    rw [hr]
    have hV : ipv6Value a.addrSegments.val = s0.val * 2^112 + s1.val * 2^96 + s2.val * 2^80 +
        s3.val * 2^64 + s4.val * 2^48 + s5.val * 2^32 + s6.val * 2^16 + s7.val := by
      rw [hs, ipv6Value_eight_segments]
    have b0 := u16_val_lt s0; have b1 := u16_val_lt s1; have b2 := u16_val_lt s2
    have b3 := u16_val_lt s3; have b4 := u16_val_lt s4; have b5 := u16_val_lt s5
    have b6 := u16_val_lt s6; have b7 := u16_val_lt s7
    have hlo : inPrefix ipv6Loopback (ipv6Value a.addrSegments.val) = decide (s0.val = 0 ∧
        s1.val = 0 ∧ s2.val = 0 ∧ s3.val = 0 ∧ s4.val = 0 ∧ s5.val = 0 ∧ s6.val = 0 ∧
        s7.val = 1) :=
      inPrefix_ipv6Prefix_eq_decide [0, 0, 0, 0, 0, 0, 0, 1] 128 0 0 0 0 0 0 0 1 rfl
      (ipv6Value a.addrSegments.val) _ (by rw [hV]; omega)
    simp only [isLoopbackHost, hlo]
    cases r <;> simp_all

/-- `with_base_url` as an equation, under the UTF-8 premise. -/
theorem exists_with_base_url_eq_ok (base_url : url.Url) (lookup : Lookup)
    (h_utf8 : ∀ d, ExtModel.urlHost base_url = some (url.host.Host.Domain d) →
      ExtModel.IsUtf8 d.val) :
    ∃ r, MetadataAddressResolver.with_base_url base_url lookup = ok r ∧
      r.base_ip = literalIp (ExtModel.urlHost base_url) ∧
      r.unfiltered_hosts.data.val = [] ∧
      r.base_classes.data.val = baseClasses (ExtModel.urlHost base_url) ∧
      r.lookup = lookup := by
  unfold MetadataAddressResolver.with_base_url
  rw [literal_ip_eq, bind_ok]
  simp only [url.Url.host, bind_ok]
  cases hh : ExtModel.urlHost base_url with
  | none =>
    simp [core.convert.IntoFrom.into, alloc.sync.ArcSlice.Insts.CoreConvertFromVec.from,
      baseClasses, alloc.vec.Vec.deref, alloc.vec.Vec.new]
  | some host =>
    cases host with
    | Domain d =>
      simp only
      rw [is_loopback_metadata_host_eq _ (by intro d' e; cases e; exact h_utf8 _ hh), bind_ok]
      simp only [isLoopbackHost]
      by_cases hl : isLocalhostName d.val = true
      · simp only [hl, ↓reduceIte, lift, alloc.slice.Slice.into_vec, bind_ok,
          core.convert.IntoFrom.into, alloc.sync.ArcSlice.Insts.CoreConvertFromVec.from,
          alloc.vec.Vec.deref, alloc.vec.Vec.new, alloc.vec.Vec.from_val, ok.injEq, baseClasses,
          exists_eq_left', Slice.from_val, and_true, true_and]
        rfl
      · simp only [hl, Bool.false_eq_true, ↓reduceIte, alloc.vec.Vec.new,
          core.convert.IntoFrom.into, alloc.sync.ArcSlice.Insts.CoreConvertFromVec.from,
          alloc.vec.Vec.deref, alloc.vec.Vec.from_val, bind_ok, ok.injEq, baseClasses,
          exists_eq_left', Slice.from_val, and_self]
    | Ipv4 a | Ipv6 a =>
      simp only [of_eq, lift, alloc.slice.Slice.into_vec, bind_ok, core.convert.IntoFrom.into,
        alloc.sync.ArcSlice.Insts.CoreConvertFromVec.from, alloc.vec.Vec.deref,
        alloc.vec.Vec.new, alloc.vec.Vec.from_val, ok.injEq, baseClasses, exists_eq_left',
        Slice.from_val, and_true, true_and]
      rfl

theorem with_base_url_eq_fail (base_url : url.Url) (lookup : Lookup) (d : Str)
    (h_host : ExtModel.urlHost base_url = some (url.host.Host.Domain d))
    (h : ¬ ExtModel.IsUtf8 d.val) :
    MetadataAddressResolver.with_base_url base_url lookup = fail .undef := by
  unfold MetadataAddressResolver.with_base_url
  rw [literal_ip_eq, bind_ok]
  simp only [url.Url.host, bind_ok, h_host]
  rw [is_loopback_metadata_host_domain_eq_fail d h, bind_fail, bind_fail]

theorem with_base_url_of_eq_ok (base_url : url.Url) (lookup : Lookup) (r : MetadataAddressResolver)
    (h : MetadataAddressResolver.with_base_url base_url lookup = ok r) :
      r.base_ip = literalIp (ExtModel.urlHost base_url) ∧
      r.unfiltered_hosts.data.val = [] ∧
      r.base_classes.data.val = baseClasses (ExtModel.urlHost base_url) ∧
      r.lookup = lookup := by
  by_cases hu : ∀ d, ExtModel.urlHost base_url = some (url.host.Host.Domain d) →
      ExtModel.IsUtf8 d.val
  · obtain ⟨r', hr', h'⟩ := exists_with_base_url_eq_ok base_url lookup hu
    rw [hr', ok.injEq] at h; subst h; exact h'
  · push Not at hu
    obtain ⟨d, hd, hn⟩ := hu
    rw [with_base_url_eq_fail base_url lookup d hd hn] at h
    exact absurd h.symm ok_not_fail

theorem new_eq_bind (base_url : url.Url) :
    MetadataAddressResolver.new base_url =
      (do
        let r ← MetadataAddressResolver.with_base_url base_url ExtModel.systemLookup
        MetadataAddressResolver.with_proxy_hosts
          (core.iter.traits.collect.IntoIteratorVec String) r ExtModel.proxyEnvValues) := by
  unfold MetadataAddressResolver.new
  simp only [prim.system_lookup, prim.proxy_env_values, bind_ok]

theorem ip_eq_socketIp (x : core.net.socket_addr.SocketAddr) :
    core.net.socket_addr.SocketAddr.ip x = ok (socketIp x) := by
  cases x <;> rfl

theorem exists_allowed_addresses_loop_eq_ok : ∀ (rs : List core.net.socket_addr.SocketAddr)
    (it : alloc.vec.into_iter.IntoIter core.net.socket_addr.SocketAddr)
    (_ : (show alloc.vec.Vec core.net.socket_addr.SocketAddr from it).val = rs)
    (a : alloc.sync.Arc (Slice AddressClass)) (acc : alloc.vec.Vec core.net.socket_addr.SocketAddr)
    (_ : acc.val.length + rs.length ≤ Usize.max),
    ∃ v, MetadataAddressResolver.allowed_addresses_loop it a acc = ok v ∧
      v.val = acc.val ++ rs.filter (fun x => isAllowed (addressClass (socketIp x)) a.data.val)
  | [], it, hit, a, acc, hl => by
    refine ⟨acc, ?_, by simp⟩
    unfold MetadataAddressResolver.allowed_addresses_loop
    rw [loop]
    dsimp only
    rw [MetadataAddressResolver.allowed_addresses_loop.body]
    unfold alloc.vec.into_iter.IteratorIntoIter.next
    split
    · simp
    · rename_i hd tl h; rw [hit] at h; simp at h
  | x :: rs, it, hit, a, acc, hl => by
    unfold MetadataAddressResolver.allowed_addresses_loop
    rw [loop]
    dsimp only
    rw [MetadataAddressResolver.allowed_addresses_loop.body]
    unfold alloc.vec.into_iter.IteratorIntoIter.next
    split
    · rename_i h; rw [hit] at h; simp at h
    · rename_i hd tl h
      rw [hit] at h
      simp only [List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1 h2
      have hl' : acc.val.length + rs.length + 1 ≤ Usize.max := by omega
      simp only [bind_ok, uncurry, ip_eq_socketIp, of_eq,
          alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, is_allowed_eq]
      by_cases hal : isAllowed (addressClass (socketIp x)) a.data.val = true
      · rw [ite_eq_left hal, push_eq_ok acc x (by omega), bind_ok, bind_ok]
        dsimp only
        obtain ⟨v, hv, hvv⟩ := exists_allowed_addresses_loop_eq_ok rs
          (alloc.vec.Vec.from rs (by omega)) (by simp) a
          (alloc.vec.Vec.from (acc.val ++ [x])
            (by rw [List.length_append, List.length_singleton]; omega))
          (by rw [alloc.vec.Vec.from_val, List.length_append, List.length_singleton]; omega)
        refine ⟨v, hv, ?_⟩
        rw [hvv]; simp [hal]
      · rw [ite_eq_right hal, bind_ok]
        dsimp only
        obtain ⟨v, hv, hvv⟩ := exists_allowed_addresses_loop_eq_ok rs
          (alloc.vec.Vec.from rs (by omega)) (by simp) a acc (by omega)
        refine ⟨v, hv, ?_⟩
        rw [hvv]; simp [hal]

theorem to_vec_addressClass (s : Slice AddressClass) :
    alloc.slice.Slice.to_vec AddressClass.Insts.CoreCloneClone s = ok ⟨s⟩ := by
  obtain ⟨v, hv, hvv⟩ := Proofs.External.WP.exists_ok_of_spec
    (alloc.slice.Slice.to_vec_spec AddressClass.Insts.CoreCloneClone s (fun x _ => rfl))
  rw [hv]; cases v; simp_all

theorem exists_allowing_private_addresses_eq_ok (self : MetadataAddressResolver)
    (h_room : AddressClass.Private ∈ self.base_classes.data.val ∨
      self.base_classes.data.val.length < Usize.max) :
    ∃ r, MetadataAddressResolver.allowing_private_addresses self = ok r ∧
      r.base_classes.data.val = withPrivate self.base_classes.data.val ∧
      r.base_ip = self.base_ip ∧ r.unfiltered_hosts = self.unfiltered_hosts ∧
      r.lookup = self.lookup := by
  unfold MetadataAddressResolver.allowing_private_addresses
  simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, bind_ok, contains_addressClass,
      to_vec_addressClass]
  by_cases hp : AddressClass.Private ∈ self.base_classes.data.val
  · simp [hp, withPrivate]
  · have hl := h_room.resolve_left hp
    simp only [hp, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [push_eq_ok ⟨self.base_classes.data⟩ _ hl, bind_ok]
    simp only [core.convert.IntoFrom.into, alloc.sync.ArcSlice.Insts.CoreConvertFromVec.from,
      alloc.vec.Vec.deref, alloc.vec.Vec.from_val, bind_ok, ok.injEq, withPrivate, hp, ↓reduceIte,
      exists_eq_left', Slice.from_val, List.append_cancel_right_eq, and_self, and_true]
    rfl

theorem allowing_private_addresses_eq_fail (self : MetadataAddressResolver)
    (h : ¬ (AddressClass.Private ∈ self.base_classes.data.val ∨
      self.base_classes.data.val.length < Usize.max)) :
    MetadataAddressResolver.allowing_private_addresses self = fail .maximumSizeExceeded := by
  rw [not_or] at h
  unfold MetadataAddressResolver.allowing_private_addresses
  simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, bind_ok, contains_addressClass,
      to_vec_addressClass, h.1,
    decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [push_eq_fail ({ slice := self.base_classes.data } : alloc.vec.Vec AddressClass) _ h.2,
      bind_fail]

theorem allowing_private_addresses_of_eq_ok (self r : MetadataAddressResolver)
    (h : MetadataAddressResolver.allowing_private_addresses self = ok r) :
      r.base_classes.data.val = withPrivate self.base_classes.data.val ∧
      r.base_ip = self.base_ip ∧ r.unfiltered_hosts = self.unfiltered_hosts ∧
      r.lookup = self.lookup := by
  by_cases hr : AddressClass.Private ∈ self.base_classes.data.val ∨
      self.base_classes.data.val.length < Usize.max
  · obtain ⟨r', h1, h2⟩ := exists_allowing_private_addresses_eq_ok self hr
    rw [h1, ok.injEq] at h; subst h; exact h2
  · rw [allowing_private_addresses_eq_fail self hr] at h; exact absurd h.symm ok_not_fail

theorem exists_with_base_url_eq_ok_of_new_eq_ok (base_url : url.Url) (r : MetadataAddressResolver)
    (h : MetadataAddressResolver.new base_url = ok r) :
    ∃ m, MetadataAddressResolver.with_base_url base_url ExtModel.systemLookup = ok m ∧
      MetadataAddressResolver.with_proxy_hosts (core.iter.traits.collect.IntoIteratorVec String) m
        ExtModel.proxyEnvValues = ok r := by
  rw [new_eq_bind] at h
  exact bind_eq_ok_iff.1 h

theorem exists_normalize_host_eq_ok (host : Str) (h : IsUtf8 host.val) :
    ∃ s, normalize_host host = ok s ∧ utf8 s = normalizeHost host.val := by
  have hu := Proofs.External.MetadataResolver.isUtf8_map_asciiLowercase
      (Proofs.External.MetadataResolver.isUtf8_dropTrailingDots h)
  rw [← normalizeHost_eq_map_dropTrailingDots] at hu
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, ?_, hu.symm⟩
  rw [normalize_host_eq, hu, strOfBytes?_utf8]

theorem exists_proxy_host_eq_ok (p : String) (hf : ProxyFits p) (hu : ProxyHostUtf8 p) :
    ∃ o, proxy_host p = ok o := by
  rw [proxy_host_eq_proxyHostTail p hf, proxyHostTail]
  cases hp : ExtModel.urlParse (proxyUrl (Defs.utf8Bytes p)) with
  | Err e => exact ⟨none, rfl⟩
  | Ok u =>
    cases hh : ExtModel.urlHostStr u with
    | none => exact ⟨none, by simp only [hh]⟩
    | some hs =>
      obtain ⟨s, h1, -⟩ := exists_normalize_host_eq_ok hs (hu u hs hp hh)
      exact ⟨some s, by simp only [hh, h1, bind_ok]⟩

theorem exists_with_proxy_hosts_loop_eq_ok : ∀ (ps : List String) (hps : ps.length ≤ Usize.max)
    (acc : alloc.vec.Vec String) (_ : ∀ p ∈ ps, ProxyFits p ∧ ProxyHostUtf8 p)
    (_ : acc.val.length + (ps.filterMap (fun p => proxyHost (Defs.utf8Bytes p))).length ≤
      Usize.max),
    ∃ v, MetadataAddressResolver.with_proxy_hosts_loop
      (core.iter.traits.collect.IntoIteratorVec String) (mkIntoIter ps hps) acc = ok v
  | [], hps, acc, hf, hl => by
    unfold MetadataAddressResolver.with_proxy_hosts_loop
    rw [loop]
    simp only [MetadataAddressResolver.with_proxy_hosts_loop.body]
    rw [next_mkIntoIter_nil, bind_ok]
    simp only [uncurry, bind_ok]
    exact ⟨acc, rfl⟩
  | p :: ps, hps, acc, hf, hl => by
    unfold MetadataAddressResolver.with_proxy_hosts_loop
    rw [loop]
    simp only [MetadataAddressResolver.with_proxy_hosts_loop.body]
    rw [next_mkIntoIter_cons, bind_ok]
    simp only [uncurry]
    obtain ⟨o, ho⟩ := exists_proxy_host_eq_ok p (hf p (by simp)).1 (hf p (by simp)).2
    have hov := (proxy_host_of_eq_ok ho).1
    have hf' : ∀ q ∈ ps, ProxyFits q ∧ ProxyHostUtf8 q := fun q hq => hf q (by simp [hq])
    rw [ho, bind_ok]
    cases o with
    | none =>
      simp only [bind_ok]
      rw [List.filterMap_cons, ← hov] at hl
      exact exists_with_proxy_hosts_loop_eq_ok ps _ acc hf' hl
    | some host =>
      simp only
      rw [List.filterMap_cons, ← hov] at hl
      simp only [Option.map_some, List.length_cons] at hl
      rw [push_eq_ok acc host (by omega), bind_ok, bind_ok]
      exact exists_with_proxy_hosts_loop_eq_ok ps _ _ hf'
        (by rw [alloc.vec.Vec.from_val, List.length_append, List.length_singleton]; omega)

theorem allowing_private_addresses_eq_ok_self (s : MetadataAddressResolver)
    (h : AddressClass.Private ∈ s.base_classes.data.val) :
    MetadataAddressResolver.allowing_private_addresses s = ok s := by
  unfold MetadataAddressResolver.allowing_private_addresses
  simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, bind_ok, contains_addressClass, h,
    decide_true, ↓reduceIte]

end Proofs.Transport.MetadataResolver
