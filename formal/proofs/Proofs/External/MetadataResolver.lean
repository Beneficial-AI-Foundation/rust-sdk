/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Proofs.External.Byte
public import Proofs.External.String
public import Proofs.External.WP
public import Mathlib.Data.List.DropRight

@[expose] public section

/-!
# Specs of the externals of the `metadata_resolver.rs` address policy (N01, N03–N11, patch 05)

Spec theorems for the models of `formal/trusted/Rmcp/FunsExternal.lean`, section
"`metadata_resolver.rs` address policy": the five `metadata_resolver::prim` functions that
translation patch 05 adds (`crates/rmcp/src/transport/auth/metadata_resolver.rs` in the patched
copy) and the standard-library and `url` functions that the targets reach. Each external has a
theorem named after it with `_spec`; where the external takes a function or a trait instance whose
behaviour is not fixed, the theorem is not a `step` lemma: `call_once_spec` is the equation
`call_once f a = f a` (every outcome of `f`), and `map_or_spec` takes the closure's behaviour as a
hypothesis (as `Option`'s `eq_spec` does); `call_once_ip_addr_v4_spec` and `map_or_ip_addr_v4_spec`
give the one instance of the translation (`IpAddr::V4` passed to `Option::map_or` in
`AddressClass::of`). The opaque values (`ExtModel.urlParse`, `ExtModel.urlHost`,
`ExtModel.urlHostStr`, `ExtModel.systemLookup`, `ExtModel.proxyEnvValues`) appear in the
postconditions unopened: their laws are hypotheses of the statements that need them (human decision
2026-11-25). `proxy_env_values_spec` only says that the function returns the one reading
`proxyEnvValues`; the review rule at `ExtModel.proxyEnvValues` restricts every other statement that
names it.

Section "ASCII lowercase" proves that mapping `A`–`Z` to `a`–`z` keeps the UTF-8 bytes of a string
UTF-8 (`exists_map_asciiLowercase_utf8_eq_utf8`), as `Proofs.External.Skill` does for uppercase,
from the generic character-level facts of `Proofs.External.String`;
`to_ascii_lowercase_spec_of_eq_utf8` uses it, `to_ascii_lowercase_spec_of_isUtf8` is the same under
the UTF-8 premise `ExtModel.IsUtf8` (where a statement may assume it: the docstring of
`ExtModel.IsUtf8`), `isUtf8_map_asciiLowercase` says that the mapping keeps that premise, and
`to_ascii_lowercase_eq_fail` gives the other branch of the model (bytes whose lowercase mapping is
not UTF-8, which no Rust `&str` has). Section "Trailing dots" proves that `dropTrailingDots` is the
identity on bytes without a trailing `.` (`dropTrailingDots_eq_self_of_getLast?_ne`), that its
result ends with no `.` (`val_ne_of_mem_getLast?_dropTrailingDots`) and that it keeps the UTF-8
premise (`isUtf8_dropTrailingDots`: a trailing `.` is the one byte 46 and the last byte of any other
character is not 46); no external spec uses them, they are kept for the specs of N11
`normalize_host` and of `is_loopback_metadata_host` (each `prim::trim_end_dots` followed by
`to_ascii_lowercase`; N10 `literal_ip` does not call `trim_end_dots`). Section "Converses" proves
the converses `isUtf8_of_isUtf8_map_asciiLowercase` and `isUtf8_of_isUtf8_dropTrailingDots`, used
by the failure statements of N11 and of `is_loopback_metadata_host`. Section "Evaluation of the
models" checks the exact models on small inputs by kernel evaluation (`decide`).
-/

open Aeneas Aeneas.Std Result
open rmcp

namespace Proofs.External.MetadataResolver

open ExtModel Proofs.External.Byte Proofs.External.Utf8

/-! ### ASCII lowercase -/

/-- `asciiLowercase` leaves a byte of at least 128 unchanged. -/
theorem asciiLowercase_eq_self_of_le_val {b : U8} (h : 128 ≤ b.val) : asciiLowercase b = b := by
  rw [asciiLowercase, ite_eq_right (by omega)]

/-- `asciiLowercase` maps an ASCII byte to an ASCII byte. -/
theorem val_asciiLowercase_lt_of_lt {b : U8} (h : b.val < 128) : (asciiLowercase b).val < 128 := by
  unfold asciiLowercase
  split
  · rw [byte_val]; omega
  · exact h

/-- The bytes of a string of characters, with ASCII uppercase letters mapped to lowercase, are
the UTF-8 bytes of a string. -/
theorem exists_map_asciiLowercase_utf8_ofList_eq_utf8 : ∀ cs : List Char,
    ∃ u, (utf8 (String.ofList cs)).map asciiLowercase = utf8 u
  | [] => ⟨"", by rw [utf8_ofList, List.flatMap_nil]; rfl⟩
  | c :: cs => by
    obtain ⟨u, hu⟩ := exists_map_asciiLowercase_utf8_ofList_eq_utf8 cs
    have hc : ∃ v, (utf8 (String.ofList [c])).map asciiLowercase = utf8 v := by
      by_cases hlt : c.toNat < 128
      · rw [utf8_ofList_singleton_ascii c hlt, List.map_cons, List.map_nil]
        have hb0 : (byte c.toNat).val < 128 := by rw [byte_val]; omega
        have hx : ∀ b ∈ [asciiLowercase (byte c.toNat)], b.val < 128 := by
          intro b hb
          rw [List.mem_singleton] at hb
          rw [hb]; exact val_asciiLowercase_lt_of_lt hb0
        exact ⟨_, (utf8_ofList_ascii [asciiLowercase (byte c.toNat)] hx).symm⟩
      · refine ⟨String.ofList [c], ?_⟩
        conv => rhs; rw [← List.map_id (utf8 (String.ofList [c]))]
        apply List.map_congr_left
        intro b hb
        exact asciiLowercase_eq_self_of_le_val
          (le_val_of_mem_utf8_ofList_singleton (Nat.not_lt.1 hlt) b hb)
    obtain ⟨v, hv⟩ := hc
    exact ⟨v ++ u, by rw [utf8_ofList_cons, List.map_append, hv, hu, utf8_append]⟩

/-- **`to_ascii_lowercase` keeps UTF-8**: the UTF-8 bytes of a string with ASCII uppercase
letters mapped to lowercase are the UTF-8 bytes of a string. -/
theorem exists_map_asciiLowercase_utf8_eq_utf8 (t : String) :
    ∃ u, (utf8 t).map asciiLowercase = utf8 u := by
  have := exists_map_asciiLowercase_utf8_ofList_eq_utf8 t.toList
  rwa [String.ofList_toList] at this

/-- `to_ascii_lowercase` keeps the UTF-8 premise: if `l` is UTF-8, so are its bytes with ASCII
uppercase letters mapped to lowercase. -/
theorem isUtf8_map_asciiLowercase {l : List U8} (h : IsUtf8 l) :
    IsUtf8 (l.map asciiLowercase) := by
  obtain ⟨t, rfl⟩ := h
  obtain ⟨u, hu⟩ := exists_map_asciiLowercase_utf8_eq_utf8 t
  exact ⟨u, hu⟩

/-! ### Trailing dots -/

/-- Without a trailing `.`, `dropTrailingDots` is the identity. -/
theorem dropTrailingDots_eq_self_of_getLast?_ne {l : List U8}
    (h : ∀ b ∈ l.getLast?, b.val ≠ 46) : dropTrailingDots l = l := by
  unfold dropTrailingDots
  cases hl : l.reverse with
  | nil => rw [List.dropWhile_nil, ← hl, List.reverse_reverse]
  | cons b rest =>
    have hb : b ∈ l.getLast? := by
      rw [List.getLast?_eq_head?_reverse, hl, List.head?_cons, Option.mem_def]
    have hne := h b hb
    rw [List.dropWhile_cons, ite_eq_right (by simpa using hne), ← hl, List.reverse_reverse]

/-- After `dropTrailingDots` the bytes end with no `.`. -/
theorem val_ne_of_mem_getLast?_dropTrailingDots (l : List U8) :
    ∀ b ∈ (dropTrailingDots l).getLast?, b.val ≠ 46 := by
  intro b hb
  rw [dropTrailingDots, List.getLast?_reverse, Option.mem_def] at hb
  have := List.head?_dropWhile_not (fun b : U8 => decide (b.val = 46)) l.reverse
  rw [hb] at this
  simpa using this

/-- `dropTrailingDots` of bytes ending with a `.` drops that `.` and continues. -/
theorem dropTrailingDots_append_dot (l : List U8) :
    dropTrailingDots (l ++ [byte 46]) = dropTrailingDots l := by
  rw [dropTrailingDots, dropTrailingDots, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.dropWhile_cons_of_pos (by rw [byte_val]; decide)]

/-- `dropTrailingDots` of the UTF-8 bytes of a string of characters are the UTF-8 bytes of a
string: a trailing `.` is the one byte 46, and the last byte of any other character is not 46. -/
theorem exists_dropTrailingDots_utf8_ofList_eq_utf8 (cs : List Char) :
    ∃ u, dropTrailingDots (utf8 (String.ofList cs)) = utf8 u := by
  induction cs using List.reverseRecOn with
  | nil => exact ⟨"", by rw [dropTrailingDots, utf8_ofList, List.flatMap_nil]; rfl⟩
  | append_singleton cs c ih =>
    have happ : utf8 (String.ofList (cs ++ [c])) =
        utf8 (String.ofList cs) ++ utf8 (String.ofList [c]) := by
      rw [utf8_ofList, utf8_ofList, utf8_ofList, List.flatMap_append]
    by_cases hdot : c.toNat = 46
    · rw [happ, utf8_ofList_singleton_ascii c (by omega), hdot, dropTrailingDots_append_dot]
      exact ih
    · refine ⟨String.ofList (cs ++ [c]), dropTrailingDots_eq_self_of_getLast?_ne ?_⟩
      intro b hb
      have hne : utf8 (String.ofList [c]) ≠ [] := by
        rw [utf8_ofList, List.flatMap_cons, List.flatMap_nil, List.append_nil, ne_eq,
          List.map_eq_nil_iff]
        exact String.utf8EncodeChar_ne_nil
      rw [happ, List.getLast?_append_of_ne_nil _ hne] at hb
      have hmem : b ∈ utf8 (String.ofList [c]) := List.mem_of_getLast? hb
      by_cases hlt : c.toNat < 128
      · rw [utf8_ofList_singleton_ascii c hlt, List.mem_singleton] at hmem
        rw [hmem, byte_val]
        omega
      · have := le_val_of_mem_utf8_ofList_singleton (Nat.not_lt.1 hlt) b hmem
        omega

/-- **`trim_end_matches('.')` keeps UTF-8**: if `l` is UTF-8, so is `dropTrailingDots l`. -/
theorem isUtf8_dropTrailingDots {l : List U8} (h : IsUtf8 l) :
    IsUtf8 (dropTrailingDots l) := by
  obtain ⟨t, rfl⟩ := h
  have := exists_dropTrailingDots_utf8_ofList_eq_utf8 t.toList
  rwa [String.ofList_toList] at this

/-! ### Converses

The converses of `isUtf8_map_asciiLowercase` and `isUtf8_dropTrailingDots`, used for the failure
statements of N11 `normalize_host` and of `is_loopback_metadata_host` (the UTF-8 premise is the
weakest): the lowercase mapping changes only ASCII letters, into ASCII letters, and the trailing
bytes removed by `dropTrailingDots` are ASCII `.`. -/

/-- `asciiLowercase` maps exactly the ASCII bytes to ASCII bytes. -/
theorem val_asciiLowercase_lt_iff (b : U8) : (asciiLowercase b).val < 128 ↔ b.val < 128 := by
  unfold asciiLowercase
  split
  · rw [byte_val]; omega
  · exact Iff.rfl

/-- Bytes whose ASCII-lowercase mapping is the UTF-8 encoding of a string of characters are
UTF-8. -/
theorem isUtf8_of_map_asciiLowercase_eq_utf8_ofList : ∀ (cs : List Char) (l : List U8),
    l.map asciiLowercase = utf8 (String.ofList cs) → IsUtf8 l
  | [], l, h => by
    rw [show String.ofList [] = "" from rfl, utf8_empty, List.map_eq_nil_iff] at h
    exact ⟨"", by rw [h, utf8_empty]⟩
  | c :: cs, l, h => by
    rw [utf8_ofList_cons, List.map_eq_append_iff] at h
    obtain ⟨l1, l2, rfl, h1, h2⟩ := h
    obtain ⟨u, hu⟩ := isUtf8_of_map_asciiLowercase_eq_utf8_ofList cs l2 h2
    have hl1 : IsUtf8 l1 := by
      by_cases hc : c.toNat < 128
      · rw [utf8_ofList_singleton_ascii c hc, List.map_eq_singleton_iff] at h1
        obtain ⟨b, rfl, hb⟩ := h1
        have hb128 : b.val < 128 := by
          rw [← val_asciiLowercase_lt_iff, hb, byte_val]; omega
        refine ⟨String.ofList ([b].map (fun b => Char.ofNat b.val)), ?_⟩
        rw [utf8_ofList_ascii]
        intro x hx; rw [List.mem_singleton] at hx; rw [hx]; exact hb128
      · refine ⟨String.ofList [c], ?_⟩
        rw [← h1]
        conv => lhs; rw [← List.map_id l1]
        apply List.map_congr_left
        intro b hb
        have hge := le_val_of_mem_utf8_ofList_singleton (Nat.not_lt.1 hc) _
          (h1 ▸ List.mem_map_of_mem hb)
        have : 128 ≤ b.val := by
          by_contra hlt; exact absurd ((val_asciiLowercase_lt_iff b).2 (by omega)) (by omega)
        exact (asciiLowercase_eq_self_of_le_val this).symm
    obtain ⟨v, hv⟩ := hl1
    exact ⟨v ++ u, by rw [hv, hu, utf8_append]⟩

/-- **Converse of `isUtf8_map_asciiLowercase`**: if the bytes with ASCII uppercase letters
mapped to lowercase are UTF-8, so are the bytes. -/
theorem isUtf8_of_isUtf8_map_asciiLowercase {l : List U8} (h : IsUtf8 (l.map asciiLowercase)) :
    IsUtf8 l := by
  obtain ⟨t, ht⟩ := h
  rw [← String.ofList_toList (s := t)] at ht
  exact isUtf8_of_map_asciiLowercase_eq_utf8_ofList t.toList l ht

/-- **Converse of `isUtf8_dropTrailingDots`**: if the bytes without their trailing `.` bytes are
UTF-8, so are the bytes (the removed bytes are ASCII). -/
theorem isUtf8_of_isUtf8_dropTrailingDots {l : List U8} (h : IsUtf8 (dropTrailingDots l)) :
    IsUtf8 l := by
  obtain ⟨t, ht⟩ := h
  have hsplit : l = dropTrailingDots l ++ l.rtakeWhile (fun b => decide (b.val = 46)) := by
    have := List.rdropWhile_append_rtakeWhile (p := fun b : U8 => decide (b.val = 46)) (l := l)
    rw [dropTrailingDots]; exact this.symm
  have hdots : ∀ b ∈ l.rtakeWhile (fun b => decide (b.val = 46)), b.val < 128 := by
    intro b hb
    have := List.mem_rtakeWhile_imp hb
    rw [decide_eq_true_eq] at this
    omega
  refine ⟨t ++ String.ofList ((l.rtakeWhile (fun b => decide (b.val = 46))).map
    (fun b => Char.ofNat b.val)), ?_⟩
  rw [utf8_append, utf8_ofList_ascii _ hdots, ← ht]
  exact hsplit

end Proofs.External.MetadataResolver

/-! ## The `metadata_resolver::prim` functions -/

namespace transport.auth.metadata_resolver.prim

open ExtModel

/-- **Spec theorem for `rmcp::transport::auth::metadata_resolver::prim::trim_end_dots`**

Always succeeds with the bytes of `s` without its trailing `.` bytes. -/
@[step]
theorem trim_end_dots_spec (s : Str) :
    transport.auth.metadata_resolver.prim.trim_end_dots s ⦃ (result : Str) =>
      result.val = dropTrailingDots s.val ⦄ := by
  exact (WP.spec_ok (p := fun result : Str => result.val = dropTrailingDots s.val) _).2
    (Slice.from_val _ _)

/-- **Spec theorem for `rmcp::transport::auth::metadata_resolver::prim::ends_with`**

Always succeeds: `true` exactly when the bytes of `suffix` are a suffix of the bytes of `s`. -/
@[step]
theorem ends_with_spec (s : Str) (suffix : Str) :
    transport.auth.metadata_resolver.prim.ends_with s suffix ⦃ (result : Bool) =>
      (result = true ↔ suffix.val <:+ s.val) ⦄ := by
  simp only [transport.auth.metadata_resolver.prim.ends_with, WP.spec_ok, decide_eq_true_eq]

/-- **Spec theorem for `rmcp::transport::auth::metadata_resolver::prim::contains`**

Always succeeds: `true` exactly when the bytes of `pat` occur contiguously in the bytes of
`s`. -/
@[step]
theorem contains_spec (s : Str) (pat : Str) :
    transport.auth.metadata_resolver.prim.contains s pat ⦃ (result : Bool) =>
      (result = true ↔ pat.val <:+: s.val) ⦄ := by
  simp only [transport.auth.metadata_resolver.prim.contains, WP.spec_ok, decide_eq_true_eq]

/-- **Spec theorem for `rmcp::transport::auth::metadata_resolver::prim::system_lookup`**

Always succeeds with the operating-system resolver `systemLookup` (an opaque value). -/
@[step]
theorem system_lookup_spec :
    transport.auth.metadata_resolver.prim.system_lookup
      ⦃ (result : transport.auth.metadata_resolver.Lookup) => result = systemLookup ⦄ := by
  simp only [transport.auth.metadata_resolver.prim.system_lookup, WP.spec_ok]

/-- **Spec theorem for `rmcp::transport::auth::metadata_resolver::prim::proxy_env_values`**

Always succeeds with the one environment reading `proxyEnvValues` (an opaque constant; review
rule at `ExtModel.proxyEnvValues`: no statement constrains its value or relates two
readings). -/
@[step]
theorem proxy_env_values_spec :
    transport.auth.metadata_resolver.prim.proxy_env_values
      ⦃ (result : alloc.vec.Vec String) => result = proxyEnvValues ⦄ := by
  simp only [transport.auth.metadata_resolver.prim.proxy_env_values, WP.spec_ok]

end transport.auth.metadata_resolver.prim

/-! ## Standard library and `url` -/

open ExtModel Proofs.External.Utf8 Proofs.External.MetadataResolver

/-- **Spec theorem for `<IpAddr as PartialEq>::eq`**

Always succeeds: `true` exactly when the two addresses are equal. -/
@[step]
theorem core.net.ip_addr.IpAddr.Insts.CoreCmpPartialEqIpAddr.eq_spec
    (self : core.net.ip_addr.IpAddr) (other : core.net.ip_addr.IpAddr) :
    core.net.ip_addr.IpAddr.Insts.CoreCmpPartialEqIpAddr.eq self other
      ⦃ (result : Bool) => (result = true ↔ self = other) ⦄ := by
  rcases self with ⟨⟨a⟩⟩ | ⟨⟨a⟩⟩ <;> rcases other with ⟨⟨b⟩⟩ | ⟨⟨b⟩⟩ <;>
    simp only [core.net.ip_addr.IpAddr.Insts.CoreCmpPartialEqIpAddr.eq, WP.spec_ok,
      decide_eq_true_eq, reduceCtorEq, iff_false, Bool.false_eq_true, not_false_eq_true,
      core.net.ip_addr.IpAddr.V4.injEq, core.net.ip_addr.IpAddr.V6.injEq,
      core.net.ip_addr.Ipv4Addr.mk.injEq, core.net.ip_addr.Ipv6Addr.mk.injEq] <;>
    exact (Std.Array.eq_iff _ _).symm

/-- **Spec theorem for the constructor `IpAddr::V4` used as a function**

Always succeeds with `IpAddr::V4(a)`. -/
@[step]
theorem core.net.ip_addr.IpAddr.V4.constructor_spec (a : core.net.ip_addr.Ipv4Addr) :
    core.net.ip_addr.IpAddr.V4.constructor a
      ⦃ (result : core.net.ip_addr.IpAddr) => result = core.net.ip_addr.IpAddr.V4 a ⦄ := by
  simp only [core.net.ip_addr.IpAddr.V4.constructor, WP.spec_ok]

/-- **Spec theorem for `<fn(Ipv4Addr) -> IpAddr as FnOnce>::call_once`**

The call of `f` on `a`, with every outcome of `f a` (success, failure or divergence) unchanged:
`call_once f a = f a`. -/
theorem P.Insts.CoreOpsFunctionFnOnceTupleIpv4AddrIpAddr.call_once_spec
    (f : core.net.ip_addr.Ipv4Addr → Result core.net.ip_addr.IpAddr)
    (a : core.net.ip_addr.Ipv4Addr) :
    P.Insts.CoreOpsFunctionFnOnceTupleIpv4AddrIpAddr.call_once f a = f a :=
  rfl

/-- `call_once` of the constructor `IpAddr::V4` (the instance of `AddressClass::of`) is
`IpAddr::V4(a)`. -/
@[step]
theorem P.Insts.CoreOpsFunctionFnOnceTupleIpv4AddrIpAddr.call_once_ip_addr_v4_spec
    (a : core.net.ip_addr.Ipv4Addr) :
    P.Insts.CoreOpsFunctionFnOnceTupleIpv4AddrIpAddr.call_once
      core.net.ip_addr.IpAddr.V4.constructor a
      ⦃ (result : core.net.ip_addr.IpAddr) => result = core.net.ip_addr.IpAddr.V4 a ⦄ := by
  rw [P.Insts.CoreOpsFunctionFnOnceTupleIpv4AddrIpAddr.call_once_spec]
  exact core.net.ip_addr.IpAddr.V4.constructor_spec a

/-- **Spec theorem for `SocketAddr::ip`**

Always succeeds with the IP address of the socket address. -/
@[step]
theorem core.net.socket_addr.SocketAddr.ip_spec (self : core.net.socket_addr.SocketAddr) :
    core.net.socket_addr.SocketAddr.ip self ⦃ (result : core.net.ip_addr.IpAddr) =>
      result = match self with
        | core.net.socket_addr.SocketAddr.V4 a => core.net.ip_addr.IpAddr.V4 a.addrIp
        | core.net.socket_addr.SocketAddr.V6 a => core.net.ip_addr.IpAddr.V6 a.addrIp ⦄ := by
  cases self <;> simp only [core.net.socket_addr.SocketAddr.ip, WP.spec_ok]

/-- **Spec theorem for `Option::map_or`**

For a closure that maps `t` to `p t` without failing (the hypothesis on the `FnOnce` instance),
`p t` for `Some(t)` and `default` for `None`. -/
theorem core.option.Option.map_or_spec {T U F : Type}
    (inst : core.ops.function.FnOnce F T U) (self : Option T) (default : U) (f : F)
    (p : T → U) (hp : ∀ t, self = some t → inst.call_once f t = ok (p t)) :
    core.option.Option.map_or inst self default f ⦃ (result : U) =>
      result = self.elim default p ⦄ := by
  cases self with
  | none => simp only [core.option.Option.map_or, WP.spec_ok, Option.elim_none]
  | some t => simp only [core.option.Option.map_or, hp t rfl, WP.spec_ok, Option.elim_some]

/-- `Option::map_or` with the constructor `IpAddr::V4` (as in `AddressClass::of`):
`IpAddr::V4(t)` for `Some(t)`, `default` for `None`. -/
@[step]
theorem core.option.Option.map_or_ip_addr_v4_spec (self : Option core.net.ip_addr.Ipv4Addr)
    (default : core.net.ip_addr.IpAddr) :
    core.option.Option.map_or P.Insts.CoreOpsFunctionFnOnceTupleIpv4AddrIpAddr self default
      core.net.ip_addr.IpAddr.V4.constructor ⦃ (result : core.net.ip_addr.IpAddr) =>
        result = self.elim default core.net.ip_addr.IpAddr.V4 ⦄ :=
  core.option.Option.map_or_spec _ self default _ _ (fun _ _ => rfl)

/-- **Spec theorem for `str::to_ascii_lowercase`**

For bytes whose lowercase mapping is the UTF-8 encoding of `u` (as for every Rust `&str`, see
`to_ascii_lowercase_spec_of_eq_utf8`), succeeds with `u`. -/
@[step]
theorem alloc.str.Str.to_ascii_lowercase_spec (self : Str) (u : String)
    (hu : self.val.map asciiLowercase = utf8 u) :
    alloc.str.Str.to_ascii_lowercase self ⦃ (result : String) =>
      result = u ∧ utf8 result = self.val.map asciiLowercase ⦄ := by
  simp only [alloc.str.Str.to_ascii_lowercase, hu, strOfBytes?_utf8, WP.spec_ok, and_self]

/-- `str::to_ascii_lowercase` on the bytes of a string `t` (every Rust `&str`): the mapped bytes
are UTF-8 (`exists_map_asciiLowercase_utf8_eq_utf8`), so the result is the string they encode. -/
theorem alloc.str.Str.to_ascii_lowercase_spec_of_eq_utf8 (self : Str) (t : String)
    (ht : self.val = utf8 t) :
    alloc.str.Str.to_ascii_lowercase self ⦃ (result : String) =>
      utf8 result = self.val.map asciiLowercase ⦄ := by
  obtain ⟨u, hu⟩ := exists_map_asciiLowercase_utf8_eq_utf8 t
  rw [← ht] at hu
  simp only [alloc.str.Str.to_ascii_lowercase, hu, strOfBytes?_utf8, WP.spec_ok]

/-- `str::to_ascii_lowercase` under the UTF-8 premise `IsUtf8 self.val` (the Rust `&str`
invariant, see `ExtModel.IsUtf8` for where a statement may assume it): succeeds with the string
whose UTF-8 bytes are those of `self` with `A`–`Z` mapped to `a`–`z`. -/
theorem alloc.str.Str.to_ascii_lowercase_spec_of_isUtf8 (self : Str) (h : IsUtf8 self.val) :
    alloc.str.Str.to_ascii_lowercase self ⦃ (result : String) =>
      utf8 result = self.val.map asciiLowercase ⦄ := by
  obtain ⟨t, ht⟩ := h
  exact alloc.str.Str.to_ascii_lowercase_spec_of_eq_utf8 self t ht

/-- `str::to_ascii_lowercase` on bytes whose lowercase mapping is not UTF-8 (no Rust `&str`
has such bytes, see `to_ascii_lowercase_spec_of_eq_utf8`): the model fails with `undef`, the
other branch of the model besides `to_ascii_lowercase_spec`. -/
theorem alloc.str.Str.to_ascii_lowercase_eq_fail (self : Str)
    (h : strOfBytes? (self.val.map asciiLowercase) = none) :
    alloc.str.Str.to_ascii_lowercase self = fail .undef := by
  rw [alloc.str.Str.to_ascii_lowercase, h]

/-- **Spec theorem for `<String as PartialEq<&str>>::eq`**

Always succeeds: `true` exactly when the UTF-8 bytes of the string are the bytes of `other`. -/
@[step]
theorem alloc.string.String.Insts.CoreCmpPartialEqShared0Str.eq_spec (self : String)
    (other : Str) :
    alloc.string.String.Insts.CoreCmpPartialEqShared0Str.eq self other ⦃ (result : Bool) =>
      (result = true ↔ utf8 self = other.val) ⦄ := by
  simp only [alloc.string.String.Insts.CoreCmpPartialEqShared0Str.eq, WP.spec_ok,
    decide_eq_true_eq]

/-- **Spec theorem for `<Arc<[T]> as From<Vec<T>>>::from`**

Always succeeds with an `Arc` holding the vector's elements. -/
@[step]
theorem alloc.sync.ArcSlice.Insts.CoreConvertFromVec.from_spec {T A : Type}
    (inst : core.alloc.AllocatorClone A) (v : alloc.vec.Vec T) :
    alloc.sync.ArcSlice.Insts.CoreConvertFromVec.from inst v
      ⦃ (result : alloc.sync.Arc (Slice T)) => result.data.val = v.val ⦄ := by
  exact (WP.spec_ok (p := fun result : alloc.sync.Arc (Slice T) => result.data.val = v.val)
    _).2 (Slice.from_val _ _)

/-- **Spec theorem for `url::Url::parse`**

Always succeeds with the parse outcome `urlParse input.val` (an opaque value). -/
@[step]
theorem url.Url.parse_spec (input : Str) :
    url.Url.parse input ⦃ (result : core.result.Result url.Url url.parser.ParseError) =>
      result = urlParse input.val ⦄ := by
  simp only [url.Url.parse, WP.spec_ok]

/-- **Spec theorem for `url::Url::host_str`**

Always succeeds with the host string `urlHostStr self` (an opaque value). -/
@[step]
theorem url.Url.host_str_spec (self : url.Url) :
    url.Url.host_str self ⦃ (result : Option Str) => result = urlHostStr self ⦄ := by
  simp only [url.Url.host_str, WP.spec_ok]

/-- **Spec theorem for `url::Url::host`**

Always succeeds with the host `urlHost self` (an opaque value). -/
@[step]
theorem url.Url.host_spec (self : url.Url) :
    url.Url.host self ⦃ (result : Option (url.host.Host Str)) => result = urlHost self ⦄ := by
  simp only [url.Url.host, WP.spec_ok]

/-! ## Evaluation of the models

Kernel evaluation (`decide`) of the exact models on small inputs; each value is the one Rust
computes (checked against the Rust documentation and the sources cited at each model). -/

namespace Proofs.External.MetadataResolver

/-- `"a.b..".trim_end_matches('.')` is `"a.b"`; `"..".trim_end_matches('.')` is `""`; `"a"` is
unchanged. -/
example : dropTrailingDots [97#u8, 46#u8, 98#u8, 46#u8, 46#u8] = [97#u8, 46#u8, 98#u8] := by
  decide

example : dropTrailingDots [46#u8, 46#u8] = [] := by decide

example : dropTrailingDots [97#u8] = [97#u8] := by decide

/-- `u8::to_ascii_lowercase`: `b'A'` is `b'a'`, `b'Z'` is `b'z'`, `b'a'`, `b'@'` (64) and
`b'['` (91) are unchanged. -/
example : asciiLowercase 65#u8 = 97#u8 ∧ asciiLowercase 90#u8 = 122#u8 ∧
    asciiLowercase 97#u8 = 97#u8 ∧ asciiLowercase 64#u8 = 64#u8 ∧
    asciiLowercase 91#u8 = 91#u8 := by decide

/-- On the bytes of short strings: `"a.l".ends_with(".l")` and `"l".ends_with("")` hold;
`"l".ends_with(".l")` does not (`.` is 46, `a` 97, `l` 108). -/
example : ([46#u8, 108#u8] <:+ [97#u8, 46#u8, 108#u8]) ∧ ([] <:+ [108#u8]) ∧
    ¬ ([46#u8, 108#u8] <:+ [108#u8]) := by decide

/-- On the bytes of short strings: `"h://h".contains("://")` holds, `"h:/x".contains("://")`
does not, and `"h".contains("")` holds (`h` is 104, `:` 58, `/` 47, `x` 120). -/
example : ([58#u8, 47#u8, 47#u8] <:+: [104#u8, 58#u8, 47#u8, 47#u8, 104#u8]) ∧
    ¬ ([58#u8, 47#u8, 47#u8] <:+: [104#u8, 58#u8, 47#u8, 120#u8]) ∧
    (([] : List U8) <:+: [104#u8]) := by decide

end Proofs.External.MetadataResolver
