/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Proofs.Defs.McpHeaders
public import Proofs.External.Base64Std

@[expose] public section

/-!
# Helper lemmas for the SEP-2243 header-value encoding (G01–G04)

Equations and helper facts for the translated private functions of
`crates/rmcp/src/transport/common/mcp_headers.rs` (translation patch 07), used by the spec
theorems and laws in `Proofs.Transport.McpHeaders`:

- the sentinel markers: the bytes of `BASE64_HEADER_PREFIX` and `BASE64_HEADER_SUFFIX` are
  `Defs.McpHeaders.base64Prefix` and `base64Suffix` (9 and 2 bytes), `wrapSentinel` adds 11
  bytes, is injective and always passes G01's sentinel-shape test;
- G02: `is_tchar` as an equation (`is_tchar_eq`), and `isTchar` on code points
  (`isTchar_eq_decide`), so that the characterisations over the ASCII range are decided on
  natural numbers;
- G01: `requires_base64` as an equation (`requires_base64_eq`), and the char-level reading of
  the byte tests on UTF-8 (`utf8Char`, `isPrefix_flatMap_iff`, `any_head?_flatMap`);
- G03, G04: `encode_header_value` and `decode_header_value` as equations on the model, with
  their failures.

Source: "crates/rmcp/src/transport/common/mcp_headers.rs" (patched copy with patches 01–07,
lines 62–76, 80–98, 240–246 and 250–261; upstream `7caec76` lines 62–77, 81–100, 242–252 and
256–268)
-/

open Aeneas Aeneas.Std Result
open rmcp
open Defs (utf8Bytes)
open Defs.McpHeaders
open ExtModel Proofs.External.Utf8 Proofs.External.Byte Proofs.External.Base64Std

set_option autoImplicit false

namespace Proofs.Transport.McpHeaders

/-! ## The sentinel markers -/

theorem base64Prefix_eq :
    base64Prefix = [61#u8, 63#u8, 98#u8, 97#u8, 115#u8, 101#u8, 54#u8, 52#u8, 63#u8] := by
  decide +kernel

theorem base64Suffix_eq : base64Suffix = [63#u8, 61#u8] := by decide +kernel

theorem length_base64Prefix : base64Prefix.length = 9 := by rw [base64Prefix_eq]; rfl

theorem length_base64Suffix : base64Suffix.length = 2 := by rw [base64Suffix_eq]; rfl

theorem val_BASE64_HEADER_PREFIX :
    transport.common.http_header.BASE64_HEADER_PREFIX.val = base64Prefix := by
  unfold transport.common.http_header.BASE64_HEADER_PREFIX
  rw [toStr_val]; rfl

theorem val_BASE64_HEADER_SUFFIX :
    transport.common.http_header.BASE64_HEADER_SUFFIX.val = base64Suffix := by
  unfold transport.common.http_header.BASE64_HEADER_SUFFIX
  rw [toStr_val]; rfl

theorem length_wrapSentinel (inner : List U8) :
    (wrapSentinel inner).length = inner.length + 11 := by
  simp only [wrapSentinel, List.length_append, length_base64Prefix, length_base64Suffix]
  omega

theorem wrapSentinel_injective {a b : List U8} (h : wrapSentinel a = wrapSentinel b) : a = b := by
  unfold wrapSentinel at h
  exact List.append_cancel_left (List.append_cancel_right h)

theorem requiresBase64_wrapSentinel (inner : List U8) :
    requiresBase64 (wrapSentinel inner) = true := by
  unfold requiresBase64
  have h1 : base64Prefix <+: wrapSentinel inner := by
    unfold wrapSentinel; rw [List.append_assoc]; exact List.prefix_append _ _
  have h2 : base64Suffix <:+ wrapSentinel inner := List.suffix_append _ _
  simp [h1, h2]

theorem isSome_strOfBytes?_iff (y : List U8) :
    (strOfBytes? y).isSome ↔ ExtModel.IsUtf8 y := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 h
    exact ⟨t, (strOfBytes?_eq_some_iff y t).1 ht⟩
  · rintro ⟨t, rfl⟩; rw [strOfBytes?_utf8]; rfl

theorem isPrintableAscii_of_requiresBase64_eq_false {s : List U8}
    (h : requiresBase64 s = false) : ∀ b ∈ s, isPrintableAscii b = true := by
  unfold requiresBase64 at h
  simp only [Bool.or_eq_false_iff, List.any_eq_false] at h
  exact fun b hb => by simpa using h.1.2 b hb

theorem not_isPrintableAscii_eq (b : U8) :
    (!isPrintableAscii b) = isControlOrNonAsciiByte b := by
  unfold isPrintableAscii isControlOrNonAsciiByte
  by_cases h : 0x20 ≤ b.val ∧ b.val ≤ 0x7E
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

/-! ## G02 `is_tchar` -/

theorem isDigit_or_isAlpha_eq (c : Char) : (c.isDigit || c.isAlpha) =
    decide ((48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨
      (97 ≤ c.toNat ∧ c.toNat ≤ 122)) := by
  simp only [Char.isDigit, Char.isAlpha, Char.isUpper, Char.isLower]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  simp only [Char.toNat, UInt32.le_iff_toNat_le]
  constructor <;> intro h <;> simp at h ⊢ <;> omega

theorem is_tchar_eq (c : Char) :
    transport.common.mcp_headers.is_tchar c = ok (isTchar c) := by
  unfold transport.common.mcp_headers.is_tchar
  simp only [core.char.methods.Char.is_ascii_alphanumeric, Char.Insts.CoreConvertFromU8.from,
    bind_ok]
  have hq : Char.ofNat (39#u8).val = '\'' := rfl
  rw [hq]
  unfold isTchar
  rw [isDigit_or_isAlpha_eq]
  by_cases h : (48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨
      (97 ≤ c.toNat ∧ c.toNat ≤ 122)
  · simp [h]
  · have hl : "!#$%&'*+-.^_`|~".toList = ['!', '#', '$', '%', '&', '\'', '*', '+', '-', '.', '^',
        '_', '`', '|', '~'] := by decide +kernel
    rw [decide_eq_false h, hl, ite_eq_right Bool.false_ne_true, Bool.false_or]
    by_cases hm : c ∈ ['!', '#', '$', '%', '&', '\'', '*', '+', '-', '.', '^', '_', '`', '|', '~']
    · rw [decide_eq_true hm]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    · rw [decide_eq_false hm]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hm
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_right h5,
        ite_eq_right h6, ite_eq_right h7, ite_eq_right h8, ite_eq_right h9, ite_eq_right h10,
        ite_eq_right h11, ite_eq_right h12, ite_eq_right h13, ite_eq_right h14,
        decide_eq_false h15]

theorem mem_iff_toNat_mem (c : Char) (l : List Char) : c ∈ l ↔ c.toNat ∈ l.map Char.toNat := by
  rw [List.mem_map]
  constructor
  · intro h; exact ⟨c, h, rfl⟩
  · rintro ⟨d, hd, he⟩
    have : d = c := Char.ext (UInt32.toNat_inj.1 he)
    exact this ▸ hd

/-- The code points of the fifteen punctuation characters of `tchar`. -/
def punctCodes : List Nat := [33, 35, 36, 37, 38, 39, 42, 43, 45, 46, 94, 95, 96, 124, 126]

/-- The code points of the 17 RFC 9110 delimiters, in the order of `isDelimiter`. -/
def delimiterCodes : List Nat :=
  [34, 40, 41, 44, 47, 58, 59, 60, 61, 62, 63, 91, 92, 93, 123, 125, 64]

theorem map_toNat_punct : "!#$%&'*+-.^_`|~".toList.map Char.toNat = punctCodes := by
  decide +kernel

theorem map_toNat_delimiters :
    "\"(),/:;<=>?[\\]{}@".toList.map Char.toNat = delimiterCodes := by
  decide +kernel

theorem map_toNat_tchars : tchars.map Char.toNat =
    punctCodes ++ List.range' 48 10 ++ List.range' 65 26 ++ List.range' 97 26 := by
  decide +kernel

theorem isTchar_eq_decide (c : Char) : isTchar c = decide ((48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨
    (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨ (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ c.toNat ∈ punctCodes) := by
  unfold isTchar
  rw [isDigit_or_isAlpha_eq, Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, mem_iff_toNat_mem c, map_toNat_punct]
  tauto

theorem tcharCode_iff_mem : ∀ n < 128, ((48 ≤ n ∧ n ≤ 57) ∨ (65 ≤ n ∧ n ≤ 90) ∨
    (97 ≤ n ∧ n ≤ 122) ∨ n ∈ punctCodes) ↔
      n ∈ punctCodes ++ List.range' 48 10 ++ List.range' 65 26 ++ List.range' 97 26 := by
  decide +kernel

theorem tcharCode_iff_vchar : ∀ n < 128, ((48 ≤ n ∧ n ≤ 57) ∨ (65 ≤ n ∧ n ≤ 90) ∨
    (97 ≤ n ∧ n ≤ 122) ∨ n ∈ punctCodes) ↔ ((0x21 ≤ n ∧ n ≤ 0x7E) ∧ n ∉ delimiterCodes) := by
  decide +kernel

/-! ## G01 on UTF-8: chars against bytes -/

/-- The UTF-8 bytes of one char, as `ExtModel.utf8` writes them. -/
def utf8Char (c : Char) : List U8 := (String.utf8EncodeChar c).map (fun x => byte x.toNat)

theorem utf8_eq_flatMap (v : String) : utf8 v = v.toList.flatMap utf8Char := by
  conv => lhs; rw [← String.ofList_toList (s := v)]
  rw [utf8_ofList]; rfl

theorem utf8Char_of_lt (c : Char) (h : c.toNat < 128) : utf8Char c = [byte c.toNat] := by
  have := utf8_ofList_singleton_ascii c h
  rw [utf8_ofList, List.flatMap_cons, List.flatMap_nil, List.append_nil] at this
  exact this

theorem utf8Char_of_le (c : Char) (h : 128 ≤ c.toNat) :
    utf8Char c ≠ [] ∧ ∀ b ∈ utf8Char c, 128 ≤ b.val := by
  have hge := le_val_of_mem_utf8_ofList_singleton h
  rw [utf8_ofList, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hge
  refine ⟨?_, hge⟩
  intro h0
  have := congrArg List.length h0
  simp only [utf8Char, List.length_map, String.length_utf8EncodeChar, List.length_nil] at this
  exact absurd this (Nat.ne_of_gt (Char.utf8Size_pos c))

theorem reverse_utf8Char_of_lt (c : Char) (h : c.toNat < 128) :
    (utf8Char c).reverse = [byte c.toNat] := by
  rw [utf8Char_of_lt c h]; rfl

theorem reverse_utf8Char_of_le (c : Char) (h : 128 ≤ c.toNat) :
    (utf8Char c).reverse ≠ [] ∧ ∀ b ∈ (utf8Char c).reverse, 128 ≤ b.val := by
  obtain ⟨h1, h2⟩ := utf8Char_of_le c h
  exact ⟨by simpa using h1, fun b hb => h2 b (List.mem_reverse.1 hb)⟩

theorem reverse_flatMap_utf8Char (v : List Char) :
    (v.flatMap utf8Char).reverse = v.reverse.flatMap (fun c => (utf8Char c).reverse) := by
  induction v with
  | nil => rfl
  | cons c cs ih => simp [List.flatMap_cons, List.reverse_append, ih, List.flatMap_append]

/-- A code that writes an ASCII char as its byte and any other char as a nonempty list of
bytes of at least `0x80` preserves and reflects prefixes of ASCII strings. -/
theorem isPrefix_flatMap_iff (f : Char → List U8)
    (hA : ∀ c, c.toNat < 128 → f c = [byte c.toNat])
    (hN : ∀ c, 128 ≤ c.toNat → f c ≠ [] ∧ ∀ b ∈ f c, 128 ≤ b.val) :
    ∀ (p v : List Char), (∀ c ∈ p, c.toNat < 128) →
      (p.flatMap f <+: v.flatMap f ↔ p <+: v) := by
  intro p
  induction p with
  | nil => intro v _; simp
  | cons c cs ih =>
    intro v hp
    have hc := hp c List.mem_cons_self
    have hcs : ∀ d ∈ cs, d.toNat < 128 := fun d hd => hp d (List.mem_cons_of_mem c hd)
    constructor
    · intro h
      cases v with
      | nil =>
        simp only [List.flatMap_cons, List.flatMap_nil, hA c hc] at h
        have := h.length_le; simp at this
      | cons d ds =>
        simp only [List.flatMap_cons, hA c hc] at h
        by_cases hd : d.toNat < 128
        · rw [hA d hd] at h
          simp only [List.singleton_append, List.cons_prefix_cons] at h
          have hcd : c = d := by
            have := congrArg UScalar.val h.1
            rw [byte_val, byte_val, Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)] at this
            exact Char.toNat_inj.1 this
          subst hcd
          exact List.cons_prefix_cons.2 ⟨rfl, (ih ds hcs).1 h.2⟩
        · obtain ⟨hne, hge⟩ := hN d (by omega)
          obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil hne
          rw [hb] at h
          simp only [List.cons_append, List.cons_prefix_cons] at h
          have := hge b (hb ▸ List.mem_cons_self)
          rw [← h.1, byte_val, Nat.mod_eq_of_lt (by omega)] at this
          omega
    · rintro ⟨t, rfl⟩
      exact ⟨t.flatMap f, by simp⟩

theorem any_head?_flatMap (f : Char → List U8)
    (hA : ∀ c, c.toNat < 128 → f c = [byte c.toNat])
    (hN : ∀ c, 128 ≤ c.toNat → f c ≠ [] ∧ ∀ b ∈ f c, 128 ≤ b.val) (v : List Char) :
    (v.flatMap f).head?.any isSpaceOrTab =
      v.head?.any (fun c => decide (c = ' ' ∨ c = '\t')) := by
  cases v with
  | nil => simp
  | cons c cs =>
    simp only [List.flatMap_cons, List.head?_cons, Option.any_some]
    by_cases hc : c.toNat < 128
    · rw [hA c hc]
      simp only [List.singleton_append, List.head?_cons, Option.any_some, isSpaceOrTab, byte_val,
        Nat.mod_eq_of_lt (by omega : c.toNat < 256)]
      apply decide_eq_decide.2
      constructor
      · rintro (h | h)
        · left; exact Char.toNat_inj.1 (by rw [h]; rfl)
        · right; exact Char.toNat_inj.1 (by rw [h]; rfl)
      · rintro (rfl | rfl)
        · left; rfl
        · right; rfl
    · obtain ⟨hne, hge⟩ := hN c (by omega)
      obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil hne
      have := hge b (hb ▸ List.mem_cons_self)
      rw [hb]
      simp only [List.cons_append, List.head?_cons, Option.any_some, isSpaceOrTab]
      rw [decide_eq_false (by omega), decide_eq_false]
      rintro (rfl | rfl) <;> simp at hc

/-! ## G01 `requires_base64` -/

/-- `bind_tc_ok` for a `Str` read as a `Slice U8` (`str::as_bytes`): the generic lemma does not
fire on `ok (α := Slice U8) x` with `x : Str`. -/
theorem bind_ok_slice {β : Type} (x : Str) (f : Slice U8 → Result β) :
    (do let y ← ok (α := Slice U8) x; f y) = f x := bind_tc_ok x f

theorem requires_base64_eq (value : Str) :
    transport.common.mcp_headers.requires_base64 value = ok (requiresBase64 value.val) := by
  unfold transport.common.mcp_headers.requires_base64
  simp only [core.str.Str.is_empty, core.str.Str.as_bytes, core.slice.Slice.first,
    core.slice.Slice.last, core.option.OptionShared0T.copied, bind_ok,
    transport.common.mcp_headers.prim.has_control_or_non_ascii,
    transport.common.mcp_headers.prim.starts_with, transport.common.mcp_headers.prim.ends_with,
    val_BASE64_HEADER_PREFIX, val_BASE64_HEADER_SUFFIX]
  simp only [bind_ok_slice]
  generalize value.val = l
  cases l with
  | nil => simp [requiresBase64]; intro _; decide +kernel
  | cons x xs =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
    rw [Aeneas.Std.bind_ok]
    have hmid : (x :: xs).any (fun b => !isPrintableAscii b) =
        (x :: xs).any isControlOrNonAsciiByte := by
      congr 1; funext b; exact not_isPrintableAscii_eq b
    unfold requiresBase64
    rw [hmid]
    obtain ⟨y, hy⟩ : ∃ y, (x :: xs).getLast? = some y :=
      ⟨_, List.getLast?_eq_some_getLast (by simp)⟩
    rw [hy]
    have nst : ∀ z : U8, ¬ z = 32#u8 → ¬ z = 9#u8 → isSpaceOrTab z = false := by
      intro z h1 h2
      simp only [isSpaceOrTab, decide_eq_false_iff_not]
      rintro (h | h)
      · exact h1 (UScalar.eq_of_val_eq (by rw [h]; rfl))
      · exact h2 (UScalar.eq_of_val_eq (by rw [h]; rfl))
    simp only [List.head?_cons, Option.any_some]
    split
    · simp only [Aeneas.Std.bind_ok, ite_true]; congr 1
    · simp only [Aeneas.Std.bind_ok, ite_true]; congr 1
    · rename_i h1 h2
      simp only [Aeneas.Std.bind_ok, Bool.false_eq_true, ite_false, nst x h1 h2,
        Bool.false_or]
      split
      · simp only [Aeneas.Std.bind_ok, ite_true]; congr 1
      · simp only [Aeneas.Std.bind_ok, ite_true]; congr 1
      · rename_i h3 h4
        simp only [Aeneas.Std.bind_ok, Bool.false_eq_true, ite_false, nst y h3 h4,
          Bool.false_or]
        cases (x :: xs).any isControlOrNonAsciiByte
        · by_cases hp : base64Prefix <+: x :: xs <;> simp [hp]
        · rfl

/-! ## G03 `encode_header_value` -/

theorem to_owned_eq (v : Str) :
    Str.Insts.AllocBorrowToOwnedString.to_owned v =
      match strOfBytes? v.val with | some s => ok s | none => fail Error.undef := rfl

theorem encode_header_value_eq_of_requiresBase64_eq_true (value : Str)
    (h_req : requiresBase64 value.val = true) :
    transport.common.mcp_headers.encode_header_value value =
      Aeneas.Std.bind (transport.common.mcp_headers.prim.base64_encode value) (fun s =>
        Aeneas.Std.bind (alloc.string.String.Insts.CoreOpsDerefDerefStr.deref s)
          transport.common.mcp_headers.prim.wrap_sentinel) := by
  unfold transport.common.mcp_headers.encode_header_value
  rw [requires_base64_eq, bind_ok, h_req]
  rfl

/-! ## G04 `decode_header_value` -/

theorem decode_header_value_eq (value : Str) :
    transport.common.mcp_headers.decode_header_value value =
      match sentinelInner? value.val with
      | none =>
        Aeneas.Std.bind (Str.Insts.AllocBorrowToOwnedString.to_owned value)
          (fun s => ok (some s))
      | some inner =>
        if ExtModel.maxStringBytes < ExtModel.b64StdDecodedLenEstimate inner.length then
          fail Error.panic
        else ok ((ExtModel.b64StdPadDecode inner).bind strOfBytes?) := by
  unfold transport.common.mcp_headers.decode_header_value
  simp only [transport.common.mcp_headers.prim.strip_prefix, val_BASE64_HEADER_PREFIX]
  unfold sentinelInner?
  by_cases hp : base64Prefix <+: value.val
  · rw [ite_eq_left hp, bind_ok]
    simp only [transport.common.mcp_headers.prim.strip_suffix, val_BASE64_HEADER_SUFFIX,
      Slice.from_val]
    by_cases hq : base64Suffix <:+ value.val.drop base64Prefix.length
    · rw [ite_eq_left hq, ite_eq_left ⟨hp, hq⟩, bind_ok]
      simp only [transport.common.mcp_headers.prim.base64_decode, Slice.from_val]
      split_ifs with hl
      · rw [bind_fail]
      · split
        · rename_i heq
          rw [Slice.from_val] at heq
          simp only [bind_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual, heq,
            Option.bind_none]
        · rename_i l heq
          rw [Slice.from_val] at heq
          simp only [bind_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
            alloc.string.String.from_utf8, alloc.vec.Vec.from_val, heq, Option.bind_some]
          cases strOfBytes? l <;> simp [core.result.Result.ok]
    · rw [ite_eq_right hq, ite_eq_right (fun h => hq h.2), bind_ok]
  · rw [ite_eq_right hp, ite_eq_right (fun h => hp h.1), bind_ok]

theorem map_utf8Bytes_bind_strOfBytes? (o : Option (List U8)) :
    (o.bind strOfBytes?).map utf8Bytes = o.filter (fun y => (strOfBytes? y).isSome) := by
  rcases o with _ | y
  · rfl
  · simp only [Option.bind_some, Option.filter_some]
    cases h : strOfBytes? y with
    | none => simp
    | some t =>
      simp only [Option.map_some, Option.isSome_some, ite_true]
      rw [(strOfBytes?_eq_some_iff y t).1 h]; rfl

end Proofs.Transport.McpHeaders
