/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Proofs.External.String
public import Proofs.External.WP
public import Proofs.External.Skill
public import Proofs.Defs.AuthMetadata

@[expose] public section

/-!
# Specs of the externals of the `auth.rs` OAuth metadata checks (A04–A10, patch 06)

Spec theorems for the models of `formal/trusted/Rmcp/FunsExternal.lean`, section "`auth.rs` OAuth
metadata URL and issuer checks": the ten `auth::prim` functions that translation patch 06 adds
(`crates/rmcp/src/transport/auth.rs` in the patched copy), `Option::zip`,
`str::eq_ignore_ascii_case` and the seven `url::Url` functions that the targets A04–A10 reach.
Each external has a theorem named after it with `_spec`. The opaque values (`ExtModel.urlScheme`,
`urlPath`, `urlFragment`, `urlPort`, `urlSerialization`, `urlJoin`, `issuerUrl`; human decision
AD4 2026-11-26) appear in the postconditions unopened; their laws are hypotheses of the statements
that need them.
Stated exceptions (the same three in the header of patch 06, the section docstring of
FunsExternal.lean and the module docstring of Proofs.External.Auth): (1) AD7: the `issuer_url`
setters can panic for a discovery URL longer than `u32::MAX` bytes; the model returns `ok`. (2) AD8:
the `debug_assert!` of `Url::join` (url-2.5.9 `src/parser.rs` line 1304) can panic for a `file:`
base whose last path segment is a normalized Windows drive letter; the model returns `ok`. (3)
The `tracing` side effect of the four log functions is not modelled; they return `()`.

Section "Whitespace" proves that the byte strings of `ExtModel.whitespaceUtf8` are the UTF-8
encodings of the code points `ExtModel.whitespaceCodePoints` (`whitespaceUtf8_eq`), so the
`prim::trim` model strips exactly the encodings of the Unicode `White_Space` chars, and that on
the UTF-8 bytes of a string it is the char-level trim `Defs.AuthMetadata.trimUnicodeWhitespace`
(`trimWhitespace_utf8Bytes`, signed off 2026-11-27 with A04–A10 and restated as
`Theorems.External.trimWhitespace_utf8Bytes` in `Proofs.Internal.External`). Section
"Evaluation of the models" checks the exact models on small inputs by kernel evaluation
(`decide`).
-/

open Aeneas Aeneas.Std Result
open rmcp

namespace Proofs.External.Auth

open ExtModel Proofs.External.Utf8

/-! ### Whitespace -/

/-- The byte strings that the `prim::trim` model strips are the UTF-8 encodings of the Unicode
`White_Space` code points, in the same order. -/
theorem whitespaceUtf8_eq :
    whitespaceUtf8 = whitespaceCodePoints.map (fun n => utf8 (String.ofList [Char.ofNat n])) := by
  simp only [utf8_ofList, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  decide

/-! ### `str::trim` on UTF-8 bytes

The law `trimWhitespace_utf8Bytes`: on the UTF-8 bytes of a string, the byte model
`ExtModel.trimWhitespace` of `prim::trim` is the char-level trim
`Defs.AuthMetadata.trimUnicodeWhitespace`. The proof writes the bytes as the concatenation of the
encodings of the chars (`charUtf8`) and uses that UTF-8 is prefix-free and suffix-free at char
boundaries, so a whitespace encoding matches at either end exactly when the end char is
whitespace. -/

section Trim

open Defs (utf8Bytes)
open Defs.AuthMetadata Proofs.External.Skill Proofs.External.Byte

/-- The UTF-8 bytes of one char. -/
abbrev charUtf8 (c : Char) : List U8 := utf8 (String.ofList [c])

theorem utf8_ofList_eq_flatMap (cs : List Char) :
    utf8 (String.ofList cs) = cs.flatMap charUtf8 := by
  rw [utf8_ofList]
  congr 1
  funext c
  exact (utf8_ofList_singleton c).symm

theorem charUtf8_eq (c : Char) :
    charUtf8 c = (String.utf8EncodeChar c).map (fun x => byte x.toNat) :=
  utf8_ofList_singleton c

theorem charUtf8_ne_nil (c : Char) : charUtf8 c ≠ [] := by
  rw [charUtf8_eq, ne_eq, List.map_eq_nil_iff]
  exact String.utf8EncodeChar_ne_nil

theorem map_toUInt8_charUtf8 (c : Char) :
    (charUtf8 c).map (fun b : U8 => b.val.toUInt8) = String.utf8EncodeChar c := by
  rw [charUtf8_eq, List.map_map]
  conv => rhs; rw [← List.map_id (String.utf8EncodeChar c)]
  apply List.map_congr_left
  intro x _
  exact toUInt8_byte x

/-- UTF-8 is prefix-free at a char boundary. -/
theorem eq_of_charUtf8_prefix {d c : Char} {R : List U8} (h : charUtf8 d <+: charUtf8 c ++ R) :
    d = c := by
  obtain ⟨T, hT⟩ := h
  have h1 := congrArg (List.map (fun b : U8 => b.val.toUInt8)) hT
  rw [List.map_append, List.map_append, map_toUInt8_charUtf8, map_toUInt8_charUtf8] at h1
  have h2 := congrArg (fun l : List UInt8 => l.toByteArray.utf8DecodeChar? 0) h1
  simp only [List.toByteArray_append, ByteArray.utf8DecodeChar?_utf8EncodeChar_append,
    Option.some.injEq] at h2
  exact h2

theorem charUtf8_injective : Function.Injective charUtf8 :=
  fun _ _ h => eq_of_charUtf8_prefix (R := []) (by rw [h, List.append_nil])

theorem val_byte_toNat (x : UInt8) : (byte x.toNat).val = x.toNat := by
  rw [byte_val, Nat.mod_eq_of_lt (UInt8.toNat_lt x)]

/-- The first byte of a char encoding is a lead byte (`< 0x80` or `≥ 0xC0`). -/
theorem lt_or_le_of_mem_head?_charUtf8 (c : Char) :
    ∀ x ∈ (charUtf8 c).head?, x.val < 128 ∨ 192 ≤ x.val := by
  intro x hx
  rw [charUtf8_eq, List.head?_map] at hx
  simp only [Option.mem_def, Option.map_eq_some_iff] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [val_byte_toNat]
  exact toNat_lt_or_le_of_mem_head?_utf8EncodeChar c y hy

/-- The other bytes of a char encoding are continuation bytes (`0x80`–`0xBF`). -/
theorem le_and_lt_of_mem_tail_charUtf8 (c : Char) :
    ∀ x ∈ (charUtf8 c).tail, 128 ≤ x.val ∧ x.val < 192 := by
  intro x hx
  rw [charUtf8_eq] at hx
  have ht := le_toNat_and_toNat_lt_of_mem_tail_utf8EncodeChar c
  cases hc : String.utf8EncodeChar c with
  | nil => rw [hc] at hx; simp only [List.map_nil, List.tail_nil, List.not_mem_nil] at hx
  | cons y ys =>
    rw [hc] at hx ht
    simp only [List.map_cons, List.tail_cons, List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [val_byte_toNat]
    exact ht z (by simpa only [List.tail_cons] using hz)

/-- A char encoding inside another, not at its start, is impossible. -/
theorem false_of_cons_append_charUtf8_eq (d c : Char) (t : U8) (T : List U8)
    (h : t :: T ++ charUtf8 d = charUtf8 c) : False := by
  obtain ⟨x, a', ha⟩ : ∃ x a', charUtf8 d = x :: a' := by
    cases hE : charUtf8 d with
    | nil => exact absurd hE (charUtf8_ne_nil d)
    | cons x a' => exact ⟨x, a', rfl⟩
  have hl := lt_or_le_of_mem_head?_charUtf8 d x (by rw [ha]; rfl)
  have hc := le_and_lt_of_mem_tail_charUtf8 c x (by
    rw [← h, ha]
    simp only [List.cons_append, List.tail_cons, List.mem_append, List.mem_cons, true_or,
      or_true])
  omega

/-- UTF-8 is suffix-free at a char boundary (lead bytes against continuation bytes). -/
theorem eq_of_charUtf8_suffix {d c : Char} {P : List U8} (h : charUtf8 d <:+ P ++ charUtf8 c) :
    d = c := by
  have hb : charUtf8 c <:+ P ++ charUtf8 c := List.suffix_append _ _
  by_cases hl : (charUtf8 d).length ≤ (charUtf8 c).length
  · obtain ⟨T, hT⟩ := List.suffix_of_suffix_length_le h hb hl
    cases T with
    | nil => exact charUtf8_injective (by simpa only [List.nil_append] using hT)
    | cons t T' => exact (false_of_cons_append_charUtf8_eq d c t T' hT).elim
  · obtain ⟨T, hT⟩ := List.suffix_of_suffix_length_le hb h (by omega)
    cases T with
    | nil => simp only [List.nil_append] at hT; rw [hT] at hl; exact (hl le_rfl).elim
    | cons t T' => exact (false_of_cons_append_charUtf8_eq c d t T' hT).elim

theorem isUnicodeWhitespace_iff (c : Char) :
    isUnicodeWhitespace c = true ↔ c.toNat ∈ whitespaceCodePoints := by
  simp only [isUnicodeWhitespace, List.mem_cons, List.not_mem_nil, or_false, Bool.decide_or,
    Bool.or_eq_true, decide_eq_true_eq, whitespaceCodePoints]

theorem toNat_ofNat_of_mem_whitespaceCodePoints :
    ∀ n ∈ whitespaceCodePoints, (Char.ofNat n).toNat = n := by
  decide

theorem whitespaceUtf8_eq_map_charUtf8 :
    whitespaceUtf8 = whitespaceCodePoints.map (fun n => charUtf8 (Char.ofNat n)) :=
  whitespaceUtf8_eq

/-- The length of the whitespace encoding equal to the encoding of `c`, if `c` is whitespace. -/
theorem map_find?_whitespaceCodePoints (c : Char) :
    (whitespaceCodePoints.find? (fun n => decide (Char.ofNat n = c))).map
        (fun n => (charUtf8 (Char.ofNat n)).length) =
      if isUnicodeWhitespace c then some (charUtf8 c).length else none := by
  cases hf : whitespaceCodePoints.find? (fun n => decide (Char.ofNat n = c)) with
  | none =>
    have hw : isUnicodeWhitespace c = false := by
      cases hw : isUnicodeWhitespace c
      · rfl
      · rw [isUnicodeWhitespace_iff] at hw
        have := List.find?_eq_none.mp hf _ hw
        simp only [Char.ofNat_toNat, decide_true, not_true_eq_false] at this
    simp only [Option.map_none, hw, Bool.false_eq_true, ↓reduceIte]
  | some n =>
    have hn : Char.ofNat n = c := by simpa only [decide_eq_true_eq] using List.find?_some hf
    have hmem := List.mem_of_find?_eq_some hf
    have hw : isUnicodeWhitespace c = true := by
      rw [isUnicodeWhitespace_iff, ← hn, toNat_ofNat_of_mem_whitespaceCodePoints n hmem]
      exact hmem
    simp only [Option.map_some, hn, hw, ↓reduceIte]

/-- At the front: the whitespace encoding matched is the encoding of the first char, if it is
whitespace. -/
theorem matchedPrefixLength_whitespaceUtf8_charUtf8_append (c : Char) (R : List U8) :
    matchedPrefixLength whitespaceUtf8 (charUtf8 c ++ R) =
      if isUnicodeWhitespace c then (charUtf8 c).length else 0 := by
  have hp : ((fun w : List U8 => w.isPrefixOf (charUtf8 c ++ R)) ∘
      (fun n => charUtf8 (Char.ofNat n))) = fun n => decide (Char.ofNat n = c) := by
    funext n
    simp only [Function.comp]
    rw [Bool.eq_iff_iff, List.isPrefixOf_iff_prefix, decide_eq_true_iff]
    constructor
    · exact eq_of_charUtf8_prefix
    · rintro rfl; exact List.prefix_append _ _
  have hf := map_find?_whitespaceCodePoints c
  unfold matchedPrefixLength
  rw [whitespaceUtf8_eq_map_charUtf8, List.find?_map, hp]
  revert hf
  cases (whitespaceCodePoints.find? (fun n => decide (Char.ofNat n = c))) <;>
    cases isUnicodeWhitespace c <;> intro hf <;>
    simp_all only [Option.map_none, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, Option.map_some,
      Option.some.injEq]

/-- At the back (on the reversed bytes): the whitespace encoding matched is the encoding of the
last char, if it is whitespace. -/
theorem matchedPrefixLength_map_reverse_charUtf8_append (c : Char) (P : List U8) :
    matchedPrefixLength (whitespaceUtf8.map List.reverse) ((charUtf8 c).reverse ++ P.reverse) =
      if isUnicodeWhitespace c then (charUtf8 c).length else 0 := by
  have hp : ((fun w : List U8 => w.isPrefixOf ((charUtf8 c).reverse ++ P.reverse)) ∘
      (fun n => (charUtf8 (Char.ofNat n)).reverse)) = fun n => decide (Char.ofNat n = c) := by
    funext n
    simp only [Function.comp]
    rw [Bool.eq_iff_iff, List.isPrefixOf_iff_prefix, decide_eq_true_iff, ← List.reverse_append,
      List.reverse_prefix]
    constructor
    · exact eq_of_charUtf8_suffix
    · rintro rfl; exact List.suffix_append _ _
  have hf := map_find?_whitespaceCodePoints c
  unfold matchedPrefixLength
  rw [whitespaceUtf8_eq_map_charUtf8, List.map_map, List.find?_map]
  have hc : (List.reverse ∘ fun n => charUtf8 (Char.ofNat n)) =
      fun n => (charUtf8 (Char.ofNat n)).reverse := rfl
  rw [hc, hp]
  revert hf
  cases (whitespaceCodePoints.find? (fun n => decide (Char.ofNat n = c))) <;>
    cases isUnicodeWhitespace c <;> intro hf <;>
    simp_all only [Option.map_none, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, Option.map_some,
      Option.some.injEq, List.length_reverse]

theorem matchedPrefixLength_whitespaceUtf8_nil : matchedPrefixLength whitespaceUtf8 [] = 0 := by
  decide

theorem matchedPrefixLength_map_reverse_nil :
    matchedPrefixLength (whitespaceUtf8.map List.reverse) [] = 0 := by
  decide

/-- Dropping whitespace encodings at the front drops the leading whitespace chars. -/
theorem dropEncodedPrefixes_whitespaceUtf8_flatMap :
    ∀ (cs : List Char) (n : Nat), (cs.flatMap charUtf8).length ≤ n →
      dropEncodedPrefixes whitespaceUtf8 n (cs.flatMap charUtf8) =
        (cs.dropWhile isUnicodeWhitespace).flatMap charUtf8
  | [], n, _ => by
    cases n with
    | zero => rfl
    | succ m =>
      simp only [List.flatMap_nil, List.dropWhile_nil]
      rw [dropEncodedPrefixes, matchedPrefixLength_whitespaceUtf8_nil]
  | c :: rest, n, hn => by
    rw [List.flatMap_cons] at hn ⊢
    have hpos : 0 < (charUtf8 c).length := List.length_pos_iff.mpr (charUtf8_ne_nil c)
    rw [List.length_append] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [dropEncodedPrefixes, matchedPrefixLength_whitespaceUtf8_charUtf8_append]
    by_cases hw : isUnicodeWhitespace c = true
    · obtain ⟨k, hk⟩ : ∃ k, (charUtf8 c).length = k + 1 :=
        ⟨(charUtf8 c).length - 1, by omega⟩
      simp only [hw, ↓reduceIte, hk]
      rw [← hk, List.drop_left, List.dropWhile_cons_of_pos hw]
      exact dropEncodedPrefixes_whitespaceUtf8_flatMap rest m (by omega)
    · have hw' : isUnicodeWhitespace c = false := by simpa only [Bool.not_eq_true] using hw
      simp only [hw', Bool.false_eq_true, ↓reduceIte]
      rw [List.dropWhile_cons_of_neg hw, List.flatMap_cons]

/-- Dropping reversed whitespace encodings from the reversed bytes drops the trailing whitespace
chars. -/
theorem dropEncodedPrefixes_map_reverse_flatMap :
    ∀ (ds : List Char) (n : Nat), (ds.flatMap charUtf8).length ≤ n →
      (dropEncodedPrefixes (whitespaceUtf8.map List.reverse) n
          (ds.flatMap charUtf8).reverse).reverse =
        (ds.rdropWhile isUnicodeWhitespace).flatMap charUtf8 := by
  intro ds
  induction ds using List.reverseRecOn with
  | nil =>
    intro n _
    cases n with
    | zero => rfl
    | succ m =>
      simp only [List.flatMap_nil, List.reverse_nil, List.rdropWhile_nil]
      rw [dropEncodedPrefixes, matchedPrefixLength_map_reverse_nil]; rfl
  | append_singleton A c ih =>
    intro n hn
    rw [List.flatMap_append, List.flatMap_singleton] at hn ⊢
    rw [List.reverse_append]
    have hpos : 0 < (charUtf8 c).length := List.length_pos_iff.mpr (charUtf8_ne_nil c)
    rw [List.length_append] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [dropEncodedPrefixes, matchedPrefixLength_map_reverse_charUtf8_append]
    by_cases hw : isUnicodeWhitespace c = true
    · obtain ⟨k, hk⟩ : ∃ k, (charUtf8 c).length = k + 1 :=
        ⟨(charUtf8 c).length - 1, by omega⟩
      simp only [hw, ↓reduceIte, hk]
      have hr : (charUtf8 c).length = (charUtf8 c).reverse.length := by
        simp only [List.length_reverse]
      rw [← hk, hr, List.drop_left,
        List.rdropWhile_concat_pos (p := isUnicodeWhitespace) (l := A) c hw]
      exact ih m (by omega)
    · have hw' : isUnicodeWhitespace c = false := by simpa only [Bool.not_eq_true] using hw
      simp only [hw', Bool.false_eq_true, ↓reduceIte]
      rw [List.rdropWhile_concat_neg (p := isUnicodeWhitespace) (l := A) c
          (by simpa only [Bool.not_eq_true] using hw), ← List.reverse_append,
        List.reverse_reverse, List.flatMap_append, List.flatMap_singleton]

/-- **A07, the byte model of `str::trim` is the char-level trim**: on the UTF-8 bytes of a string,
`ExtModel.trimWhitespace` gives the bytes of `trimUnicodeWhitespace` (Unicode `White_Space`
removed at both ends). Restated as `Theorems.External.trimWhitespace_utf8Bytes` in
`Proofs.Internal.External`. No premise. -/
theorem trimWhitespace_utf8Bytes (s : String) :
    ExtModel.trimWhitespace (utf8Bytes s) = utf8Bytes (trimUnicodeWhitespace s) := by
  have hs : utf8 s = s.toList.flatMap charUtf8 := by
    conv_lhs => rw [← String.ofList_toList (s := s)]
    exact utf8_ofList_eq_flatMap _
  rw [utf8Bytes_eq_utf8, utf8Bytes_eq_utf8, trimUnicodeWhitespace, utf8_ofList_eq_flatMap, hs]
  unfold trimWhitespace
  dsimp only
  rw [dropEncodedPrefixes_whitespaceUtf8_flatMap s.toList _ le_rfl,
    dropEncodedPrefixes_map_reverse_flatMap _ _ le_rfl]

end Trim

end Proofs.External.Auth

/-! ## The `auth::prim` functions -/

namespace transport.auth.prim

open ExtModel

/-- **Spec theorem for `rmcp::transport::auth::prim::trim`**

Always succeeds with the bytes of `s` without its leading and trailing UTF-8-encoded
`White_Space` chars. -/
@[step]
theorem trim_spec (s : Str) :
    transport.auth.prim.trim s ⦃ (result : Str) => result.val = trimWhitespace s.val ⦄ := by
  exact (WP.spec_ok (p := fun result : Str => result.val = trimWhitespace s.val) _).2
    (Slice.from_val _ _)

/-- **Spec theorem for `rmcp::transport::auth::prim::starts_with`**

Always succeeds: `true` exactly when the bytes of `pre` are a prefix of the bytes of `s`. -/
@[step]
theorem starts_with_spec (s : Str) (pre : Str) :
    transport.auth.prim.starts_with s pre ⦃ (result : Bool) =>
      (result = true ↔ pre.val <+: s.val) ⦄ := by
  simp only [transport.auth.prim.starts_with, WP.spec_ok, decide_eq_true_eq]

/-- **Spec theorem for `rmcp::transport::auth::prim::strip_suffix`**

Always succeeds: the bytes of `s` before `suffix` if `suffix` is a suffix of `s`, otherwise
`None`. -/
@[step]
theorem strip_suffix_spec (s : Str) (suffix : Str) :
    transport.auth.prim.strip_suffix s suffix ⦃ (result : Option Str) =>
      result.map (·.val) = if suffix.val <:+ s.val then
        some (s.val.take (s.val.length - suffix.val.length)) else none ⦄ := by
  unfold transport.auth.prim.strip_suffix
  by_cases h : suffix.val <:+ s.val
  · rw [ite_eq_left h]
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_left h]
    exact congrArg some (Slice.from_val _ _)
  · rw [ite_eq_right h]
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_right h, Option.map_none]

/-- **Spec theorem for `rmcp::transport::auth::prim::strip_dir_prefix`**

Always succeeds: the bytes of `path` after `pre` and a `/` if `path` starts with them, otherwise
`None`. -/
@[step]
theorem strip_dir_prefix_spec (path : Str) (pre : Str) :
    transport.auth.prim.strip_dir_prefix path pre ⦃ (result : Option Str) =>
      result.map (·.val) = if pre.val ++ [47#u8] <+: path.val then
        some (path.val.drop (pre.val.length + 1)) else none ⦄ := by
  unfold transport.auth.prim.strip_dir_prefix
  by_cases h : pre.val ++ [47#u8] <+: path.val
  · rw [ite_eq_left h]
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_left h]
    exact congrArg some (Slice.from_val _ _)
  · rw [ite_eq_right h]
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_right h, Option.map_none]

/-- **Spec theorem for `rmcp::transport::auth::prim::trim_start_slashes`**

Always succeeds with the bytes of `s` without its leading `/` bytes. -/
@[step]
theorem trim_start_slashes_spec (s : Str) :
    transport.auth.prim.trim_start_slashes s ⦃ (result : Str) =>
      result.val = s.val.dropWhile (fun b => decide (b.val = 47)) ⦄ := by
  exact (WP.spec_ok (p := fun result : Str =>
    result.val = s.val.dropWhile (fun b => decide (b.val = 47))) _).2 (Slice.from_val _ _)

/-- **Spec theorem for `rmcp::transport::auth::prim::issuer_url`**

Always succeeds with the issuer `issuerUrl discovery_url issuer_path.val` (an opaque value).
This is the model; Rust panics for a discovery URL with neither query nor fragment that is longer
than `u32::MAX` bytes (stated exception, human decision AD7, docstring of
`transport.auth.prim.issuer_url`). -/
@[step]
theorem issuer_url_spec (discovery_url : url.Url) (issuer_path : Str) :
    transport.auth.prim.issuer_url discovery_url issuer_path ⦃ (result : String) =>
      result = issuerUrl discovery_url issuer_path.val ⦄ := by
  simp only [transport.auth.prim.issuer_url, WP.spec_ok]

/-- **Spec theorem for `rmcp::transport::auth::prim::debug_empty_resource_metadata`**

Always succeeds (the `tracing` event is not modelled). -/
@[step]
theorem debug_empty_resource_metadata_spec :
    transport.auth.prim.debug_empty_resource_metadata ⦃ (_ : Unit) => True ⦄ := by
  simp only [transport.auth.prim.debug_empty_resource_metadata, WP.spec_ok]

/-- **Spec theorem for `rmcp::transport::auth::prim::debug_unparsable_resource_metadata`**

Always succeeds (the `tracing` event is not modelled). -/
@[step]
theorem debug_unparsable_resource_metadata_spec (value : Str) (error : url.parser.ParseError) :
    transport.auth.prim.debug_unparsable_resource_metadata value error
      ⦃ (_ : Unit) => True ⦄ := by
  simp only [transport.auth.prim.debug_unparsable_resource_metadata, WP.spec_ok]

/-- **Spec theorem for `rmcp::transport::auth::prim::warn_downgraded_resource_metadata`**

Always succeeds (the `tracing` event is not modelled). -/
@[step]
theorem warn_downgraded_resource_metadata_spec (target base_url : url.Url) :
    transport.auth.prim.warn_downgraded_resource_metadata target base_url
      ⦃ (_ : Unit) => True ⦄ := by
  simp only [transport.auth.prim.warn_downgraded_resource_metadata, WP.spec_ok]

/-- **Spec theorem for `rmcp::transport::auth::prim::warn_disallowed_resource_metadata`**

Always succeeds (the `tracing` event is not modelled). -/
@[step]
theorem warn_disallowed_resource_metadata_spec (target base_url : url.Url) :
    transport.auth.prim.warn_disallowed_resource_metadata target base_url
      ⦃ (_ : Unit) => True ⦄ := by
  simp only [transport.auth.prim.warn_disallowed_resource_metadata, WP.spec_ok]

end transport.auth.prim

/-! ## Standard library and `url` -/

open ExtModel

/-- **Spec theorem for `Option::zip`**

Always succeeds: `Some((a, b))` for `Some(a)` and `Some(b)`, otherwise `None`. -/
@[step]
theorem core.option.Option.zip_spec {T U : Type} (self : Option T) (other : Option U) :
    core.option.Option.zip self other ⦃ (result : Option (T × U)) =>
      result = self.bind (fun a => other.map (fun b => (a, b))) ⦄ := by
  cases self <;> cases other <;>
    simp only [core.option.Option.zip, WP.spec_ok, Option.bind_none, Option.bind_some,
      Option.map_none, Option.map_some]

/-- **Spec theorem for `str::eq_ignore_ascii_case`**

Always succeeds: `true` exactly when the bytes agree after mapping `A`–`Z` to `a`–`z`. -/
@[step]
theorem core.str.Str.eq_ignore_ascii_case_spec (self : Str) (other : Str) :
    core.str.Str.eq_ignore_ascii_case self other ⦃ (result : Bool) =>
      (result = true ↔ self.val.map asciiLowercase = other.val.map asciiLowercase) ⦄ := by
  simp only [core.str.Str.eq_ignore_ascii_case, WP.spec_ok, decide_eq_true_eq]

/-- **Spec theorem for `<url::Url as Clone>::clone`**

Always succeeds with the same URL. -/
@[step]
theorem url.Url.Insts.CoreCloneClone.clone_spec (self : url.Url) :
    url.Url.Insts.CoreCloneClone.clone self ⦃ (result : url.Url) => result = self ⦄ := by
  simp only [url.Url.Insts.CoreCloneClone.clone, WP.spec_ok]

/-- **Spec theorem for `url::Url::join`**

Always succeeds with the resolution outcome `urlJoin self input.val` (an opaque value). This is
the model; with debug assertions on, Rust can panic for a `file:` base whose last path segment is
a normalized Windows drive letter, joined with an input whose first segment is `..` or a
percent-encoded double dot (stated exception, human decision AD8, docstring of `url.Url.join`;
the condition is a superset description: `file:///C:` joined with `..` does not panic). -/
@[step]
theorem url.Url.join_spec (self : url.Url) (input : Str) :
    url.Url.join self input ⦃ (result : core.result.Result url.Url url.parser.ParseError) =>
      result = urlJoin self input.val ⦄ := by
  simp only [url.Url.join, WP.spec_ok]

/-- **Spec theorem for `url::Url::scheme`**

Always succeeds with the scheme `urlScheme self` (an opaque value). -/
@[step]
theorem url.Url.scheme_spec (self : url.Url) :
    url.Url.scheme self ⦃ (result : Str) => result = urlScheme self ⦄ := by
  simp only [url.Url.scheme, WP.spec_ok]

/-- **Spec theorem for `url::Url::port_or_known_default`**

Always succeeds with the explicit port `urlPort self`, or if there is none the default port of
the scheme `urlScheme self`. -/
@[step]
theorem url.Url.port_or_known_default_spec (self : url.Url) :
    url.Url.port_or_known_default self ⦃ (result : Option Std.U16) =>
      result = (urlPort self).or (defaultPort (urlScheme self).val) ⦄ := by
  unfold url.Url.port_or_known_default
  cases urlPort self <;> simp only [WP.spec_ok, Option.some_or, Option.none_or]

/-- **Spec theorem for `url::Url::path`**

Always succeeds with the path `urlPath self` (an opaque value). -/
@[step]
theorem url.Url.path_spec (self : url.Url) :
    url.Url.path self ⦃ (result : Str) => result = urlPath self ⦄ := by
  simp only [url.Url.path, WP.spec_ok]

/-- **Spec theorem for `url::Url::fragment`**

Always succeeds with the fragment `urlFragment self` (an opaque value). -/
@[step]
theorem url.Url.fragment_spec (self : url.Url) :
    url.Url.fragment self ⦃ (result : Option Str) => result = urlFragment self ⦄ := by
  simp only [url.Url.fragment, WP.spec_ok]

/-- **Spec theorem for `<url::Url as PartialEq>::eq`**

Always succeeds: `true` exactly when the serializations are equal. -/
@[step]
theorem url.Url.Insts.CoreCmpPartialEqUrl.eq_spec (self : url.Url) (other : url.Url) :
    url.Url.Insts.CoreCmpPartialEqUrl.eq self other ⦃ (result : Bool) =>
      (result = true ↔ urlSerialization self = urlSerialization other) ⦄ := by
  simp only [url.Url.Insts.CoreCmpPartialEqUrl.eq, WP.spec_ok, decide_eq_true_eq]

/-! ## Evaluation of the models

Kernel evaluation (`decide`) of the exact models on small inputs; each value is the one Rust
computes (checked against the Rust documentation and the sources cited at each model). -/

namespace Proofs.External.Auth

open Proofs.External.Utf8

/-- `" \t a b\u{a0}\u{3000}\n".trim() == "a b"`: ASCII and multi-byte whitespace at both ends,
the inner space kept. -/
example : trimWhitespace [0x20#u8, 0x09#u8, 0x61#u8, 0x20#u8, 0x62#u8, 0xC2#u8, 0xA0#u8,
    0xE3#u8, 0x80#u8, 0x80#u8, 0x0A#u8] = [0x61#u8, 0x20#u8, 0x62#u8] := by
  decide

/-- `" \u{2028} ".trim() == ""`: only whitespace. -/
example : trimWhitespace [0x20#u8, 0xE2#u8, 0x80#u8, 0xA8#u8, 0x20#u8] = [] := by decide

/-- `"\u{200b}x".trim()` keeps U+200B ZERO WIDTH SPACE (`E2 80 8B`), which is not
`White_Space`; `"\u{1c}x".trim()` keeps U+001C, which `char::is_whitespace` excludes. -/
example : trimWhitespace [0xE2#u8, 0x80#u8, 0x8B#u8, 0x78#u8] = [0xE2#u8, 0x80#u8, 0x8B#u8, 0x78#u8]
    ∧ trimWhitespace [0x1C#u8, 0x78#u8] = [0x1C#u8, 0x78#u8] := by
  decide

/-- `"\u{85}é".trim()` drops U+0085 (`C2 85`) and keeps `é` (`C3 A9`). -/
example : trimWhitespace [0xC2#u8, 0x85#u8, 0xC3#u8, 0xA9#u8] = [0xC3#u8, 0xA9#u8] := by decide

/-- The default ports of `url::parser::default_port`. -/
example : defaultPort (utf8 "http") = some 80#u16 ∧ defaultPort (utf8 "wss") = some 443#u16 ∧
    defaultPort (utf8 "ftp") = some 21#u16 ∧ defaultPort (utf8 "file") = none := by
  have hi : ∀ s t : String, utf8 s = utf8 t ↔ s = t :=
    fun _ _ => ⟨utf8_injective, congrArg utf8⟩
  simp only [defaultPort, hi]
  decide

end Proofs.External.Auth
