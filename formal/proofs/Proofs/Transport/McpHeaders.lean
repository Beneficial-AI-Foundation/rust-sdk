/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Proofs.Transport.McpHeaders.Common

@[expose] public section

/-!
# Spec theorems for the SEP-2243 header-value encoding of `mcp_headers.rs` (G01–G04)

The private functions of `crates/rmcp/src/transport/common/mcp_headers.rs` that translation
patch 07 makes translatable (human decisions GD1–GD3): G01 `requires_base64`, G02 `is_tchar`,
G03 `encode_header_value`, G04 `decode_header_value`. First the laws of the definitions of
`Defs.McpHeaders` (in the namespace `Defs.McpHeaders`), then the spec theorems with their failure
companions, then the compositions (round trip, header safety, the token characters, what the
decoder accepts and rejects).

The statements are the ones signed off by the human spec owner on 2026-11-28 (statements
unchanged); they are restated, as `Theorems.mcp_headers.*`, in
`Proofs.Internal.Transport.Common.McpHeaders`, with the decisions CD1–CD7 (H17, H18) and the
premise keys. Each spec theorem is proved through the equations of
`Proofs.Transport.McpHeaders.Common`; the compositions combine the spec theorems with the laws.

Source: "crates/rmcp/src/transport/common/mcp_headers.rs", upstream `7caec76` lines 62–77,
81–100, 242–252 and 256–268, translated through `formal/trusted/patches/07-mcp-headers.patch`
(patched lines 62–76, 80–98, 240–246 and 250–261)
-/

open Aeneas Aeneas.Std Result
open rmcp
open Defs (utf8Bytes)
open Defs.McpHeaders
open ExtModel Proofs.External.Utf8 Proofs.External.Base64Std
open Proofs.Transport.McpHeaders

set_option autoImplicit false

/-! ## Laws of `Defs.McpHeaders` -/

namespace Defs.McpHeaders

/-- **`tchar` is VCHAR except the delimiters** (RFC 9110 §5.6.2: "any VCHAR, except
delimiters"): the ABNF list and the prose of the RFC agree. In particular every token character
is visible ASCII (`0x21`–`0x7E`): no SP, no control, nothing non-ASCII. -/
theorem isTchar_eq_true_iff_isVchar_and_not_isDelimiter (c : Char) :
    isTchar c = true ↔ isVchar c = true ∧ isDelimiter c = false := by
  rw [isTchar_eq_decide, decide_eq_true_iff]
  unfold isVchar isDelimiter
  rw [decide_eq_true_iff, decide_eq_false_iff_not, mem_iff_toNat_mem, map_toNat_delimiters]
  by_cases h : c.toNat < 128
  · exact tcharCode_iff_vchar _ h
  · simp only [punctCodes, List.mem_cons, List.not_mem_nil]
    generalize c.toNat = n at *
    simp only [or_false]
    exact iff_of_false (by omega) (by omega)

/-- **The token characters are the 77 chars of `tchars`.** -/
theorem isTchar_eq_true_iff_mem_tchars (c : Char) : isTchar c = true ↔ c ∈ tchars := by
  rw [isTchar_eq_decide, decide_eq_true_iff, mem_iff_toNat_mem, map_toNat_tchars]
  by_cases h : c.toNat < 128
  · exact tcharCode_iff_mem _ h
  · simp only [List.mem_append, List.mem_range'_1, punctCodes, List.mem_cons, List.not_mem_nil]
    generalize c.toNat = n at *
    simp only [or_false]
    exact iff_of_false (by omega) (by omega)

/-- `tchars` has 77 elements (94 VCHAR minus 17 delimiters). -/
theorem length_tchars : tchars.length = 77 := by
  decide +kernel

/-- `tchars` has no repetition, so it lists 77 distinct characters. -/
theorem nodup_tchars : tchars.Nodup := by
  rw [← List.nodup_map_iff (f := Char.toNat) (fun a b h => Char.ext (UInt32.toNat_inj.1 h)),
    map_toNat_tchars]
  decide +kernel

/-- **G01 at the char level, on UTF-8** (the reading of the Rust doc, upstream lines 58–60 and
the code of lines 63–76): for the bytes of a string `v`, wrapping is required exactly when the
first or the last char is SP or HTAB, or some char has a code point below `0x20` or above
`0x7E` (`(c as u32) < 0x20 || (c as u32) > 0x7E`, lines 70–75), or `v` starts with `=?base64?`
and ends with `?=`. (The first byte of a UTF-8 string is SP or HTAB exactly when its first char
is, and likewise for the last; `Proofs.External.Base64Std.any_isControlOrNonAsciiByte_utf8` for
the middle test.) -/
theorem requiresBase64_utf8Bytes (v : String) :
    requiresBase64 (utf8Bytes v) =
      (v.toList.head?.any (fun c => decide (c = ' ' ∨ c = '\t')) ||
        v.toList.getLast?.any (fun c => decide (c = ' ' ∨ c = '\t')) ||
        v.toList.any (fun c => decide (c.toNat < 0x20 ∨ 0x7E < c.toNat)) ||
        (decide ("=?base64?".toList <+: v.toList) && decide ("?=".toList <:+ v.toList))) := by
  have hmid : (utf8Bytes v).any (fun b => !isPrintableAscii b) =
      v.toList.any (fun c => decide (c.toNat < 0x20 ∨ 0x7E < c.toNat)) := by
    rw [← any_isControlOrNonAsciiByte_utf8]
    show (utf8 v).any _ = _
    congr 1; funext b
    exact not_isPrintableAscii_eq b
  have hhead : (utf8Bytes v).head?.any isSpaceOrTab =
      v.toList.head?.any (fun c => decide (c = ' ' ∨ c = '\t')) := by
    show (utf8 v).head?.any _ = _
    rw [utf8_eq_flatMap]; exact any_head?_flatMap utf8Char utf8Char_of_lt utf8Char_of_le _
  have hlast : (utf8Bytes v).getLast?.any isSpaceOrTab =
      v.toList.getLast?.any (fun c => decide (c = ' ' ∨ c = '\t')) := by
    show (utf8 v).getLast?.any _ = _
    rw [utf8_eq_flatMap, ← List.head?_reverse, ← List.head?_reverse, reverse_flatMap_utf8Char]
    exact any_head?_flatMap _ reverse_utf8Char_of_lt reverse_utf8Char_of_le _
  have hpre : (base64Prefix <+: utf8Bytes v) ↔ "=?base64?".toList <+: v.toList := by
    have : base64Prefix = "=?base64?".toList.flatMap utf8Char := by
      show utf8 "=?base64?" = _; rw [utf8_eq_flatMap]
    rw [this]; show _ <+: utf8 v ↔ _; rw [utf8_eq_flatMap]
    refine isPrefix_flatMap_iff utf8Char utf8Char_of_lt utf8Char_of_le _ _ ?_
    simp
  have hsuf : (base64Suffix <:+ utf8Bytes v) ↔ "?=".toList <:+ v.toList := by
    have : base64Suffix = "?=".toList.flatMap utf8Char := by
      show utf8 "?=" = _; rw [utf8_eq_flatMap]
    rw [this]; show _ <:+ utf8 v ↔ _; rw [utf8_eq_flatMap]
    rw [← List.reverse_prefix, ← List.reverse_prefix, reverse_flatMap_utf8Char,
      reverse_flatMap_utf8Char]
    refine isPrefix_flatMap_iff _ reverse_utf8Char_of_lt reverse_utf8Char_of_le _ _ ?_
    simp
  unfold requiresBase64
  rw [hhead, hlast, hmid, decide_eq_decide.2 hpre, decide_eq_decide.2 hsuf]

/-- **A value that is not wrapped is UTF-8**: its bytes are printable ASCII. So G03 never reaches
the `fail undef` of the `str::to_owned` model, and needs no UTF-8 premise. -/
theorem isUtf8_of_requiresBase64_eq_false (s : List U8) (h : requiresBase64 s = false) :
    ExtModel.IsUtf8 s := by
  have hp := isPrintableAscii_of_requiresBase64_eq_false h
  refine ⟨String.ofList (s.map (fun b => Char.ofNat b.val)), (utf8_ofList_ascii s ?_).symm⟩
  intro b hb
  have := hp b hb
  simp only [isPrintableAscii, decide_eq_true_eq] at this
  omega

/-- **G04's sentinel**: `sentinelInner? s = some inner` exactly when `s` is `=?base64?` ++
`inner` ++ `?=` (`strip_prefix` then `strip_suffix`, upstream lines 258–261). -/
theorem sentinelInner?_eq_some_iff (s inner : List U8) :
    sentinelInner? s = some inner ↔ s = wrapSentinel inner := by
  unfold sentinelInner? wrapSentinel
  constructor
  · intro h
    split_ifs at h with hc
    obtain ⟨⟨r, rfl⟩, hq⟩ := hc
    simp only [Option.some.injEq, List.drop_left'] at h hq
    obtain ⟨q, rfl⟩ := hq
    simp only [List.length_append, Nat.add_sub_cancel, List.take_left'] at h
    subst h; simp
  · intro h; subst h
    simp [List.append_assoc, length_base64Suffix]

/-- **A value that is not wrapped is no sentinel for G04**: G01's sentinel test (prefix and
suffix, line 76) is implied by G04's (prefix, then suffix of the rest, lines 259–260). This is
why the round trip has no gap. -/
theorem sentinelInner?_eq_none_of_requiresBase64_eq_false (s : List U8)
    (h : requiresBase64 s = false) : sentinelInner? s = none := by
  cases hs : sentinelInner? s with
  | none => rfl
  | some inner =>
    rw [sentinelInner?_eq_some_iff] at hs
    rw [hs, requiresBase64_wrapSentinel] at h
    exact absurd h (by simp)

/-- **G01's sentinel-shape test and G04's sentinel test disagree only on `=?base64?=`**: a value
that starts with `=?base64?` and ends with `?=` (G01, line 76; the fourth disjunct of
`requiresBase64`) and yet is no sentinel for G04 (lines 258–261: the suffix is looked for after
the prefix) is exactly the 10-byte `=?base64?=`, where prefix and suffix overlap in one `=`.
Every other value passing G01's test is `=?base64?` ++ `inner` ++ `?=` (CD2). -/
theorem prefix_and_suffix_and_sentinelInner?_eq_none_iff (s : List U8) :
    base64Prefix <+: s ∧ base64Suffix <:+ s ∧ sentinelInner? s = none ↔
      s = utf8Bytes "=?base64?=" := by
  constructor
  · rintro ⟨⟨r, rfl⟩, hsuf, hnone⟩
    have hnot : ¬ base64Suffix <:+ r := by
      intro hr
      have := (sentinelInner?_eq_some_iff (base64Prefix ++ r)
        (r.take (r.length - base64Suffix.length))).2
      obtain ⟨q, rfl⟩ := hr
      rw [hnone] at this
      have := this (by simp [wrapSentinel, length_base64Suffix])
      simp at this
    have hr : r.length ≤ 1 := by
      by_contra hl
      apply hnot
      exact List.suffix_of_suffix_length_le hsuf (List.suffix_append _ _)
        (by rw [length_base64Suffix]; omega)
    match r, hr with
    | [], _ => exact absurd hsuf (by decide +kernel)
    | [x], _ =>
      obtain ⟨t, ht⟩ := hsuf
      have h1 := congrArg List.getLast? ht
      have hx : x = ExtModel.byte 61 := by
        have e2 : base64Suffix.getLast? = some (ExtModel.byte 61) := by decide +kernel
        have e1 : (t ++ base64Suffix).getLast? = some (ExtModel.byte 61) := by
          rw [List.getLast?_append, e2]; rfl
        rw [e1] at h1
        simp at h1; exact h1.symm
      subst hx; decide +kernel
  · rintro rfl; decide +kernel

/-- **What G04 accepts** (property (e), on the model): `decodeHeaderValue s = some y` exactly when
`s` is no sentinel and `y = s` (returned unchanged, upstream line 266, patched lines 257 and
259), or `s` is the sentinel around the canonical padded standard Base64 encoding of `y` and `y`
is UTF-8
(`Proofs.External.Base64Std.b64StdPadDecode_eq_some_iff`: the strict decoder accepts exactly the
outputs of the encoder). -/
theorem decodeHeaderValue_eq_some_iff (s y : List U8) :
    decodeHeaderValue s = some y ↔
      (sentinelInner? s = none ∧ y = s) ∨
        (s = wrapSentinel (ExtModel.b64StdPad y) ∧ ExtModel.IsUtf8 y) := by
  unfold decodeHeaderValue
  cases hs : sentinelInner? s with
  | none =>
    simp only [Option.some.injEq, true_and]
    constructor
    · intro h; exact Or.inl h.symm
    · rintro (h | ⟨h, _⟩)
      · exact h.symm
      · rw [h, (sentinelInner?_eq_some_iff _ _).2 rfl] at hs; exact absurd hs (by simp)
  | some inner =>
    have hw := (sentinelInner?_eq_some_iff s inner).1 hs
    simp only [reduceCtorEq, false_and, false_or, Option.filter_eq_some_iff,
      b64StdPadDecode_eq_some_iff, isSome_strOfBytes?_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by rw [hw, h1], h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(wrapSentinel_injective (hw ▸ h1)).symm, h2⟩

/-- **What G04 rejects**: `none` exactly for a sentinel whose inner text is the padded standard
Base64 encoding of no UTF-8 byte string (invalid Base64, non-canonical padding or trailing bits,
or decoded bytes that are not UTF-8; "Returns `None` if the sentinel wraps invalid
Base64/UTF-8", line 254). -/
theorem decodeHeaderValue_eq_none_iff (s : List U8) :
    decodeHeaderValue s = none ↔
      ∃ inner, s = wrapSentinel inner ∧
        ∀ y, ExtModel.IsUtf8 y → ExtModel.b64StdPad y ≠ inner := by
  unfold decodeHeaderValue
  cases hi : sentinelInner? s with
  | none =>
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro inner hs
    rw [hs, (sentinelInner?_eq_some_iff _ _).2 rfl] at hi
    simp at hi
  | some inner =>
    have hs := (sentinelInner?_eq_some_iff _ _).1 hi
    simp only
    constructor
    · intro h
      refine ⟨inner, hs, ?_⟩
      intro y hy he
      subst he
      rw [b64StdPadDecode_b64StdPad] at h
      simp [Option.filter_some, (isSome_strOfBytes?_iff y).2 hy] at h
    · rintro ⟨inner', hs', hno⟩
      have : inner' = inner := by
        rw [hs', (sentinelInner?_eq_some_iff _ _).2 rfl] at hi; simpa using hi
      subst this
      cases hd : ExtModel.b64StdPadDecode inner' with
      | none => rfl
      | some y =>
        have he := (b64StdPadDecode_eq_some_iff _ _).1 hd
        have : ¬ ExtModel.IsUtf8 y := fun hy => hno y hy he
        rw [← isSome_strOfBytes?_iff] at this
        simp [Option.filter_some, this]

/-- **G03 leaves a value unchanged exactly when it does not wrap it** (property (c), on the
model; the wrapped form is longer than the value: `4 ⌈n / 3⌉ + 11 > n`). -/
theorem encodeHeaderValue_eq_self_iff (s : List U8) :
    encodeHeaderValue s = s ↔ requiresBase64 s = false := by
  unfold encodeHeaderValue
  cases h : requiresBase64 s
  · simp
  · simp only [↓reduceIte, Bool.true_eq_false, iff_false]
    intro he
    have := congrArg List.length he
    rw [length_wrapSentinel, length_b64StdPad] at this
    omega

/-- **Header safety, `0x20`–`0x7E` form** (property (b), on the model): every byte of the encoded
value is printable ASCII and it neither starts nor ends with SP or HTAB. So it contains no CR,
LF, NUL or other control byte (no header injection, no response splitting) and no `obs-text`. -/
theorem isBareHeaderValue_encodeHeaderValue (s : List U8) :
    IsBareHeaderValue (encodeHeaderValue s) := by
  unfold encodeHeaderValue
  cases h : requiresBase64 s
  · simp only [Bool.false_eq_true, ite_false]
    simp only [requiresBase64, Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    obtain ⟨⟨⟨hh, hl⟩, hp⟩, -⟩ := h
    refine ⟨fun b hb => ?_, ?_, ?_⟩
    · have := hp b hb; simpa using this
    · cases hs : s.head? <;> simp_all
    · cases hs : s.getLast? <;> simp_all
  · simp only [ite_true]
    refine ⟨fun b hb => ?_, ?_, ?_⟩
    · unfold wrapSentinel at hb
      simp only [List.mem_append] at hb
      rcases hb with (hb | hb) | hb
      · have : ∀ c ∈ base64Prefix, isPrintableAscii c = true := by decide +kernel
        exact this b hb
      · have := visible_of_mem_b64StdPad hb
        simp only [isPrintableAscii, decide_eq_true_eq]; omega
      · have : ∀ c ∈ base64Suffix, isPrintableAscii c = true := by decide +kernel
        exact this b hb
    · have : (wrapSentinel (b64StdPad s)).head? = base64Prefix.head? := by
        unfold wrapSentinel; rw [List.append_assoc, List.head?_append_of_ne_nil]; decide +kernel
      rw [this]; decide +kernel
    · have : (wrapSentinel (b64StdPad s)).getLast? = base64Suffix.getLast? := by
        unfold wrapSentinel; rw [List.getLast?_append_of_ne_nil]; decide +kernel
      rw [this]; decide +kernel

/-- **The wrapped form** (G03, upstream lines 244–248): a value that must be wrapped is sent as
`=?base64?` ++ the padded standard Base64 of its bytes ++ `?=`. -/
theorem encodeHeaderValue_eq_wrapSentinel_of_requiresBase64_eq_true (s : List U8)
    (h : requiresBase64 s = true) :
    encodeHeaderValue s = wrapSentinel (ExtModel.b64StdPad s) := by
  simp [encodeHeaderValue, h]

/-- **The bare form** (G03, upstream line 250): a value that need not be wrapped is sent
unchanged. -/
theorem encodeHeaderValue_eq_self_of_requiresBase64_eq_false (s : List U8)
    (h : requiresBase64 s = false) : encodeHeaderValue s = s := by
  simp [encodeHeaderValue, h]

/-- **Header safety, wrapped form** (property (b)): a wrapped value is `=?base64?`, the padded
Base64 symbols and `?=`, all visible ASCII `0x21`–`0x7E` (no SP either;
`Proofs.External.Base64Std.visible_of_mem_b64StdPad`). -/
theorem isVisibleAscii_encodeHeaderValue_of_requiresBase64_eq_true (s : List U8)
    (h : requiresBase64 s = true) : IsVisibleAscii (encodeHeaderValue s) := by
  rw [encodeHeaderValue_eq_wrapSentinel_of_requiresBase64_eq_true s h]
  intro b hb
  simp only [wrapSentinel, List.mem_append] at hb
  rcases hb with (hb | hb) | hb
  · rw [base64Prefix_eq] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact visible_of_mem_b64StdPad hb
  · rw [base64Suffix_eq] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> decide

/-- **A bare header value is an RFC 9110 field value** (§5.5). -/
theorem isFieldValue_of_isBareHeaderValue (s : List U8) (h : IsBareHeaderValue s) :
    IsFieldValue s := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun b hb => ?_, h2, h3⟩
  have := h1 b hb
  simp only [isPrintableAscii, decide_eq_true_eq] at this
  by_cases hb20 : b.val = 0x20
  · right; right; simp [isSpaceOrTab, hb20]
  · left; omega

/-- **Every wrapped UTF-8 value decodes, whether or not G03 would wrap it** (CD1): for a value
that G03 sends bare (`requiresBase64 s = false`), both `s` and this sentinel decode to `s`. -/
theorem decodeHeaderValue_wrapSentinel_b64StdPad (s : List U8) (h : ExtModel.IsUtf8 s) :
    decodeHeaderValue (wrapSentinel (ExtModel.b64StdPad s)) = some s := by
  unfold decodeHeaderValue
  rw [(sentinelInner?_eq_some_iff _ _).2 rfl]
  simp only [b64StdPadDecode_b64StdPad, Option.filter_some, (isSome_strOfBytes?_iff s).2 h,
    ite_true]

/-- **Round trip on the model** (property (a)): decoding the encoding of UTF-8 bytes gives them
back. A bare value is no sentinel (`sentinelInner?_eq_none_of_requiresBase64_eq_false`); a
wrapped one decodes by the Base64 round trip
(`Proofs.External.Base64Std.b64StdPadDecode_b64StdPad`) and is UTF-8 by premise. -/
theorem decodeHeaderValue_encodeHeaderValue (s : List U8) (h : ExtModel.IsUtf8 s) :
    decodeHeaderValue (encodeHeaderValue s) = some s := by
  unfold encodeHeaderValue
  split_ifs with hr
  · exact decodeHeaderValue_wrapSentinel_b64StdPad s h
  · unfold decodeHeaderValue
    rw [sentinelInner?_eq_none_of_requiresBase64_eq_false s (by simpa using hr)]

/-- **G03 is injective** on all byte strings: distinct values give distinct header values (a
bare value is never of the wrapped form, which is a sentinel shape; two wrapped forms are equal
only for equal Base64, hence equal values). -/
theorem encodeHeaderValue_injective : Function.Injective encodeHeaderValue := by
  intro a b h
  unfold encodeHeaderValue at h
  cases ha : requiresBase64 a <;> cases hb : requiresBase64 b <;> simp only [ha, hb] at h <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
  · exact h
  · rw [h, requiresBase64_wrapSentinel] at ha; exact absurd ha (by simp)
  · rw [← h, requiresBase64_wrapSentinel] at hb; exact absurd hb (by simp)
  · have := wrapSentinel_injective h
    have h2 := b64StdPadDecode_b64StdPad a
    rw [this, b64StdPadDecode_b64StdPad] at h2
    exact (Option.some.inj h2).symm

/-- **G04 against G03** (CD1, CD2): for a header value `s` that is UTF-8 (every value
`header_str` passes on), `decodeHeaderValue s = some y` exactly when `y` is UTF-8 and either `s`
is G03's encoding of `y`, or `s` is a form G03 never sends for `y`: the sentinel around the
Base64 of a `y` that G03 sends bare (CD1), or `y` itself, bare, although G03 wraps it, provided
`y` is no sentinel for G04 (CD2). -/
theorem decodeHeaderValue_eq_some_iff_encodeHeaderValue (s y : List U8)
    (hs : ExtModel.IsUtf8 s) :
    decodeHeaderValue s = some y ↔
      ExtModel.IsUtf8 y ∧
        (s = encodeHeaderValue y ∨
          (requiresBase64 y = false ∧ s = wrapSentinel (ExtModel.b64StdPad y)) ∨
          (requiresBase64 y = true ∧ sentinelInner? s = none ∧ s = y)) := by
  constructor
  · intro h
    unfold decodeHeaderValue at h
    cases hi : sentinelInner? s with
    | none =>
      rw [hi] at h; simp only [Option.some.injEq] at h; subst h
      refine ⟨hs, ?_⟩
      cases hr : requiresBase64 s
      · left; unfold encodeHeaderValue; simp [hr]
      · right; right; exact ⟨rfl, rfl, rfl⟩
    | some inner =>
      rw [hi] at h
      rw [sentinelInner?_eq_some_iff] at hi
      rw [Option.filter_eq_some_iff] at h
      obtain ⟨hd, hu⟩ := h
      rw [b64StdPadDecode_eq_some_iff] at hd
      subst hd hi
      have hy := (isSome_strOfBytes?_iff y).1 hu
      refine ⟨hy, ?_⟩
      cases hr : requiresBase64 y
      · right; left; exact ⟨rfl, rfl⟩
      · left; unfold encodeHeaderValue; simp [hr]
  · rintro ⟨hy, h | ⟨_, h⟩ | ⟨_, hi, h⟩⟩
    · subst h; exact decodeHeaderValue_encodeHeaderValue y hy
    · subst h; exact decodeHeaderValue_wrapSentinel_b64StdPad y hy
    · subst h; unfold decodeHeaderValue; rw [hi]

end Defs.McpHeaders

/-! ## G03 and G04 as successful calls -/

namespace Proofs.Transport.McpHeaders

/-- G03 under (E) returns a `String` whose bytes are `encodeHeaderValue value.val`. -/
theorem exists_encode_header_value_eq_ok (value : Str) (h_fits : EncodeFits value.val) :
    ∃ r, transport.common.mcp_headers.encode_header_value value = ok r ∧
      utf8Bytes r = encodeHeaderValue value.val := by
  cases h_req : requiresBase64 value.val
  · obtain ⟨t, ht⟩ := isUtf8_of_requiresBase64_eq_false _ h_req
    refine ⟨t, ?_, ?_⟩
    · unfold transport.common.mcp_headers.encode_header_value
      rw [requires_base64_eq, bind_ok, h_req, to_owned_eq, ht, strOfBytes?_utf8]; rfl
    · unfold encodeHeaderValue; rw [h_req, ht]; rfl
  · have hf := h_fits h_req
    rw [encode_header_value_eq_of_requiresBase64_eq_true value h_req]
    obtain ⟨s, hs, hsv⟩ := Proofs.External.WP.exists_ok_of_spec
      (transport.common.mcp_headers.prim.base64_encode_spec value (by omega))
    have hlen : s.utf8ByteSize ≤ Usize.max := by
      rw [← length_utf8, hsv, length_b64StdPad]
      exact (by omega : _ ≤ maxStringBytes).trans maxStringBytes_le_usize_max
    obtain ⟨e, he, hev⟩ := Proofs.External.WP.exists_ok_of_spec
      (alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec s hlen)
    obtain ⟨r, hr, hrv⟩ := Proofs.External.WP.exists_ok_of_spec
      (transport.common.mcp_headers.prim.wrap_sentinel_spec e s hev
        (by rw [hev, hsv, length_b64StdPad]; exact hf))
    refine ⟨r, by rw [hs, bind_ok, he, bind_ok, hr], ?_⟩
    unfold encodeHeaderValue
    rw [h_req, ite_eq_left rfl, Proofs.External.Utf8.utf8Bytes_eq_utf8, hrv.2, hev, hsv]
    rfl

/-- G04 under (U) and (D) returns an `Option String` whose bytes are
`decodeHeaderValue value.val`. -/
theorem exists_decode_header_value_eq_ok (value : Str)
    (h_utf8 : sentinelInner? value.val = none → ExtModel.IsUtf8 value.val)
    (h_fits : DecodeFits value.val) :
    ∃ r, transport.common.mcp_headers.decode_header_value value = ok r ∧
      r.map utf8Bytes = decodeHeaderValue value.val := by
  rw [decode_header_value_eq]
  unfold decodeHeaderValue
  cases hs : sentinelInner? value.val with
  | none =>
    obtain ⟨t, ht⟩ := h_utf8 hs
    refine ⟨some t, ?_, ?_⟩
    · simp only; rw [to_owned_eq, ht, strOfBytes?_utf8]; simp only [bind_ok]
    · rw [Option.map_some, ht]; rfl
  | some inner =>
    simp only [ite_eq_right (Nat.not_lt.2 (h_fits inner hs))]
    exact ⟨_, rfl, map_utf8Bytes_bind_strOfBytes? _⟩

theorem length_le_of_sentinelInner?_eq_some {s inner : List U8}
    (h : sentinelInner? s = some inner) : inner.length ≤ s.length := by
  rw [(sentinelInner?_eq_some_iff s inner).1 h, length_wrapSentinel]; omega

end Proofs.Transport.McpHeaders

/-! ## G01–G04 (upstream lines 62–268, patched 62–261), in Rust source order -/

namespace rmcp.transport.common.mcp_headers

/-- **Spec theorem for `rmcp::transport::common::mcp_headers::requires_base64`** (G01; upstream
lines 62–77, patched 62–76)

Never fails, on every `Str` (all checks read bytes; the control/non-ASCII test is the byte-level
model, equal to Rust's char-level test on UTF-8, law `requiresBase64_utf8Bytes`). `true` exactly
when the value is non-empty and its first or last byte is SP or HTAB (lines 66–69), or some byte
is outside `0x20`–`0x7E` (lines 70–75), or it starts with `=?base64?` and ends with `?=` (line 76,
possibly overlapping) (`Defs.McpHeaders.requiresBase64`; the empty value gives `false`, lines
63–65). No premise. -/
@[step]
theorem requires_base64_spec (value : Str) :
    requires_base64 value ⦃ (result : Bool) =>
      result = requiresBase64 value.val ⦄ := by
  rw [requires_base64_eq, WP.spec_ok]

/-- **Spec theorem for `rmcp::transport::common::mcp_headers::is_tchar`** (G02; upstream lines
81–100, patched 80–98)

Never fails. `true` exactly for an RFC 9110 §5.6.2 token character: an ASCII letter or digit
(`is_ascii_alphanumeric`, line 82) or one of `` !#$%&'*+-.^_`|~ `` (lines 83–99; patched 82–97, the
quote compared as `char::from(b'\'')`) (`Defs.McpHeaders.isTchar`). No premise. -/
@[step]
theorem is_tchar_spec (c : Char) :
    is_tchar c ⦃ (result : Bool) =>
      result = isTchar c ⦄ := by
  rw [is_tchar_eq, WP.spec_ok]

/-- **Spec theorem for `rmcp::transport::common::mcp_headers::encode_header_value`** (G03;
upstream lines 242–252, patched 240–246)

Never fails under (E). The bytes of the result are `Defs.McpHeaders.encodeHeaderValue value.val`:
if `requires_base64(value)` (line 244), `=?base64?` ++ the padded standard Base64 encoding of the
bytes of `value` ++ `?=` (lines 245–248); otherwise the bytes of `value` (`value.to_owned()`,
line 250). Premise (E) `EncodeFits value.val`: a wrapped value fits in `isize::MAX` bytes;
exact (`encode_header_value_fail`). No UTF-8 premise: a value that is not UTF-8 is wrapped
(`Defs.McpHeaders.isUtf8_of_requiresBase64_eq_false`), and the wrapping branch reads only bytes;
for such a value the result is the wrapped Base64 of its bytes. -/
@[step]
theorem encode_header_value_spec (value : Str)
    (h_fits : EncodeFits value.val) :
    encode_header_value value ⦃ (result : String) =>
      utf8Bytes result = encodeHeaderValue value.val ⦄ := by
  obtain ⟨r, hr, hv⟩ := exists_encode_header_value_eq_ok value h_fits
  rw [hr, WP.spec_ok]; exact hv

/-- G03 without (E): a value that must be wrapped and whose wrapped form exceeds `isize::MAX`
bytes makes the call panic (in `base64_encode` if the Base64 text alone is too long, otherwise in
`wrap_sentinel`; Rust panics there too, "capacity overflow"). -/
theorem encode_header_value_fail (value : Str)
    (h_req : requiresBase64 value.val = true)
    (h_len : ExtModel.maxStringBytes < (value.val.length + 2) / 3 * 4 + 11) :
    encode_header_value value = fail Error.panic := by
  rw [encode_header_value_eq_of_requiresBase64_eq_true value h_req]
  by_cases h1 : ExtModel.maxStringBytes < (value.val.length + 2) / 3 * 4
  · rw [transport.common.mcp_headers.prim.base64_encode_fail value h1, bind_fail]
  · obtain ⟨s, hs, hsv⟩ := Proofs.External.WP.exists_ok_of_spec
      (transport.common.mcp_headers.prim.base64_encode_spec value (by omega))
    have hlen : s.utf8ByteSize ≤ Usize.max := by
      rw [← length_utf8, hsv, length_b64StdPad]
      exact (Nat.le_of_not_lt h1).trans maxStringBytes_le_usize_max
    obtain ⟨e, he, hev⟩ := Proofs.External.WP.exists_ok_of_spec
      (alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec s hlen)
    rw [hs, bind_ok, he, bind_ok]
    apply transport.common.mcp_headers.prim.wrap_sentinel_fail e s hev
    rw [hev, hsv, length_b64StdPad]; exact h_len

/-- G03 for a value of at most `isize::MAX / 2` bytes (E'), which implies (E)
(`Proofs.External.Base64Std.add_two_div_three_mul_four_add_eleven_le`). -/
theorem encode_header_value_spec_of_length_le (value : Str)
    (h_len : value.val.length ≤ ExtModel.maxStringBytes / 2) :
    encode_header_value value ⦃ (result : String) =>
      utf8Bytes result = encodeHeaderValue value.val ⦄ := by
  exact encode_header_value_spec value (fun _ => add_two_div_three_mul_four_add_eleven_le h_len)

/-- **Spec theorem for `rmcp::transport::common::mcp_headers::decode_header_value`** (G04;
upstream lines 256–268, patched 250–261)

Never fails under (U) and (D). `result.map utf8Bytes = Defs.McpHeaders.decodeHeaderValue value.val`
(the bytes determine the `String`): if `value` is `=?base64?` ++ `inner` ++ `?=` (lines 258–261),
`Some` of the string whose bytes `inner` encodes in strict padded standard Base64 (line 263),
`None` if `inner` is not such an encoding (`.ok()?`, line 263) or the decoded bytes are not UTF-8
(`String::from_utf8(bytes).ok()`, line 264); otherwise `Some(value.to_owned())` (line 266).
Premises: (U) a value that is no sentinel is UTF-8 (rule (ii)(a); a sentinel needs none, its
path reads only bytes). (U) is the exact, weakest form of the UTF-8 premise:
`decode_header_value_fail_undef` shows that without it the model fails. The spec owner approved
this conditional form of the UTF-8 rule on 2026-11-27. (D)
`DecodeFits value.val` (exact, `decode_header_value_fail`). -/
@[step]
theorem decode_header_value_spec (value : Str)
    (h_utf8 : sentinelInner? value.val = none → ExtModel.IsUtf8 value.val)
    (h_fits : DecodeFits value.val) :
    decode_header_value value ⦃ (result : Option String) =>
      result.map utf8Bytes = decodeHeaderValue value.val ⦄ := by
  obtain ⟨r, hr, hv⟩ := exists_decode_header_value_eq_ok value h_utf8 h_fits
  rw [hr, WP.spec_ok]; exact hv

/-- G04 without (U): a value that is no sentinel and not UTF-8 (no Rust `&str`) reaches the
`fail undef` of the `str::to_owned` model. -/
theorem decode_header_value_fail_undef (value : Str)
    (h_sentinel : sentinelInner? value.val = none)
    (h_utf8 : ¬ ExtModel.IsUtf8 value.val) :
    decode_header_value value = fail Error.undef := by
  rw [decode_header_value_eq, h_sentinel]
  have : strOfBytes? value.val = none :=
    (strOfBytes?_eq_none_iff _).2 (fun t ht => h_utf8 ⟨t, ht⟩)
  simp only
  rw [to_owned_eq, this, bind_fail]

/-- G04 without (D): for a sentinel whose decode buffer exceeds `isize::MAX` bytes, the model of
`BASE64_STANDARD.decode` panics before reading (`vec![0; estimate]`, "capacity overflow"). No
Rust `&str` is that long (it would need more than `4/3 · isize::MAX` bytes), so this describes
the Lean model only. -/
theorem decode_header_value_fail (value : Str) (inner : List U8)
    (h_sentinel : sentinelInner? value.val = some inner)
    (h_len : ExtModel.maxStringBytes < ExtModel.b64StdDecodedLenEstimate inner.length) :
    decode_header_value value = fail Error.panic := by
  rw [decode_header_value_eq, h_sentinel]
  simp only [ite_eq_left h_len]

/-- G04 under the invariants of every Rust `&str`: UTF-8 (U*, implies (U)) and at most
`isize::MAX` bytes (D', implies (D) by
`Proofs.External.Base64Std.b64StdDecodedLenEstimate_le_of_le`, the inner text being shorter). -/
theorem decode_header_value_spec_of_isUtf8 (value : Str)
    (h_utf8 : ExtModel.IsUtf8 value.val)
    (h_len : value.val.length ≤ ExtModel.maxStringBytes) :
    decode_header_value value ⦃ (result : Option String) =>
      result.map utf8Bytes = decodeHeaderValue value.val ⦄ := by
  exact decode_header_value_spec value (fun _ => h_utf8)
    (fun _ h => b64StdDecodedLenEstimate_le_of_le
      ((length_le_of_sentinelInner?_eq_some h).trans h_len))

/-! ## Compositions -/

/-- **(a) Round trip** (G03 then G04): for the bytes of any string `v` meeting (E),
`encode_header_value` succeeds, its result is a valid `&str`, and `decode_header_value` of any
`Str` holding the result's bytes returns `Some(v)`. So no value decodes differently from how it
was encoded, and every encoded value is accepted by the decoder. About the translated
`encode_header_value` and `decode_header_value`; premises: `value` holds the bytes of `v`, and
(E). -/
theorem decode_header_value_encode_header_value (value : Str) (v : String)
    (h_value : value.val = utf8Bytes v) (h_fits : EncodeFits value.val) :
    encode_header_value value ⦃ (encoded : String) =>
      (∃ s : Str, s.val = utf8Bytes encoded) ∧
      ∀ s : Str, s.val = utf8Bytes encoded →
        decode_header_value s ⦃ (result : Option String) =>
          result = some v ⦄ ⦄ := by
  obtain ⟨e, he, hev⟩ := exists_encode_header_value_eq_ok value h_fits
  rw [he, WP.spec_ok]
  have hmax := maxStringBytes_le_usize_max
  have hlen : (utf8Bytes e).length ≤ maxStringBytes ∨ requiresBase64 value.val = false := by
    cases hr : requiresBase64 value.val
    · exact Or.inr rfl
    · left
      rw [hev, encodeHeaderValue, hr, ite_eq_left rfl, wrapSentinel]
      simp only [List.length_append, length_base64Prefix, length_base64Suffix, length_b64StdPad]
      have := h_fits hr; omega
  refine ⟨⟨Slice.from (utf8Bytes e) ?_, Slice.from_val _ _⟩, fun s hs => ?_⟩
  · rcases hlen with h | h
    · omega
    · rw [hev, encodeHeaderValue, h]; simpa using value.property
  · have hsU : IsUtf8 s.val := ⟨e, hs⟩
    have hDF : DecodeFits s.val := by
      intro inner hi
      rcases hlen with h | h
      · apply b64StdDecodedLenEstimate_le_of_le
        rw [(sentinelInner?_eq_some_iff _ _).1 hi, wrapSentinel] at hs
        have := congrArg List.length hs
        simp only [List.length_append] at this
        omega
      · rw [hs, hev, encodeHeaderValue, h] at hi
        simp only [Bool.false_eq_true, ↓reduceIte] at hi
        rw [sentinelInner?_eq_none_of_requiresBase64_eq_false _ h] at hi
        exact absurd hi (by simp)
    obtain ⟨r, hr, hrv⟩ := exists_decode_header_value_eq_ok s (fun _ => hsU) hDF
    rw [hr, WP.spec_ok]
    rw [hs, hev, decodeHeaderValue_encodeHeaderValue _ ⟨v, h_value⟩, h_value] at hrv
    cases r with
    | none => simp at hrv
    | some w =>
      simp only [Option.map_some, Option.some.injEq] at hrv
      rw [utf8Bytes_eq_utf8, utf8Bytes_eq_utf8] at hrv
      rw [utf8_injective hrv]

/-- **(b) Header safety, `0x20`–`0x7E` form**: under (E), every byte of the result of
`encode_header_value` is printable ASCII (`0x20`–`0x7E`) and the result neither starts nor ends
with SP or HTAB (`IsBareHeaderValue`); hence it is an RFC 9110 §5.5 field value
(`IsFieldValue`) with no CR, LF, NUL or other control byte: no header injection, and
`HeaderValue::from_str` in `standard_request_headers` (upstream lines 287–294) accepts it. For
every `Str`, UTF-8 or not. The second conjunct follows from the first
(`isFieldValue_of_isBareHeaderValue`); it is kept so that the statement names the RFC 9110
property. About the translated `encode_header_value`; premise (E). -/
theorem isBareHeaderValue_encode_header_value (value : Str)
    (h_fits : EncodeFits value.val) :
    encode_header_value value ⦃ (result : String) =>
      IsBareHeaderValue (utf8Bytes result) ∧ IsFieldValue (utf8Bytes result) ⦄ := by
  obtain ⟨r, hr, hv⟩ := exists_encode_header_value_eq_ok value h_fits
  rw [hr, WP.spec_ok, hv]
  have := isBareHeaderValue_encodeHeaderValue value.val
  exact ⟨this, isFieldValue_of_isBareHeaderValue _ this⟩

/-- **(b) The wrapped form**: when `requires_base64(value)` is `true`, under (E) the result of
`encode_header_value(value)` is `=?base64?` ++ the padded standard Base64 of the bytes of `value`
++ `?=` (upstream lines 244–248). About the translated `requires_base64` and
`encode_header_value`; premise (E). -/
theorem encode_header_value_eq_wrapSentinel_of_requires_base64_eq_true (value : Str)
    (h_fits : EncodeFits value.val) :
    requires_base64 value ⦃ (b : Bool) =>
      b = true →
        encode_header_value value ⦃ (result : String) =>
          utf8Bytes result = wrapSentinel (ExtModel.b64StdPad value.val) ⦄ ⦄ := by
  rw [requires_base64_eq, WP.spec_ok]
  intro hb
  obtain ⟨r, hr, hv⟩ := exists_encode_header_value_eq_ok value h_fits
  rw [hr, WP.spec_ok, hv, encodeHeaderValue_eq_wrapSentinel_of_requiresBase64_eq_true _ hb]

/-- **(b) Header safety, wrapped form**: when `requires_base64(value)` is `true`, under (E) every
byte of the result of `encode_header_value(value)` is visible ASCII `0x21`–`0x7E` (no SP, no
HTAB, no control byte, no `obs-text`). About the translated `requires_base64` and
`encode_header_value`; premise (E). -/
theorem isVisibleAscii_encode_header_value_of_requires_base64_eq_true (value : Str)
    (h_fits : EncodeFits value.val) :
    requires_base64 value ⦃ (b : Bool) =>
      b = true →
        encode_header_value value ⦃ (result : String) =>
          IsVisibleAscii (utf8Bytes result) ⦄ ⦄ := by
  rw [requires_base64_eq, WP.spec_ok]
  intro hb
  obtain ⟨r, hr, hv⟩ := exists_encode_header_value_eq_ok value h_fits
  rw [hr, WP.spec_ok, hv]
  exact isVisibleAscii_encodeHeaderValue_of_requiresBase64_eq_true _ hb

/-- **(c) Bare exactly when not required**: `encode_header_value(value)` has the bytes of `value`
exactly when `requires_base64(value)` is `false`. About the translated `requires_base64` and
`encode_header_value`; premise (E). -/
theorem encode_header_value_eq_self_iff (value : Str)
    (h_fits : EncodeFits value.val) :
    requires_base64 value ⦃ (b : Bool) =>
      encode_header_value value ⦃ (result : String) =>
        (utf8Bytes result = value.val ↔ b = false) ⦄ ⦄ := by
  rw [requires_base64_eq, WP.spec_ok]
  obtain ⟨r, hr, hv⟩ := exists_encode_header_value_eq_ok value h_fits
  rw [hr, WP.spec_ok, hv]
  exact encodeHeaderValue_eq_self_iff _

/-- **(d) The token characters, listed**: `is_tchar(c)` is `true` exactly for the 77 characters
of `Defs.McpHeaders.tchars` (77 distinct chars: `length_tchars`, `nodup_tchars`; the RFC 9110
§5.6.2 `tchar` list, upstream lines 81–100). About the translated `is_tchar`; no premise. -/
theorem is_tchar_eq_true_iff_mem_tchars (c : Char) :
    is_tchar c ⦃ (result : Bool) =>
      (result = true ↔ c ∈ tchars) ⦄ := by
  rw [is_tchar_eq, WP.spec_ok]
  exact isTchar_eq_true_iff_mem_tchars c

/-- **(d) The token characters, RFC 9110 prose**: `is_tchar(c)` is `true` exactly for the visible
ASCII characters (`0x21`–`0x7E`) other than the 17 RFC 9110 delimiters (§5.6.2, "any VCHAR,
except delimiters"); no non-ASCII character, no control, no SP. About the translated
`is_tchar`; no premise. -/
theorem is_tchar_eq_true_iff_isVchar_and_not_isDelimiter (c : Char) :
    is_tchar c ⦃ (result : Bool) =>
      (result = true ↔ isVchar c = true ∧ isDelimiter c = false) ⦄ := by
  rw [is_tchar_eq, WP.spec_ok]
  exact isTchar_eq_true_iff_isVchar_and_not_isDelimiter c

/-- **(e) What the decoder accepts**: under (U) and (D), `decode_header_value(value)` is
`Some(v)` exactly when `value` is no sentinel and holds the bytes of `v` (returned unchanged), or
`value` is `=?base64?` ++ the canonical padded standard Base64 encoding of the UTF-8 bytes of `v`
++ `?=`. (A sentinel is `=?base64?` ++ `inner` ++ `?=` with the two not overlapping.) About the
translated `decode_header_value`; premises (U), (D). -/
theorem decode_header_value_eq_some_iff (value : Str)
    (h_utf8 : sentinelInner? value.val = none → ExtModel.IsUtf8 value.val)
    (h_fits : DecodeFits value.val) :
    decode_header_value value ⦃ (result : Option String) =>
      ∀ v : String, result = some v ↔
        (sentinelInner? value.val = none ∧ utf8Bytes v = value.val) ∨
          value.val = wrapSentinel (ExtModel.b64StdPad (utf8Bytes v)) ⦄ := by
  obtain ⟨r, hr, hv⟩ := exists_decode_header_value_eq_ok value h_utf8 h_fits
  rw [hr, WP.spec_ok]
  intro v
  have key : r = some v ↔ decodeHeaderValue value.val = some (utf8Bytes v) := by
    rw [← hv]
    constructor
    · rintro rfl; rfl
    · intro h
      rcases r with _ | w
      · simp at h
      · simp only [Option.map_some, Option.some.injEq] at h
        rw [utf8_injective h]
  rw [key, decodeHeaderValue_eq_some_iff]
  have hu : ExtModel.IsUtf8 (utf8Bytes v) := ⟨v, rfl⟩
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, _⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr h1
  · rintro (⟨h1, h2⟩ | h1)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, hu⟩

/-- **(e) What the decoder rejects**: under (U) and (D), `decode_header_value(value)` is `None`
exactly when `value` is a sentinel `=?base64?` ++ `inner` ++ `?=` and `inner` is the padded
standard Base64 encoding of no string's UTF-8 bytes. About the translated `decode_header_value`;
premises (U), (D). -/
theorem decode_header_value_eq_none_iff (value : Str)
    (h_utf8 : sentinelInner? value.val = none → ExtModel.IsUtf8 value.val)
    (h_fits : DecodeFits value.val) :
    decode_header_value value ⦃ (result : Option String) =>
      (result = none ↔
        ∃ inner, value.val = wrapSentinel inner ∧
          ∀ v : String, ExtModel.b64StdPad (utf8Bytes v) ≠ inner) ⦄ := by
  obtain ⟨r, hr, hv⟩ := exists_decode_header_value_eq_ok value h_utf8 h_fits
  rw [hr, WP.spec_ok]
  have key : r = none ↔ decodeHeaderValue value.val = none := by
    rw [← hv]; simp
  rw [key, decodeHeaderValue_eq_none_iff]
  constructor
  · rintro ⟨inner, h1, h2⟩
    exact ⟨inner, h1, fun v => h2 _ ⟨v, rfl⟩⟩
  · rintro ⟨inner, h1, h2⟩
    exact ⟨inner, h1, fun y ⟨t, ht⟩ => ht ▸ h2 t⟩

end rmcp.transport.common.mcp_headers
