/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Defs.Skill
public import Proofs.External.Skill
public import Proofs.External.Std
public import Proofs.External.Iter
public import Proofs.Model.Skill.Common

@[expose] public section

/-!
# Helper specs for `Skill::validate` and `validate_skills` (K13, K16)

Facts about the definitions of `Defs.Skill` and the trusted models, and one spec theorem per
private helper of `crates/rmcp/src/model/skill.rs` (patched copy, translation patch 04) that
`validate` and `validate_skills` call, each stated as equal to its `Defs.Skill` counterpart:
`is_unreserved` (`isUnreserved`), `is_ascii_hex` (`isHexDigit` on every byte),
`push_normalized_part` (`normalizePart`), `normalize_percent_encoding` (`normalizePercent`),
`resolve_segments` (`removeDotSegments`), `manifest_resource_key` (`manifestKey`) and
`is_valid_skill_name` (`isSkillName`).

Source: "crates/rmcp/src/model/skill.rs", lines 354–478 in the patched copy (patches 01–04 on
origin/main 7caec76).
-/

open Aeneas Aeneas.Std Result
open rmcp

namespace Proofs.Model.Skill

open ExtModel Proofs.External.Byte Proofs.External.Utf8 Proofs.External.Skill
open Defs.Skill

/-! ## Bytes -/

/-- `encodeControls` of `Defs.Skill` is the trusted model `percentEncodeControls`. -/
theorem encodeControls_eq_percentEncodeControls :
    ∀ l : List U8, encodeControls l = percentEncodeControls l
  | [] => rfl
  | b :: rest => by
    rw [encodeControls, List.flatMap_cons, percentEncodeControls, ← encodeControls,
      encodeControls_eq_percentEncodeControls rest]
    have : needsEncoding b = isControlOrNonAscii b := rfl
    rw [this]
    split <;> rfl

theorem isHexDigit_iff (b : U8) : isHexDigit b = true ↔
    (48 ≤ b.val ∧ b.val ≤ 57) ∨ (65 ≤ b.val ∧ b.val ≤ 70) ∨ (97 ≤ b.val ∧ b.val ≤ 102) := by
  simp only [isHexDigit, Defs.IntParse.isAsciiDigit, Bool.or_eq_true, decide_eq_true_eq,
    Bool.and_eq_true]
  omega

/-- The value of a hexadecimal digit as the model reads it. -/
theorem hexDigitValue?_eq (b : U8) :
    hexDigitValue? b = if isHexDigit b then some (hexValue b) else none := by
  have hiff := isHexDigit_iff b
  rw [hexDigitValue?, digitValue?, hexValue]
  by_cases h1 : 48 ≤ b.val ∧ b.val ≤ 57
  · rw [ite_eq_left h1, ite_eq_left (show b.val - 48 < 16 by omega),
      ite_eq_left (hiff.2 (Or.inl h1)), ite_eq_left (show b.val ≤ 57 by omega)]
  · rw [ite_eq_right h1]
    by_cases h2 : 10 < 16 ∧ 65 ≤ b.val ∧ b.val ≤ 90
    · rw [ite_eq_left h2]
      by_cases h3 : b.val ≤ 70
      · rw [ite_eq_left (show b.val - 55 < 16 by omega),
          ite_eq_left (hiff.2 (Or.inr (Or.inl ⟨by omega, h3⟩))),
          ite_eq_right (show ¬ b.val ≤ 57 by omega), ite_eq_left h3]
      · rw [ite_eq_right (show ¬ b.val - 55 < 16 by omega),
          ite_eq_right (show ¬ isHexDigit b = true from fun h => by have := hiff.1 h; omega)]
    · rw [ite_eq_right h2]
      by_cases h3 : 10 < 16 ∧ 97 ≤ b.val ∧ b.val ≤ 122
      · rw [ite_eq_left h3]
        by_cases h4 : b.val ≤ 102
        · rw [ite_eq_left (show b.val - 87 < 16 by omega),
            ite_eq_left (hiff.2 (Or.inr (Or.inr ⟨by omega, h4⟩))),
            ite_eq_right (show ¬ b.val ≤ 57 by omega), ite_eq_right (show ¬ b.val ≤ 70 by omega)]
        · rw [ite_eq_right (show ¬ b.val - 87 < 16 by omega),
            ite_eq_right (show ¬ isHexDigit b = true from fun h => by have := hiff.1 h; omega)]
      · rw [ite_eq_right h3,
          ite_eq_right (show ¬ isHexDigit b = true from fun h => by have := hiff.1 h; omega)]

theorem val_lt_128_of_isHexDigit {b : U8} (h : isHexDigit b = true) : b.val < 128 := by
  rw [isHexDigit_iff] at h; omega

theorem hexValue_lt {b : U8} (h : isHexDigit b = true) : hexValue b < 16 := by
  rw [isHexDigit_iff] at h
  unfold hexValue
  split_ifs <;> omega

theorem isUnreserved_iff (b : U8) : isUnreserved b = true ↔
    (48 ≤ b.val ∧ b.val ≤ 57) ∨ (65 ≤ b.val ∧ b.val ≤ 90) ∨ (97 ≤ b.val ∧ b.val ≤ 122) ∨
      b.val = 45 ∨ b.val = 46 ∨ b.val = 95 ∨ b.val = 126 := by
  have e45 : asciiByte '-' = byte 45 := rfl
  have e46 : asciiByte '.' = byte 46 := rfl
  have e95 : asciiByte '_' = byte 95 := rfl
  have e126 : asciiByte '~' = byte 126 := rfl
  simp only [isUnreserved, Defs.IntParse.isAsciiDigit, Bool.or_eq_true, decide_eq_true_eq,
    Bool.and_eq_true, beq_iff_eq, e45, e46, e95, e126, eq_byte_iff b _ (by decide : 45 < 256),
    eq_byte_iff b _ (by decide : 46 < 256), eq_byte_iff b _ (by decide : 95 < 256),
    eq_byte_iff b _ (by decide : 126 < 256)]
  omega

theorem val_lt_128_of_isUnreserved {b : U8} (h : isUnreserved b = true) : b.val < 128 := by
  rw [isUnreserved_iff] at h; omega

/-- `upperHexDigit` of `Defs.Skill` is the model's. -/
theorem upperHexDigit_eq (n : Nat) : Defs.Skill.upperHexDigit n = ExtModel.upperHexDigit n := rfl

/-- The byte of the uppercase hexadecimal digit `n < 16`: `48 + n` for `0`–`9`, `55 + n` for
`10`–`15`. -/
theorem val_upperHexDigit {n : Nat} (h : n < 16) :
    (ExtModel.upperHexDigit n).val = if n < 10 then 48 + n else 55 + n := by
  unfold ExtModel.upperHexDigit
  by_cases hn : n < 10
  · rw [ite_eq_left hn, ite_eq_left hn, byte_val, Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right hn, ite_eq_right hn, byte_val, Nat.mod_eq_of_lt (by omega)]

theorem val_upperHexDigit_lt {n : Nat} (h : n < 16) : (Defs.Skill.upperHexDigit n).val < 128 := by
  rw [upperHexDigit_eq, val_upperHexDigit h]
  split <;> omega

/-- No uppercase hexadecimal digit is the byte `k` of `/` (47) or `%` (37). -/
theorem upperHexDigit_ne_of_lt_48 {n k : Nat} (h : n < 16) (hk : k < 48) :
    ExtModel.upperHexDigit n ≠ byte k := by
  intro he
  have := congrArg UScalar.val he
  rw [val_upperHexDigit h, byte_val] at this
  split at this <;> omega

theorem upperHexDigit_ne_slash {n : Nat} (h : n < 16) :
    Defs.Skill.upperHexDigit n ≠ byte 47 :=
  upperHexDigit_ne_of_lt_48 h (by decide)

theorem val_hexByte {h l : U8} (hh : isHexDigit h = true) (hl : isHexDigit l = true) :
    (hexByte h l).val = 16 * hexValue h + hexValue l := by
  have := hexValue_lt hh; have := hexValue_lt hl
  show (byte _).val = _
  rw [byte_val]; omega

/-- On a hexadecimal digit, the ASCII uppercase is the uppercase digit of its value. -/
theorem asciiUppercase_eq_upperHexDigit {b : U8} (h : isHexDigit b = true) :
    asciiUppercase b = Defs.Skill.upperHexDigit (hexValue b) := by
  have hb := (isHexDigit_iff b).1 h
  apply UScalar.eq_of_val_eq
  unfold asciiUppercase Defs.Skill.upperHexDigit hexValue
  simp only [byteOf_eq]
  split_ifs <;> simp only [byte_val] <;> omega

/-! ## Splitting at a byte -/

theorem splitBytes_ne_nil (sep : U8) : ∀ l : List U8, splitBytes sep l ≠ []
  | [] => by simp only [splitBytes, ne_eq, List.cons_ne_self, not_false_eq_true]
  | b :: rest => by
    rw [splitBytes]
    split
    · simp only [ne_eq, reduceCtorEq, not_false_eq_true]
    · split <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.cons_ne_self]

/-- The model's split is `List.splitOn`. -/
theorem splitBytes_eq_splitOn (sep : U8) : ∀ l : List U8, splitBytes sep l = l.splitOn sep
  | [] => by rw [List.splitOn_eq_splitOnP, List.splitOnP_nil]; rfl
  | b :: rest => by
    rw [List.splitOn_eq_splitOnP, List.splitOnP_cons_eq_ite_modifyHead, ← List.splitOn_eq_splitOnP,
      ← splitBytes_eq_splitOn sep rest, splitBytes]
    by_cases hb : b = sep
    · rw [ite_eq_left hb, ite_eq_left (by simp only [hb, BEq.rfl])]
    · rw [ite_eq_right hb, ite_eq_right (by simp only [beq_iff_eq, hb, not_false_eq_true])]
      have := splitBytes_ne_nil sep rest
      split
      · rename_i p ps h; rw [h]; rfl
      · contradiction

/-- The parts of the split, with one separator each but the last, make up the list. -/
theorem sum_length_splitBytes (sep : U8) : ∀ l : List U8,
    ((splitBytes sep l).map List.length).sum + (splitBytes sep l).length = l.length + 1
  | [] => by simp only [splitBytes, List.map_cons, List.length_nil, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, List.length_cons, zero_add]
  | b :: rest => by
    have ih := sum_length_splitBytes sep rest
    rw [splitBytes]
    split
    · simp only [List.map_cons, List.length_nil, List.sum_cons, List.length_cons]; omega
    · split
      · rename_i p ps h
        rw [h] at ih
        simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega
      · rename_i h; exact absurd h (splitBytes_ne_nil sep rest)

/-- The split at the first separator. -/
theorem splitBytes_of_findIdx?_eq_some (sep : U8) : ∀ (l : List U8) (i : Nat),
    l.findIdx? (fun b => decide (b = sep)) = some i →
    splitBytes sep l = l.take i :: splitBytes sep (l.drop (i + 1))
  | [], i, h => by simp only [List.findIdx?_nil, reduceCtorEq] at h
  | b :: rest, i, h => by
    rw [List.findIdx?_cons] at h
    by_cases hb : b = sep
    · rw [ite_eq_left (by simp only [hb, decide_true])] at h
      cases h
      rw [splitBytes, ite_eq_left hb]; rfl
    · rw [ite_eq_right (by simp only [hb, decide_false, Bool.false_eq_true,
        not_false_eq_true])] at h
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 h
      have ih := splitBytes_of_findIdx?_eq_some sep rest j hj
      rw [splitBytes, ite_eq_right hb, ih]
      rfl

theorem splitBytes_of_findIdx?_eq_none (sep : U8) : ∀ (l : List U8),
    l.findIdx? (fun b => decide (b = sep)) = none → splitBytes sep l = [l]
  | [], _ => rfl
  | b :: rest, h => by
    rw [List.findIdx?_cons] at h
    by_cases hb : b = sep
    · rw [ite_eq_left (by simp only [hb, decide_true])] at h; cases h
    · rw [ite_eq_right (by simp only [hb, decide_false, Bool.false_eq_true,
        not_false_eq_true]), Option.map_eq_none_iff] at h
      rw [splitBytes, ite_eq_right hb, splitBytes_of_findIdx?_eq_none sep rest h]

/-! ## Percent-decoding -/

/-- The model `percentDecodeFrom` with no `%` pending, and after a `%`, in terms of the parts
between the `%` bytes. -/
theorem percentDecodeFrom_eq : ∀ l : List U8,
    percentDecodeFrom none l =
        (match splitBytes (byte 37) l with
          | [] => []
          | first :: parts => first ++ parts.flatMap decodePart) ∧
      percentDecodeFrom (some none) l = (splitBytes (byte 37) l).flatMap decodePart
  | [] => ⟨rfl, rfl⟩
  | c :: rest => by
    have ih := percentDecodeFrom_eq rest
    have hpart : ∀ (p : List U8) (ps : List (List U8)), splitBytes (byte 37) rest = p :: ps →
        percentDecodeFrom none rest = p ++ ps.flatMap decodePart := by
      intro p ps h; rw [ih.1, h]
    obtain ⟨p, ps, hps⟩ := List.exists_cons_of_ne_nil (splitBytes_ne_nil (byte 37) rest)
    have hD := hpart p ps hps
    have hE := ih.2
    rw [hps] at hE
    by_cases hc : c = byte 37
    · have hc' : c.val = 37 := (eq_byte_iff c 37 (by decide)).1 hc
      refine ⟨?_, ?_⟩
      · rw [percentDecodeFrom, ite_eq_left hc', hE, splitBytes, ite_eq_left hc, hps]
        rfl
      · have hnone : hexDigitValue? c = none := by
          rw [hexDigitValue?_eq, ite_eq_right]; rw [isHexDigit_iff]; omega
        rw [percentDecodeFrom, hnone]
        simp only
        rw [ite_eq_left hc', hE, splitBytes, ite_eq_left hc, hps]
        rfl
    · have hc' : c.val ≠ 37 := fun h => hc ((eq_byte_iff c 37 (by decide)).2 h)
      have hsplit : splitBytes (byte 37) (c :: rest) = (c :: p) :: ps := by
        rw [splitBytes, ite_eq_right hc, hps]
      refine ⟨?_, ?_⟩
      · rw [percentDecodeFrom, ite_eq_right hc', hsplit, hD]
        rfl
      · rw [hsplit]
        cases hhc : isHexDigit c
        · have hnone : hexDigitValue? c = none := by rw [hexDigitValue?_eq, hhc]; rfl
          rw [percentDecodeFrom, hnone]
          simp only
          rw [ite_eq_right hc', hD, List.flatMap_cons]
          have : decodePart (c :: p) = asciiByte '%' :: c :: p := by
            unfold decodePart
            split
            · rename_i h l r heq
              cases heq
              rw [hhc]; rfl
            · rfl
          rw [this]; rfl
        · have hsome : hexDigitValue? c = some (hexValue c) := by
            rw [hexDigitValue?_eq, hhc]; rfl
          rw [percentDecodeFrom, hsome]
          simp only
          -- now look at the next byte
          cases rest with
          | nil =>
            simp only [splitBytes] at hps
            cases hps
            rfl
          | cons d rest2 =>
            have ih2 := percentDecodeFrom_eq rest2
            obtain ⟨q, qs, hqs⟩ :=
              List.exists_cons_of_ne_nil (splitBytes_ne_nil (byte 37) rest2)
            have hD2 : percentDecodeFrom none rest2 = q ++ qs.flatMap decodePart := by
              rw [ih2.1, hqs]
            rw [percentDecodeFrom, hsome]
            by_cases hd : d = byte 37
            · have hd' : d.val = 37 := (eq_byte_iff d 37 (by decide)).1 hd
              have hdn : hexDigitValue? d = none := by
                rw [hexDigitValue?_eq, ite_eq_right]; rw [isHexDigit_iff]; omega
              rw [hdn]
              rw [ite_eq_left hd']
              rw [splitBytes, ite_eq_left hd] at hps
              cases hps
              rw [ih2.2, List.flatMap_cons]
              rfl
            · have hd' : d.val ≠ 37 := fun h => hd ((eq_byte_iff d 37 (by decide)).2 h)
              rw [splitBytes, ite_eq_right hd, hqs] at hps
              cases hps
              rw [List.flatMap_cons]
              cases hhd : isHexDigit d
              · have hdn : hexDigitValue? d = none := by rw [hexDigitValue?_eq, hhd]; rfl
                rw [hdn]
                rw [ite_eq_right hd', hD2]
                simp only [decodePart, hhc, hhd, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
                rfl
              · have hds : hexDigitValue? d = some (hexValue d) := by
                  rw [hexDigitValue?_eq, hhd]; rfl
                rw [hds]
                rw [hD2]
                simp only [decodePart, hhc, hhd, Bool.and_self, ↓reduceIte]
                rfl

/-- **Percent-decoding**: the model of `percent_decode_str` is `decodePercent`. -/
theorem percentDecode_eq_decodePercent (l : List U8) : percentDecode l = decodePercent l := by
  rw [percentDecode, (percentDecodeFrom_eq l).1, decodePercent, ← asciiByte_percent,
    splitBytes_eq_splitOn]
  cases List.splitOn (asciiByte '%') l <;> rfl

/-! ## One part of the percent-normalisation -/

theorem two_le_length_of_isCharBoundary {l : List U8} (h : isCharBoundary l 2 = true) :
    2 ≤ l.length := by
  unfold isCharBoundary at h
  rw [ite_eq_right (by omega)] at h
  by_contra hlt
  rw [ite_eq_left (by omega)] at h
  simp only [decide_eq_true_eq] at h
  omega

theorem isCharBoundary_two_of_isHexDigit {t : String} {h l : U8} {r : List U8}
    (ht : utf8 t = h :: l :: r) (hl : isHexDigit l = true) : isCharBoundary (utf8 t) 2 = true := by
  have h1 : 1 < (utf8 t).length := by rw [ht]; simp only [List.length_cons, lt_add_iff_pos_left,
      Order.lt_add_one_iff, zero_le]
  apply isCharBoundary_add_one_of_val_lt h1
  have : (utf8 t)[1] = l := by simp only [ht, List.getElem_cons_succ, List.getElem_cons_zero]
  rw [this]; exact val_lt_128_of_isHexDigit hl

theorem normalizePart_of_not_hex (part : List U8)
    (h : ∀ a b r, part = a :: b :: r → ¬ (isHexDigit a = true ∧ isHexDigit b = true)) :
    normalizePart part = asciiByte '%' :: part := by
  unfold normalizePart
  split
  · rename_i a b r
    rw [ite_eq_right]
    intro hab
    rw [Bool.and_eq_true] at hab
    exact h a b r rfl hab
  · rfl

theorem u8FromAscii_hex {h l : U8} (hh : isHexDigit h = true) (hl : isHexDigit l = true) :
    u8FromAscii 16 [h, l] = .ok (16 * hexValue h + hexValue l) := by
  have h43 : h.val ≠ 43 := by have := (isHexDigit_iff h).1 hh; omega
  have hvh := hexValue_lt hh
  have hvl := hexValue_lt hl
  have dh : digitValue? 16 h = some (hexValue h) := by
    have := hexDigitValue?_eq h; rw [hh] at this; exact this
  have dl : digitValue? 16 l = some (hexValue l) := by
    have := hexDigitValue?_eq l; rw [hl] at this; exact this
  simp only [u8FromAscii, ite_eq_right h43, u8DigitLoop, dh, dl]
  rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  congr 1
  omega

/-! ## Sizes and ASCII facts of the percent-normalisation -/

theorem length_splitBytes (sep : U8) : ∀ l : List U8,
    (splitBytes sep l).length = l.count sep + 1
  | [] => rfl
  | b :: rest => by
    have ih := length_splitBytes sep rest
    rw [splitBytes, List.count_cons]
    split
    · rename_i hb; simp only [List.length_cons, ih, hb, beq_self_eq_true, ↓reduceIte]
    · rename_i hb
      have hne : (b == sep) = false := by simp only [beq_eq_false_iff_ne, ne_eq, hb,
          not_false_eq_true]
      split
      · rename_i p ps h
        rw [h, List.length_cons] at ih
        rw [List.length_cons, hne, ite_eq_right Bool.false_ne_true]
        omega
      · rename_i h; exact absurd h (splitBytes_ne_nil sep rest)

theorem mem_of_mem_splitBytes (sep : U8) : ∀ (l : List U8), ∀ p ∈ splitBytes sep l, ∀ b ∈ p, b ∈ l
  | [], p, hp, b, hb => by
    rw [splitBytes, List.mem_singleton] at hp
    subst hp
    exact absurd hb List.not_mem_nil
  | c :: rest, p, hp, b, hb => by
    rw [splitBytes] at hp
    split at hp
    · rcases List.mem_cons.1 hp with rfl | hp
      · simp only [List.not_mem_nil] at hb
      · exact List.mem_cons_of_mem _ (mem_of_mem_splitBytes sep rest p hp b hb)
    · split at hp
      · rename_i q qs h
        rcases List.mem_cons.1 hp with rfl | hp
        · rcases List.mem_cons.1 hb with rfl | hb
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _
              (mem_of_mem_splitBytes sep rest q (by rw [h]; exact List.mem_cons_self) b hb)
        · exact List.mem_cons_of_mem _
            (mem_of_mem_splitBytes sep rest p (by rw [h]; exact List.mem_cons_of_mem _ hp) b hb)
      · rename_i h; exact absurd h (splitBytes_ne_nil sep rest)

theorem length_percentEncodeControls_le : ∀ l : List U8,
    (percentEncodeControls l).length ≤ 3 * l.length
  | [] => le_refl _
  | b :: rest => by
    have := length_percentEncodeControls_le rest
    rw [percentEncodeControls]
    split
    · simp only [percentEncodeByte, List.length_append, List.length_cons, List.length_nil]; omega
    · simp only [List.length_cons]; omega

theorem count_percentEncodeControls_le : ∀ l : List U8,
    (percentEncodeControls l).count (byte 37) ≤ l.length
  | [] => le_refl _
  | b :: rest => by
    have := count_percentEncodeControls_le rest
    rw [percentEncodeControls]
    split
    · have h1 : ExtModel.upperHexDigit (b.val / 16) ≠ byte 37 :=
        upperHexDigit_ne_of_lt_48 (by have := val_lt b; omega) (by decide)
      have h2 : ExtModel.upperHexDigit (b.val % 16) ≠ byte 37 :=
        upperHexDigit_ne_of_lt_48 (Nat.mod_lt _ (by decide)) (by decide)
      simp only [percentEncodeByte, List.cons_append, List.count_cons, List.nil_append,
        beq_iff_eq, h1, h2, ↓reduceIte, beq_self_eq_true, List.length_cons]
      omega
    · rw [List.count_cons, List.length_cons]; split <;> omega

theorem length_normalizePart_le (p : List U8) : (normalizePart p).length ≤ p.length + 1 := by
  unfold normalizePart
  split
  · split
    · split <;> simp only [List.cons_append, List.nil_append, List.length_cons,
        add_le_add_iff_right, le_add_iff_nonneg_right, zero_le, ↓Char.isValue, Std.le_refl]
    · simp only [↓Char.isValue, List.length_cons, Std.le_refl]
  · simp only [↓Char.isValue, List.length_cons, Std.le_refl]

theorem val_lt_128_of_mem_normalizePart {p : List U8} (hp : ∀ b ∈ p, b.val < 128) :
    ∀ b ∈ normalizePart p, b.val < 128 := by
  have hpct : (asciiByte '%').val < 128 := by decide
  unfold normalizePart
  split
  · rename_i h l r
    split
    · rename_i hhl
      rw [Bool.and_eq_true] at hhl
      intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · split at hb
        · rename_i hu; rw [List.mem_singleton] at hb; subst hb
          exact val_lt_128_of_isUnreserved hu
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl | rfl
          · exact hpct
          · exact val_upperHexDigit_lt (hexValue_lt hhl.1)
          · exact val_upperHexDigit_lt (hexValue_lt hhl.2)
      · exact hp b (by simp only [List.mem_cons, hb, or_true])
    · intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact hpct
      · exact hp b hb
  · intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hpct
    · exact hp b hb

theorem val_lt_128_of_mem_normalizePercent (l : List U8) :
    ∀ b ∈ normalizePercent l, b.val < 128 := by
  have hasc : ∀ b ∈ encodeControls l, b.val < 128 := by
    rw [encodeControls_eq_percentEncodeControls]; exact val_lt_128_of_mem_percentEncodeControls l
  unfold normalizePercent
  rw [← splitBytes_eq_splitOn]
  have hparts := mem_of_mem_splitBytes (asciiByte '%') (encodeControls l)
  split
  · simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  · rename_i first parts h
    intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact hasc b (hparts first (by rw [h]; exact List.mem_cons_self) b hb)
    · obtain ⟨p, hp, hbp⟩ := List.mem_flatMap.1 hb
      exact val_lt_128_of_mem_normalizePart
        (fun c hc => hasc c (hparts p (by rw [h]; exact List.mem_cons_of_mem _ hp) c hc)) b hbp

theorem length_normalizePercent_le (l : List U8) :
    (normalizePercent l).length ≤ 3 * l.length := by
  have h3 := length_percentEncodeControls_le l
  rw [← encodeControls_eq_percentEncodeControls] at h3
  have hsum := sum_length_splitBytes (asciiByte '%') (encodeControls l)
  unfold normalizePercent
  rw [← splitBytes_eq_splitOn]
  split
  · simp only [List.length_nil, zero_le]
  · rename_i first parts h
    rw [h] at hsum
    have hfl : (parts.flatMap normalizePart).length ≤
        (parts.map List.length).sum + parts.length := by
      clear h hsum
      induction parts with
      | nil => simp only [List.flatMap_nil, List.length_nil, List.map_nil, List.sum_nil, add_zero,
          Std.le_refl]
      | cons q qs ih =>
        simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons,
          List.length_cons]
        have := length_normalizePart_le q
        omega
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    rw [List.length_append]
    omega

/-- Bytes below 128 are the UTF-8 bytes of a string. -/
theorem exists_eq_utf8_of_ascii {l : List U8} (h : ∀ b ∈ l, b.val < 128) : ∃ t, l = utf8 t :=
  ⟨_, (utf8_ofList_ascii l h).symm⟩

/-! ## Manifest keys -/

/-- The sum of the counts of `c` over the parts of a split at another byte is its count. -/
theorem sum_count_splitBytes {sep c : U8} (hc : c ≠ sep) : ∀ l : List U8,
    ((splitBytes sep l).map (List.count c)).sum = l.count c
  | [] => by simp only [splitBytes, List.map_cons, List.count_nil, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
  | b :: rest => by
    have ih := sum_count_splitBytes hc rest
    rw [splitBytes, List.count_cons]
    split
    · rename_i hb
      have : (b == c) = false := by
        rw [hb]
        exact beq_eq_false_iff_ne.2 (Ne.symm hc)
      simp only [List.map_cons, List.count_nil, List.sum_cons, ih, this, zero_add,
        Bool.false_eq_true, ↓reduceIte, add_zero]
    · split
      · rename_i p ps h
        rw [h] at ih
        simp only [List.map_cons, List.sum_cons, List.count_cons] at ih ⊢
        omega
      · rename_i h; exact absurd h (splitBytes_ne_nil sep rest)

theorem count_slash_normalizePart_le (p : List U8) :
    (normalizePart p).count (byte 47) ≤ p.count (byte 47) + 0 := by
  have hpct : (asciiByte '%' == byte 47) = false := by decide
  unfold normalizePart
  split
  · rename_i h l r
    split
    · rename_i hhl
      rw [Bool.and_eq_true] at hhl
      have hh : (h == byte 47) = false := by
        have := (isHexDigit_iff h).1 hhl.1
        simp only [beq_eq_false_iff_ne, ne_eq, eq_byte_iff h 47 (by decide)]; omega
      have hl : (l == byte 47) = false := by
        have := (isHexDigit_iff l).1 hhl.2
        simp only [beq_eq_false_iff_ne, ne_eq, eq_byte_iff l 47 (by decide)]; omega
      rw [List.count_append, List.count_cons, List.count_cons, hh, hl]
      split
      · rename_i hu
        have : (hexByte h l == byte 47) = false := by
          have := (isUnreserved_iff (hexByte h l)).1 hu
          simp only [beq_eq_false_iff_ne, ne_eq, eq_byte_iff _ 47 (by decide)]; omega
        simp only [List.count_singleton, this, Bool.false_eq_true, ↓reduceIte, zero_add, add_zero,
          Std.le_refl]
      · have h1 : (Defs.Skill.upperHexDigit (hexValue h) == byte 47) = false := by
          simp only [beq_eq_false_iff_ne]; exact upperHexDigit_ne_slash (hexValue_lt hhl.1)
        have h2 : (Defs.Skill.upperHexDigit (hexValue l) == byte 47) = false := by
          simp only [beq_eq_false_iff_ne]; exact upperHexDigit_ne_slash (hexValue_lt hhl.2)
        simp only [List.count_cons, List.count_nil, hpct, h1, h2, Bool.false_eq_true, ↓reduceIte,
          add_zero, zero_add, Std.le_refl]
    · rw [List.count_cons, hpct]; simp only [Bool.false_eq_true, ↓reduceIte, add_zero, Std.le_refl]
  · rw [List.count_cons, hpct]; simp only [Bool.false_eq_true, ↓reduceIte, add_zero, Std.le_refl]

theorem count_slash_percentEncodeControls_le : ∀ l : List U8,
    (percentEncodeControls l).count (byte 47) ≤ l.length
  | [] => le_refl _
  | b :: rest => by
    have := count_slash_percentEncodeControls_le rest
    rw [percentEncodeControls]
    split
    · rw [List.count_append, List.length_cons]
      have : (percentEncodeByte b).count (byte 47) ≤ 1 := by
        have h1 : ExtModel.upperHexDigit (b.val / 16) ≠ byte 47 :=
          upperHexDigit_ne_of_lt_48 (by have := val_lt b; omega) (by decide)
        have h2 : ExtModel.upperHexDigit (b.val % 16) ≠ byte 47 :=
          upperHexDigit_ne_of_lt_48 (Nat.mod_lt _ (by decide)) (by decide)
        simp only [percentEncodeByte, List.count_cons, List.count_nil, beq_iff_eq, h1, h2,
          ↓reduceIte]
        split <;> omega
      omega
    · rw [List.count_cons, List.length_cons]; split <;> omega

/-- The percent-normalisation adds no `/` (a `%2F` stays encoded). -/
theorem count_slash_normalizePercent_le (l : List U8) :
    (normalizePercent l).count (byte 47) ≤ l.length := by
  have henc := count_slash_percentEncodeControls_le l
  rw [← encodeControls_eq_percentEncodeControls] at henc
  have hsum := sum_count_splitBytes (c := byte 47) (sep := byte 37) (by decide) (encodeControls l)
  unfold normalizePercent
  rw [← splitBytes_eq_splitOn, asciiByte_percent]
  split
  · simp only [List.count_nil, zero_le]
  · rename_i first parts h
    rw [h] at hsum
    rw [List.count_append, List.count_flatMap]
    have : (parts.map (List.count (byte 47) ∘ normalizePart)).sum ≤
        (parts.map (List.count (byte 47))).sum := by
      clear h hsum
      induction parts with
      | nil => simp only [List.map_nil, List.sum_nil, Std.le_refl]
      | cons q qs ih =>
        simp only [List.map_cons, List.sum_cons, Function.comp_apply]
        have := count_slash_normalizePart_le q
        omega
    simp only [List.map_cons, List.sum_cons] at hsum
    omega

/-- Dot-segment removal keeps a sublist of the segments. -/
theorem sublist_of_foldl_eq_some : ∀ (rest pre d : List (List U8)) (dirs : List (List U8)),
    d.Sublist pre →
    rest.foldl (fun acc segment => acc.bind fun dirs =>
      if segment = Defs.utf8Bytes "." then some dirs
      else if segment = Defs.utf8Bytes ".." then (if dirs = [] then none else some dirs.dropLast)
      else some (dirs ++ [segment])) (some d) = some dirs →
    dirs.Sublist (pre ++ rest)
  | [], pre, d, dirs, hd, h => by
    rw [List.foldl_nil, Option.some.injEq] at h
    subst h
    rw [List.append_nil]
    exact hd
  | seg :: rest, pre, d, dirs, hd, h => by
    rw [List.foldl_cons, Option.bind_some] at h
    have : pre ++ seg :: rest = (pre ++ [seg]) ++ rest := by simp only [List.append_assoc,
        List.cons_append, List.nil_append]
    rw [this]
    split at h
    · exact sublist_of_foldl_eq_some rest _ d dirs (hd.trans (List.sublist_append_left _ _)) h
    · split at h
      · split at h
        · exfalso
          clear hd this
          induction rest with
          | nil => simp only [List.foldl_nil, reduceCtorEq] at h
          | cons x xs ih => exact ih (by simpa only [List.foldl_cons, Option.bind_none] using h)
        · exact sublist_of_foldl_eq_some rest _ _ dirs
            ((List.dropLast_sublist d).trans (hd.trans (List.sublist_append_left _ _))) h
      · exact sublist_of_foldl_eq_some rest _ _ dirs
          (List.Sublist.append hd (List.Sublist.refl _)) h

theorem sublist_of_removeDotSegments_eq_some {segs dirs : List (List U8)}
    (h : removeDotSegments segs = some dirs) : dirs.Sublist segs := by
  have := sublist_of_foldl_eq_some segs [] [] dirs (List.Sublist.refl _) h
  simpa only [List.nil_append] using this

/-- The length of a list joined with a one-element separator. -/
theorem length_intercalate_singleton (sep : U8) : ∀ L : List (List U8),
    ([sep].intercalate L).length = (L.map List.length).sum + (L.length - 1)
  | [] => rfl
  | [l] => by simp only [List.intercalate_singleton, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, List.length_cons, List.length_nil, zero_add, tsub_self]
  | l :: l' :: zs => by
    rw [List.intercalate_cons_cons, List.length_append, List.length_append,
      length_intercalate_singleton sep (l' :: zs)]
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.length_nil]
    omega

theorem utf8_intercalate_slash : ∀ l : List String,
    utf8 (String.intercalate "/" l) = [byte 47].intercalate (l.map utf8)
  | [] => by rw [String.intercalate_nil, utf8_empty]; rfl
  | [a] => by rw [String.intercalate_singleton]; simp only [List.map_cons, List.map_nil,
      List.intercalate_singleton]
  | a :: b :: rest => by
    rw [String.intercalate_cons_cons, utf8_append, utf8_append, utf8_intercalate_slash (b :: rest)]
    simp only [List.map_cons]
    rw [List.intercalate_cons_cons]
    have : utf8 "/" = [byte 47] := by
      rw [show "/" = String.ofList ['/'] from rfl, utf8_ofList_singleton_ascii _ (by decide)]; rfl
    rw [this, List.append_assoc]

theorem takeWhile_not_isQueryOrFragmentStart (l : List U8) :
    l.takeWhile (fun b => !isQueryOrFragmentStart b) =
      l.take ((l.findIdx? fun b => decide (b.val = 63 ∨ b.val = 35)).getD l.length) := by
  rw [List.takeWhile_eq_take_findIdx_not, ← List.findIdx_eq_getD_findIdx?]
  congr 2
  funext b; rw [Bool.not_not, isQueryOrFragmentStart_eq_decide]

theorem dropWhile_not_isQueryOrFragmentStart (l : List U8) :
    l.dropWhile (fun b => !isQueryOrFragmentStart b) =
      l.drop ((l.findIdx? fun b => decide (b.val = 63 ∨ b.val = 35)).getD l.length) := by
  rw [List.dropWhile_eq_drop_findIdx_not, ← List.findIdx_eq_getD_findIdx?]
  congr 2
  funext b; rw [Bool.not_not, isQueryOrFragmentStart_eq_decide]

/-- One step of the dot-segment removal of `removeDotSegments`. -/
def dotStep (acc : Option (List (List U8))) (segment : List U8) : Option (List (List U8)) :=
  acc.bind fun dirs =>
    if segment = Defs.utf8Bytes "." then some dirs
    else if segment = Defs.utf8Bytes ".." then (if dirs = [] then none else some dirs.dropLast)
    else some (dirs ++ [segment])

theorem removeDotSegments_eq_foldl_dotStep (segs : List (List U8)) :
    removeDotSegments segs = segs.foldl dotStep (some []) := rfl

/-- The segment strings of a `Vec`, as bytes. -/
def vecBytes (v : alloc.vec.Vec String) : List (List U8) := v.val.map utf8

theorem stripSuffix_eq (l suf : List U8) :
    stripSuffix l suf = if suf <:+ l then some (l.take (l.length - suf.length)) else none := by
  unfold stripSuffix
  by_cases h : suf <:+ l
  · rw [ite_eq_left (List.isSuffixOf_iff_suffix.2 h), ite_eq_left h]
  · rw [ite_eq_right (mt List.isSuffixOf_iff_suffix.1 h), ite_eq_right h]

theorem stripPrefix_eq (l pre : List U8) :
    stripPrefix l pre = if pre <+: l then some (l.drop pre.length) else none := by
  unfold stripPrefix
  by_cases h : pre <+: l
  · rw [ite_eq_left (List.isPrefixOf_iff_prefix.2 h), ite_eq_left h]
  · rw [ite_eq_right (mt List.isPrefixOf_iff_prefix.1 h), ite_eq_right h]

theorem isCharBoundary_length (l : List U8) : isCharBoundary l l.length = true := by
  unfold isCharBoundary
  split
  · rfl
  · rw [ite_eq_left (le_refl _)]; exact decide_eq_true rfl

/-- The length of the key: the kept segments are a sublist of the directory segments. -/
theorem length_intercalate_le {segs dirs : List (List U8)} (hne : segs ≠ [])
    (hsub : dirs.Sublist segs.dropLast) :
    ([byte 47].intercalate (dirs ++ [segs.getLast hne])).length + 1 ≤
      (segs.map List.length).sum + segs.length := by
  rw [length_intercalate_singleton]
  have h1 := (hsub.map (fun d => d.length + 1)).sum_le_sum (fun _ _ => Nat.zero_le _)
  have hsplit := List.dropLast_append_getLast hne
  have hs : (segs.map List.length).sum + segs.length =
      ((segs.dropLast.map (fun d => d.length + 1)).sum) + (segs.getLast hne).length + 1 := by
    conv_lhs => rw [← hsplit]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.length_append, List.length_singleton]
    have : ∀ L : List (List U8), (L.map (fun d => d.length + 1)).sum =
        (L.map List.length).sum + L.length := by
      intro L; induction L with
      | nil => rfl
      | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
    rw [this]; omega
  have hd : (dirs.map (fun d => d.length + 1)).sum = (dirs.map List.length).sum + dirs.length := by
    clear h1 hsub hs
    induction dirs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, List.length_append, List.length_singleton]
  omega

theorem length_le_of_mem_splitBytes (sep : U8) (l : List U8) :
    ∀ p ∈ splitBytes sep l, p.length ≤ l.length := by
  intro p hp
  have hsum := sum_length_splitBytes sep l
  have h1 := List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) hp)
  have h2 : 1 ≤ (splitBytes sep l).length := List.length_pos_of_mem hp
  omega

/-! ## Skill names -/

/-- The loop of `is_valid_skill_name` (patched lines 360–378) on the characters from index `i`
on, with the flag `needs` (`needs_alphanumeric`). -/
def nameLoop (alnum : Char → Bool) : Bool → Nat → List Char → Bool
  | needs, _, [] => !needs
  | needs, i, c :: rest =>
    if 64 ≤ i then false
    else if alnum c then nameLoop alnum false (i + 1) rest
    else if c = '-' then (if needs then false else nameLoop alnum true (i + 1) rest)
    else false

/-- The loop without the index bound. -/
def goodName (alnum : Char → Bool) : Bool → List Char → Bool
  | needs, [] => !needs
  | needs, c :: rest =>
    if alnum c then goodName alnum false rest
    else if c = '-' then (if needs then false else goodName alnum true rest)
    else false

theorem nameLoop_eq (alnum : Char → Bool) : ∀ (needs : Bool) (i : Nat) (cs : List Char),
    i ≤ 64 → nameLoop alnum needs i cs = (decide (i + cs.length ≤ 64) && goodName alnum needs cs)
  | needs, i, [], hi => by
    simp only [nameLoop, goodName, List.length_nil, Nat.add_zero, hi, decide_true, Bool.true_and]
  | needs, i, c :: rest, hi => by
    rw [nameLoop, goodName]
    by_cases h64 : 64 ≤ i
    · rw [ite_eq_left h64]
      simp only [List.length_cons]
      rw [decide_eq_false (by omega), Bool.false_and]
    · rw [ite_eq_right h64]
      have ih1 := nameLoop_eq alnum false (i + 1) rest (by omega)
      have ih2 := nameLoop_eq alnum true (i + 1) rest (by omega)
      have hl : decide (i + 1 + rest.length ≤ 64) = decide (i + (c :: rest).length ≤ 64) :=
        decide_eq_decide.2 (by simp only [List.length_cons]; omega)
      split
      · rw [ih1, hl]
      · split
        · split
          · simp only [List.length_cons, Bool.and_false]
          · rw [ih2, hl]
        · simp only [List.length_cons, Bool.and_false]

theorem goodName_iff (alnum : Char → Bool) : ∀ (needs : Bool) (cs : List Char),
    goodName alnum needs cs = true ↔ (needs = true → cs ≠ []) ∧ NameRule alnum (!needs) cs
  | needs, [] => by
    cases needs
    · simp only [goodName, Bool.not_false, Bool.false_eq_true, ne_eq, not_true_eq_false, imp_self,
        nameRule_nil, and_self]
    · simp only [goodName, Bool.not_true, Bool.false_eq_true, ne_eq, not_true_eq_false, imp_false,
        nameRule_nil, and_true]
  | needs, c :: rest => by
    rw [goodName, nameRule_cons]
    by_cases hc : alnum c = true
    · rw [ite_eq_left hc, goodName_iff alnum false rest, hc]
      simp only [Bool.false_eq_true, ne_eq, IsEmpty.forall_iff, Bool.not_false, true_and,
        reduceCtorEq, not_false_eq_true, implies_true, ↓Char.isValue, Bool.not_eq_eq_eq_not,
        Bool.not_true, List.getD_eq_getElem?_getD, true_or]
    · rw [ite_eq_right hc]
      have hc' : alnum c = false := by simpa only [Bool.not_eq_true] using hc
      rw [hc']
      by_cases hd : c = '-'
      · rw [ite_eq_left hd]
        cases needs
        · rw [ite_eq_right (by simp only [Bool.false_eq_true,
            not_false_eq_true]), goodName_iff alnum true rest]
          constructor
          · rintro ⟨hne, hr⟩
            have hne := hne rfl
            refine ⟨fun h => absurd h (by decide), Or.inr ⟨hd, hne, rfl, ?_⟩, hr⟩
            rcases hr 0 (List.length_pos_iff.2 hne) with h0 | ⟨-, -, h3, -⟩
            · exact h0
            · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true] at h3
          · rintro ⟨-, h0, hr⟩
            rcases h0 with h0 | ⟨-, hne, -, -⟩
            · cases h0
            · exact ⟨fun _ => hne, hr⟩
        · rw [ite_eq_left rfl]
          simp only [Bool.false_eq_true, ne_eq, reduceCtorEq, not_false_eq_true, imp_self,
            ↓Char.isValue, Bool.not_true, List.getD_eq_getElem?_getD, false_and, and_false, or_self]
      · rw [ite_eq_right hd]
        simp only [Bool.false_eq_true, ne_eq, reduceCtorEq, not_false_eq_true, implies_true,
          ↓Char.isValue, hd, Bool.not_eq_eq_eq_not, Bool.not_true, List.getD_eq_getElem?_getD,
          false_and, or_self, and_false]

/-- `nameCharsValid` is the loop `nameLoop` of `is_valid_skill_name` from index `0`. -/
theorem nameCharsValid_eq_nameLoop (alnum : Char → Bool) (cs : List Char) :
    nameCharsValid alnum cs = nameLoop alnum true 0 cs := by
  rw [nameLoop_eq alnum true 0 cs (by omega), Nat.zero_add, Bool.eq_iff_iff,
    nameCharsValid_eq_true_iff, Bool.and_eq_true, decide_eq_true_eq, goodName_iff alnum true cs,
    Bool.not_true]
  exact ⟨fun ⟨hne, hl, h⟩ => ⟨hl, fun _ => hne, h⟩, fun ⟨hl, hne, h⟩ => ⟨hne rfl, hl, h⟩⟩

end Proofs.Model.Skill

namespace rmcp.model.skill

open ExtModel Proofs.External.Byte Proofs.External.Utf8 Proofs.External.Skill Proofs.Model.Skill
open Defs.Skill

/-- **Spec theorem for `rmcp::model::skill::is_unreserved`**: RFC 3986 unreserved bytes
(`isUnreserved`). Patched lines 476–478. -/
@[step]
theorem is_unreserved_spec (byte : U8) :
    is_unreserved byte ⦃ (result : Bool) => result = isUnreserved byte ⦄ := by
  unfold is_unreserved
  step as ⟨b, hb⟩
  have hb' := (isUnreserved_iff byte)
  by_cases h : b = true
  · rw [h]; simp only [↓reduceIte, WP.spec_ok]
    exact (hb'.2 (by have := hb.1 h; omega)).symm
  · rw [Bool.not_eq_true] at h
    rw [h]
    simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · rw [WP.spec_ok]; decide
    · rw [WP.spec_ok]; decide
    · rw [WP.spec_ok]; decide
    · rw [WP.spec_ok]; decide
    · rename_i h45 h46 h95 h126
      rw [WP.spec_ok]
      have n45 : byte.val ≠ 45 := fun e => h45 (UScalar.eq_of_val_eq (by rw [e]; rfl))
      have n46 : byte.val ≠ 46 := fun e => h46 (UScalar.eq_of_val_eq (by rw [e]; rfl))
      have n95 : byte.val ≠ 95 := fun e => h95 (UScalar.eq_of_val_eq (by rw [e]; rfl))
      have n126 : byte.val ≠ 126 := fun e => h126 (UScalar.eq_of_val_eq (by rw [e]; rfl))
      have hnb : ¬ (b = true) := by rw [h]; exact Bool.false_ne_true
      rw [hb] at hnb
      cases hu : isUnreserved byte
      · rfl
      · exact absurd (hb'.1 hu) (by omega)

/-- **Spec theorem for `rmcp::model::skill::is_ascii_hex`**: every byte is a hexadecimal digit
of either case. Patched lines 464–474. -/
@[step]
theorem is_ascii_hex_spec (s : Str) :
    is_ascii_hex s ⦃ (result : Bool) => result = s.val.all isHexDigit ⦄ := by
  unfold is_ascii_hex is_ascii_hex_loop
  step as ⟨bytes, hbytes⟩
  apply loop.spec_decr_nat (fun i : Usize => bytes.length - i.val)
    (fun i => i.val ≤ bytes.length ∧ (bytes.val.drop i.val).all isHexDigit = s.val.all isHexDigit)
  · rintro i ⟨hi, hinv⟩
    unfold is_ascii_hex_loop.body
    dsimp only
    split
    · rename_i hlt
      step as ⟨x, hx⟩
      step as ⟨b, hb⟩
      have hlt' : i.val < bytes.val.length := by scalar_tac
      have hdrop := List.drop_eq_getElem_cons hlt'
      have hxb : isHexDigit x = b := by
        rw [Bool.eq_iff_iff, hb, isHexDigit_iff]
      rw [hdrop, List.all_cons, ← hx, hxb] at hinv
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        rw [← hinv, Bool.false_and]
      · simp only [↓reduceIte]
        step as ⟨i3, hi3⟩
        refine ⟨by simp only [Slice.length] at hi ⊢; omega, ?_, ?_⟩
        · rw [hi3, ← hinv, Bool.true_and]
        · simp only [Slice.length] at hi ⊢; omega
    · rename_i hge
      have hge' : bytes.val.length ≤ i.val := by scalar_tac
      rw [WP.spec_ok, ← hinv, List.drop_eq_nil_of_le hge', List.all_nil]
  · exact ⟨Nat.zero_le _, by rw [hbytes]; rfl⟩

/-- **Spec theorem for `rmcp::model::skill::push_normalized_part`**: appends the
normalisation `normalizePart` of one part (the bytes after a `%`), for a part that is a `&str`
and a result that fits in a `String`. Patched lines 445–462.
Not tagged `@[step]`: `step` cannot infer the string `t` of the premise; use it with
`step with`. -/
theorem push_normalized_part_spec (normalized : String) (part : Str) (t : String)
    (ht : part.val = utf8 t)
    (hlen : normalized.utf8ByteSize + 1 + part.val.length ≤ maxStringBytes) :
    push_normalized_part normalized part ⦃ (result : String) =>
      utf8 result = utf8 normalized ++ normalizePart part.val ⦄ := by
  unfold push_normalized_part
  have hpct : utf8 (String.ofList ['%']) = [asciiByte '%'] := by
    rw [utf8_ofList_singleton_ascii _ (by decide)]; rfl
  step as ⟨o, ho⟩
  cases o with
  | none =>
    simp only [Option.map_none] at ho
    have hnb : isCharBoundary part.val 2 = false := by
      cases hb : isCharBoundary part.val 2
      · rfl
      · rw [hb] at ho; simp only [↓reduceIte, reduceCtorEq] at ho
    step as ⟨n1, hn1, hn1'⟩
    · have : '%'.utf8Size = 1 := by decide
      omega
    step with alloc.string.String.push_str_spec n1 part t ht as ⟨n2, hn2, hn2'⟩
    · rw [hn1, String.utf8ByteSize_push]
      have : '%'.utf8Size = 1 := by decide
      omega
    rw [hn2', hn1', hpct, List.append_assoc, List.singleton_append,
      normalizePart_of_not_hex]
    rintro a b r hp ⟨_, hb⟩
    rw [ht] at hp hnb
    rw [isCharBoundary_two_of_isHexDigit hp hb] at hnb
    cases hnb
  | some p =>
    obtain ⟨hex, rest⟩ := p
    have hbd : isCharBoundary part.val 2 = true := by
      cases hb : isCharBoundary part.val 2
      · rw [hb] at ho; simp only [Option.map_some, Bool.false_eq_true, ↓reduceIte,
          reduceCtorEq] at ho
      · rfl
    rw [hbd, ite_eq_left rfl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at ho
    obtain ⟨hhex, hrest⟩ := ho
    have hbd' : isCharBoundary (utf8 t) 2 = true := by rw [← ht]; exact hbd
    obtain ⟨v, hv⟩ := exists_eq_utf8_drop_of_isCharBoundary hbd'
    obtain ⟨u, hu⟩ := exists_eq_utf8_take_of_isCharBoundary hbd'
    rw [← ht] at hv hu
    have h2 := two_le_length_of_isCharBoundary hbd
    obtain ⟨h, l, r, hp⟩ : ∃ h l r, part.val = h :: l :: r := by
      match hq : part.val, h2 with
      | h :: l :: r, _ => exact ⟨h, l, r, rfl⟩
    rw [hp] at hhex hrest
    simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]
      at hhex hrest
    step as ⟨b, hb⟩
    rw [hhex] at hb
    simp only [List.all_cons, List.all_nil, Bool.and_true] at hb
    have hsz1 : '%'.utf8Size = 1 := by decide
    have hplen : part.val.length = r.length + 2 := by
      rw [hp]
      rfl
    split
    · rename_i hbt
      rw [hbt, eq_comm, Bool.and_eq_true] at hb
      obtain ⟨hh, hl⟩ := hb
      step as ⟨rr, hrr⟩
      rw [hhex, u8FromAscii_hex hh hl] at hrr
      obtain ⟨x, rfl, hx⟩ := hrr
      simp only [core.result.Result.expect, bind_ok]
      have hxe : x = hexByte h l := UScalar.eq_of_val_eq (by rw [hx, val_hexByte hh hl])
      step as ⟨b1, hb1⟩
      rw [hxe] at hb1
      have hnp : normalizePart part.val =
          (if isUnreserved (hexByte h l) then [hexByte h l]
            else [asciiByte '%', Defs.Skill.upperHexDigit (hexValue h),
              Defs.Skill.upperHexDigit (hexValue l)]) ++ r := by
        rw [hp]; simp only [normalizePart, hh, hl, Bool.and_self, ↓reduceIte]
      split
      · rename_i hb1t
        rw [hb1t, eq_comm] at hb1
        have hxa : x.val < 128 := by rw [hxe]; exact val_lt_128_of_isUnreserved hb1
        step as ⟨c, hc, hc'⟩
        have hcs : c.utf8Size = 1 := by
          rw [Char.utf8Size_eq_one_iff, UInt32.le_iff_toNat_le]
          exact Nat.lt_succ_iff.1 (by rw [← Char.toNat, hc']; exact hxa)
        step as ⟨n1, hn1, hn1'⟩
        step with alloc.string.String.push_str_spec n1 rest v (by rw [hrest, ← hv, hp]; rfl) as
          ⟨n2, hn2, hn2'⟩
        · rw [hn1, String.utf8ByteSize_push, hrest]; omega
        rw [hn2', hn1', utf8_ofList_singleton_ascii _ (by rw [hc']; exact hxa), hnp,
          ite_eq_left hb1, hrest, List.append_assoc, ← hxe, hc', byte_eq rfl]
      · rename_i hb1f
        have hb1' : isUnreserved (hexByte h l) = false := by
          rw [← hb1]
          exact Bool.eq_false_iff.2 hb1f
        step as ⟨n1, hn1, hn1'⟩
        obtain ⟨up, hup⟩ := exists_map_asciiUppercase_utf8_eq_utf8 u
        have hhexu : hex.val = utf8 u := by rw [hhex, ← hu, hp]; rfl
        step with alloc.str.Str.to_ascii_uppercase_spec hex up (by rw [hhexu, hup]) as
          ⟨s1, hs1, hs1'⟩
        have hs1v : utf8 s1 = [Defs.Skill.upperHexDigit (hexValue h),
            Defs.Skill.upperHexDigit (hexValue l)] := by
          rw [hs1', hhex]
          simp only [List.map_cons, List.map_nil, asciiUppercase_eq_upperHexDigit hh,
            asciiUppercase_eq_upperHexDigit hl]
        have hs1len : s1.utf8ByteSize = 2 := by rw [← length_utf8, hs1v]; rfl
        step as ⟨s2, hs2⟩
        step with alloc.string.String.push_str_spec n1 s2 s1 hs2 as ⟨n2, hn2, hn2'⟩
        · rw [hn1, String.utf8ByteSize_push, hs2, hs1v, List.length_cons, List.length_cons,
            List.length_nil]
          omega
        step with alloc.string.String.push_str_spec n2 rest v (by rw [hrest, ← hv, hp]; rfl) as
          ⟨n3, hn3, hn3'⟩
        · rw [hn2, hn1, String.utf8ByteSize_append, String.utf8ByteSize_push, hs1len, hrest]
          omega
        rw [hn3', hn2', hn1', hpct, hs2, hs1v, hnp, ite_eq_right (by rw [hb1']; decide), hrest]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
    · rename_i hbf
      step as ⟨n1, hn1, hn1'⟩
      step with alloc.string.String.push_str_spec n1 part t ht as ⟨n2, hn2, hn2'⟩
      · rw [hn1, String.utf8ByteSize_push]; omega
      rw [hn2', hn1', hpct, List.append_assoc, List.singleton_append, normalizePart_of_not_hex]
      rintro a c r' hq ⟨ha, hc⟩
      rw [hp] at hq
      simp only [List.cons.injEq] at hq
      obtain ⟨rfl, rfl, -⟩ := hq
      apply hbf
      rw [hb, ha, hc]; rfl

/-- The loop of `normalize_percent_encoding` (patched lines 436–439): appends the normalisation
of every part from index `i` on. -/
@[step]
theorem normalize_percent_encoding_loop_spec (normalized : String) (parts : alloc.vec.Vec String)
    (i : Usize) (hi : i.val ≤ parts.length)
    (hlen : (utf8 normalized).length +
      ((parts.val.drop i.val).map (fun p => (utf8 p).length + 1)).sum ≤ maxStringBytes) :
    normalize_percent_encoding_loop normalized parts i ⦃ (result : String) =>
      utf8 result = utf8 normalized ++
        (parts.val.drop i.val).flatMap (fun p => normalizePart (utf8 p)) ⦄ := by
  unfold normalize_percent_encoding_loop
  apply loop.spec_decr_nat (fun st : String × Usize => parts.length - st.2.val)
    (fun st => st.2.val ≤ parts.length ∧
      utf8 st.1 ++ (parts.val.drop st.2.val).flatMap (fun p => normalizePart (utf8 p)) =
        utf8 normalized ++ (parts.val.drop i.val).flatMap (fun p => normalizePart (utf8 p)) ∧
      (utf8 st.1).length + ((parts.val.drop st.2.val).map (fun p => (utf8 p).length + 1)).sum ≤
        maxStringBytes)
  · rintro ⟨n, j⟩ ⟨hj, heq, hb⟩
    dsimp only at hj heq hb ⊢
    unfold normalize_percent_encoding_loop.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : j.val < parts.val.length := by scalar_tac
      have hdrop := List.drop_eq_getElem_cons hlt'
      step as ⟨s, hs⟩
      subst hs
      rw [hdrop] at heq hb
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons] at heq hb
      have hmax := maxStringBytes_le_usize_max
      step as ⟨s1, hs1⟩
      · rw [← length_utf8]; omega
      step with push_normalized_part_spec n s1 _ hs1 as ⟨n1, hn1⟩
      · rw [hs1, ← length_utf8]; omega
      step as ⟨j2, hj2⟩
      refine ⟨by simp only [alloc.vec.Vec.length] at hlt' ⊢; omega, ?_, ?_, ?_⟩
      · rw [hj2, hn1, hs1, ← heq, List.append_assoc]
      · rw [hj2, hn1, hs1, List.length_append]
        have := length_normalizePart_le (utf8 parts.val[j.val])
        omega
      · simp only [alloc.vec.Vec.length] at hlt' ⊢; omega
    · rename_i hge
      have hge' : parts.val.length ≤ j.val := by scalar_tac
      rw [WP.spec_ok, ← heq, List.drop_eq_nil_of_le hge', List.flatMap_nil, List.append_nil]
  · exact ⟨hi, rfl, hlen⟩

/-- **Spec theorem for `rmcp::model::skill::normalize_percent_encoding`**: the bytes of the
`Cow` are `normalizePercent value` (patched lines 428–441), for a value of `n` bytes with
`24 * (n + 1) ≤ isize::MAX` (`UriFits`). -/
@[step]
theorem normalize_percent_encoding_spec (value : Str)
    (hfit : 24 * (value.val.length + 1) ≤ maxStringBytes) :
    normalize_percent_encoding value ⦃ (result : alloc.borrow.Cow Str String) =>
      cowStrBytes result = normalizePercent value.val ⦄ := by
  unfold normalize_percent_encoding
  have h3 := length_percentEncodeControls_le value.val
  have hc := count_percentEncodeControls_le value.val
  have hasc := val_lt_128_of_mem_percentEncodeControls value.val
  step as ⟨enc, henc, _⟩
  step with alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref_str_spec enc (by
    rintro o rfl
    have := maxStringBytes_le_usize_max
    rw [← length_utf8]; simp only [cowStrBytes] at henc; rw [henc]; omega) as ⟨s, hs⟩
  rw [henc] at hs
  have hfind : (fun b : U8 => decide (b.val = 37)) = (fun b => decide (b = byte 37)) := by
    funext b; exact decide_eq_decide.2 (eq_byte_iff b 37 (by decide)).symm
  step as ⟨o, ho⟩
  rw [hfind, hs] at ho
  have hnp : normalizePercent value.val =
      match splitBytes (byte 37) (percentEncodeControls value.val) with
      | [] => []
      | first :: parts => first ++ parts.flatMap normalizePart := by
    rw [normalizePercent, encodeControls_eq_percentEncodeControls, ← asciiByte_percent,
      ← splitBytes_eq_splitOn]
    cases splitBytes (asciiByte '%') (percentEncodeControls value.val) <;> rfl
  cases o with
  | none =>
    rw [Option.map_none, eq_comm, Option.map_eq_none_iff] at ho
    rw [WP.spec_ok, henc, hnp, splitBytes_of_findIdx?_eq_none _ _ ho]
    simp only [List.flatMap_nil, List.append_nil]
  | some p =>
    obtain ⟨pre, esc⟩ := p
    rw [Option.map_some, eq_comm, Option.map_eq_some_iff] at ho
    obtain ⟨k, hk, hkp⟩ := ho
    simp only [Prod.mk.injEq] at hkp
    obtain ⟨hpre, hesc⟩ := hkp
    replace hpre := hpre.symm
    replace hesc := hesc.symm
    have hsplit := splitBytes_of_findIdx?_eq_some _ _ _ hk
    have hkl : k < (percentEncodeControls value.val).length :=
      (List.findIdx?_eq_some_iff_getElem.1 hk).1
    have hpasc : ∀ b ∈ pre.val, b.val < 128 := by
      rw [hpre]; intro b hb; exact hasc b (List.mem_of_mem_take hb)
    have heasc : ∀ b ∈ esc.val, b.val < 128 := by
      rw [hesc]; intro b hb; exact hasc b (List.mem_of_mem_drop hb)
    obtain ⟨tp, htp⟩ := exists_eq_utf8_of_ascii hpasc
    step with Str.Insts.AllocBorrowToOwnedString.to_owned_spec pre tp htp as ⟨n0, hn0⟩
    have hcount := length_splitBytes (byte 37) (percentEncodeControls value.val)
    rw [hsplit, List.length_cons] at hcount
    step with model.skill.prim.split_percent_spec esc (fun q hq => exists_eq_utf8_of_ascii
      (fun b hb => heasc b (mem_of_mem_splitBytes _ _ q hq b hb))) (by
        rw [hesc]; omega) as ⟨parts, hparts⟩
    have hsum := sum_length_splitBytes (byte 37) esc.val
    rw [← hparts, List.map_map] at hsum
    have hlenesc : esc.val.length + 1 + pre.val.length =
        (percentEncodeControls value.val).length := by
      rw [hesc, hpre, List.length_drop, List.length_take]; omega
    have h0 : (0#usize).val = 0 := rfl
    step with normalize_percent_encoding_loop_spec n0 parts 0#usize (Nat.zero_le _) (by
      rw [hn0, ← htp, h0, List.drop_zero]
      have : (parts.val.map (fun p => (utf8 p).length + 1)).sum =
          (parts.val.map (List.length ∘ utf8)).sum + parts.val.length := by
        clear hsum hparts
        induction parts.val with
        | nil => rfl
        | cons q qs ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons, Function.comp_apply, ih]
          omega
      have hpl : parts.val.length = (splitBytes (byte 37) esc.val).length := by
        rw [← hparts, List.length_map]
      rw [List.length_map] at hsum
      omega) as ⟨n1, hn1⟩
    simp only [cowStrBytes]
    rw [hn1, hn0, ← htp, List.drop_zero, hnp, hsplit, ← hpre, ← hesc, ← hparts]
    simp only [List.flatMap_map]

theorem toStr_dot_val (h) : (toStr "." h).val = Defs.utf8Bytes "." := toStr_val _ _

theorem toStr_dotdot_val (h) : (toStr ".." h).val = Defs.utf8Bytes ".." := toStr_val _ _

theorem toStr_empty_val (h) : (toStr "" h).val = [] := by rw [toStr_val, utf8_empty]

/-- **Spec theorem for `rmcp::model::skill::resolve_segment`**: one step of the dot-segment
removal (`dotStep`), patched lines 413–423.
Not tagged `@[step]`: `step` cannot infer the string `t` of the premise; use it with
`step with`. -/
theorem resolve_segment_spec (resolved : Option (alloc.vec.Vec String)) (segment : Str)
    (t : String) (ht : segment.val = utf8 t)
    (hlen : ∀ v, resolved = some v → v.length < Usize.max) :
    resolve_segment resolved segment ⦃ (result : Option (alloc.vec.Vec String)) =>
      result.map vecBytes = dotStep (resolved.map vecBytes) segment.val ∧
        ∀ v', result = some v' → ∃ v, resolved = some v ∧ v'.length ≤ v.length + 1 ⦄ := by
  unfold resolve_segment
  step as ⟨cf, hcf⟩
  cases resolved with
  | none =>
    subst hcf
    step as ⟨r, hr⟩
    subst hr
    exact ⟨rfl, fun v' h => nomatch h⟩
  | some val =>
    subst hcf
    step as ⟨b, hb⟩
    rw [toStr_dot_val] at hb
    split
    · rename_i hbt
      rw [WP.spec_ok]
      refine ⟨?_, ?_⟩
      · simp only [Option.map_some, dotStep, Option.bind_some, hb.1 hbt, ↓reduceIte]
      · rintro v' ⟨⟩; exact ⟨val, rfl, Nat.le_succ _⟩
    · rename_i hbf
      have hnd : segment.val ≠ Defs.utf8Bytes "." := fun h => hbf (hb.2 h)
      step as ⟨b1, hb1⟩
      rw [toStr_dotdot_val] at hb1
      split
      · rename_i hb1t
        have hdd := hb1.1 hb1t
        have hne2 : Defs.utf8Bytes ".." ≠ Defs.utf8Bytes "." := hdd ▸ hnd
        step as ⟨o, val1, hp1, hp2⟩
        step as ⟨cf1, hcf1⟩
        subst hcf1
        cases o with
        | none =>
          dsimp only
          step as ⟨r, hr⟩
          subst hr
          refine ⟨?_, fun v' h => nomatch h⟩
          have : val.val = [] := List.getLast?_eq_none_iff.1 hp1.symm
          simp only [Option.map_none, Option.map_some, dotStep, Option.bind_some, hne2, hdd,
            ↓reduceIte, vecBytes, this, List.map_nil]
        | some x =>
          dsimp only
          rw [WP.spec_ok]
          have hne : val.val ≠ [] := by intro h; rw [h] at hp1; simp only [List.getLast?_nil,
              reduceCtorEq] at hp1
          refine ⟨?_, ?_⟩
          · simp only [Option.map_some, dotStep, Option.bind_some, hne2, hdd, ↓reduceIte,
              vecBytes, hp2, List.map_dropLast, List.map_eq_nil_iff, hne]
          · rintro v' ⟨⟩
            refine ⟨val, rfl, ?_⟩
            simp only [alloc.vec.Vec.length, hp2, List.length_dropLast]; omega
      · rename_i hb1f
        have hndd : segment.val ≠ Defs.utf8Bytes ".." := fun h => hb1f (hb1.2 h)
        step with Str.Insts.AllocBorrowToOwnedString.to_owned_spec segment t ht as ⟨s, hs⟩
        step as ⟨val1, hval1⟩
        refine ⟨?_, ?_⟩
        · simp only [Option.map_some, dotStep, Option.bind_some, hnd, hndd, ↓reduceIte,
            vecBytes, hval1, List.map_append, List.map_cons, List.map_nil, hs, ← ht]
        · rintro v' ⟨⟩
          refine ⟨val, rfl, ?_⟩
          simp only [alloc.vec.Vec.length, hval1, List.length_append, List.length_singleton]
          omega

/-- **Spec theorem for `rmcp::model::skill::resolve_segments`**: dot-segment removal
(`removeDotSegments`) over the segments, as bytes (patched lines 402–410). -/
@[step]
theorem resolve_segments_spec (segments : Slice String)
    (hsz : ∀ s ∈ segments.val, s.utf8ByteSize ≤ Usize.max) :
    resolve_segments segments ⦃ (result : Option (alloc.vec.Vec String)) =>
      result.map vecBytes = removeDotSegments (segments.val.map utf8) ⦄ := by
  unfold resolve_segments resolve_segments_loop
  apply loop.spec_decr_nat
    (fun st : Option (alloc.vec.Vec String) × Usize => segments.length - st.2.val)
    (fun st => st.2.val ≤ segments.length ∧
      ((segments.val.drop st.2.val).map utf8).foldl dotStep (st.1.map vecBytes) =
        removeDotSegments (segments.val.map utf8) ∧
      ∀ v, st.1 = some v → v.length ≤ st.2.val)
  · rintro ⟨r, j⟩ ⟨hj, heq, hv⟩
    dsimp only at hj heq hv ⊢
    unfold resolve_segments_loop.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : j.val < segments.val.length := by scalar_tac
      have hdrop := List.drop_eq_getElem_cons hlt'
      step as ⟨s, hs⟩
      subst hs
      step as ⟨s1, hs1⟩
      · exact hsz _ (List.getElem_mem _)
      step with resolve_segment_spec r s1 _ hs1 (by
        intro v hv'; have := hv v hv'; have := segments.property
        omega) as ⟨r1, hr1, hr1'⟩
      step as ⟨j2, hj2⟩
      refine ⟨by simp only [Slice.length] at hlt' ⊢; omega, ?_, ?_, ?_⟩
      · rw [hj2, ← heq, hdrop, List.map_cons, List.foldl_cons, hr1, hs1]
      · intro v' hv'
        obtain ⟨v, hv1, hv2⟩ := hr1' v' hv'
        have := hv v hv1
        omega
      · simp only [Slice.length] at hlt' ⊢; omega
    · rename_i hge
      have hge' : segments.val.length ≤ j.val := by scalar_tac
      rw [WP.spec_ok, ← heq, List.drop_eq_nil_of_le hge', List.map_nil, List.foldl_nil]
  · refine ⟨Nat.zero_le _, ?_, ?_⟩
    · simp only [Option.map_some, vecBytes, removeDotSegments_eq_foldl_dotStep]; rfl
    · rintro v ⟨⟩; simp only [alloc.vec.Vec.length, alloc.vec.Vec.from_val, List.length_nil,
        UScalar.ofNatCore_val_eq, Std.le_refl]

theorem SKILL_MD_val : SKILL_MD.val = utf8 "SKILL.md" := by
  unfold model.skill.SKILL_MD; exact toStr_val _ _

/-- **Spec theorem for `rmcp::model::skill::manifest_resource_key`**: the comparison key of a
manifest file (`manifestKey`), patched lines 381–399, for `&str` arguments and a resource URI of
`n` bytes with `24 * (n + 1) ≤ isize::MAX` (`UriFits`).
Not tagged `@[step]`: `step` cannot infer the string `t` of the premise; use it with
`step with`. -/
theorem manifest_resource_key_spec (skill_uri resource_uri : Str) (ts tr : String)
    (hs : skill_uri.val = utf8 ts) (hr : resource_uri.val = utf8 tr)
    (hfit : 24 * (resource_uri.val.length + 1) ≤ maxStringBytes) :
    manifest_resource_key skill_uri resource_uri ⦃ (result : Option String) =>
      result.map utf8 = manifestKey skill_uri.val resource_uri.val ⦄ := by
  unfold manifest_resource_key
  have hmax := maxStringBytes_le_usize_max
  step as ⟨o, ho⟩
  rw [SKILL_MD_val] at ho
  step as ⟨cf, hcf⟩
  subst hcf
  cases o with
  | none =>
    step as ⟨r, hr'⟩
    subst hr'
    have : stripSuffix skill_uri.val skillMd = none := by
      rw [stripSuffix_eq]; exact ho.symm
    simp only [Option.map_none, manifestKey, this, Option.bind_eq_bind, Option.bind_none]
  | some root =>
    have hsuf : utf8 "SKILL.md" <:+ skill_uri.val := by
      by_contra hn; rw [ite_eq_right hn] at ho; simp only [Option.map_some, reduceCtorEq] at ho
    rw [ite_eq_left hsuf, Option.map_some, Option.some.injEq] at ho
    have hss : stripSuffix skill_uri.val skillMd = some root.val := by
      rw [stripSuffix_eq, show skillMd = utf8 "SKILL.md" from rfl, ite_eq_left hsuf, ho]
    obtain ⟨pr, hpr⟩ := exists_eq_utf8_take_of_suffix (s := "SKILL.md") (t := ts)
      (by rw [← hs]; exact hsuf)
    rw [← hs] at hpr
    rw [← ho] at hpr
    step as ⟨o1, ho1⟩
    step as ⟨cf1, hcf1⟩
    subst hcf1
    cases o1 with
    | none =>
      step as ⟨r, hr'⟩
      subst hr'
      have : stripPrefix resource_uri.val root.val = none := by
        rw [stripPrefix_eq]; exact ho1.symm
      simp only [Option.map_none, manifestKey, hss, this, Option.bind_eq_bind, Option.bind_some,
        Option.bind_none]
    | some val1 =>
      have hpre : root.val <+: resource_uri.val := by
        by_contra hn; rw [ite_eq_right hn] at ho1; simp only [Option.map_some, reduceCtorEq] at ho1
      rw [ite_eq_left hpre, Option.map_some, Option.some.injEq] at ho1
      have hsp : stripPrefix resource_uri.val root.val = some val1.val := by
        rw [stripPrefix_eq, ite_eq_left hpre, ← ho1]
      obtain ⟨v1, hv1⟩ := exists_eq_utf8_drop_of_prefix (p := pr) (t := tr)
        (by rw [← hr, ← hpr]; exact hpre)
      rw [← hr, ← hpr, ← ho1] at hv1
      have hv1len : val1.val.length ≤ resource_uri.val.length := by
        rw [ho1, List.length_drop]; omega
      step as ⟨o2, ho2⟩
      step as ⟨i, hi⟩
      simp only [lift, bind_ok]
      -- the split index: the first `?` or `#`, else the end
      set J := (val1.val.findIdx? fun b => decide (b.val = 63 ∨ b.val = 35)).getD
        val1.val.length with hJdef
      have hj : (core.option.Option.unwrap_or o2 i).val = J := by
        cases o2 with
        | none =>
          rw [Option.map_none, eq_comm] at ho2
          simp only [core.option.Option.unwrap_or, hJdef, ho2, Option.getD_none, hi]
        | some k =>
          rw [Option.map_some, eq_comm] at ho2
          simp only [core.option.Option.unwrap_or, hJdef, ho2, Option.getD_some]
      have hbd : isCharBoundary val1.val J = true := by
        rw [hJdef]
        cases hf : val1.val.findIdx? fun b => decide (b.val = 63 ∨ b.val = 35) with
        | none => exact isCharBoundary_length _
        | some k =>
          obtain ⟨hk, hpk, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
          rw [Option.getD_some]
          exact isCharBoundary_of_val_lt hk (by simp only [decide_eq_true_eq] at hpk; omega)
      step with core.str.Str.split_at_spec val1 _ (by rw [hj]; exact hbd) as
        ⟨path, suffix, hpath, hsuffix⟩
      rw [hj] at hpath hsuffix
      have hJle : J ≤ val1.val.length := by
        rw [hJdef]
        cases hf : val1.val.findIdx? fun b => decide (b.val = 63 ∨ b.val = 35) with
        | none => exact le_refl _
        | some k => exact le_of_lt (List.findIdx?_eq_some_iff_getElem.1 hf).1
      have hplen : path.val.length ≤ resource_uri.val.length := by
        rw [hpath, List.length_take]; omega
      have hslen : suffix.val.length ≤ resource_uri.val.length := by
        rw [hsuffix, List.length_drop]; omega
      obtain ⟨sv, hsv⟩ := exists_eq_utf8_drop_of_isCharBoundary (t := v1) (i := J)
        (by rw [← hv1]; exact hbd)
      rw [← hv1, ← hsuffix] at hsv
      step with normalize_percent_encoding_spec path (by omega) as ⟨c, hc⟩
      have hNlen := length_normalizePercent_le path.val
      step with alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref_str_spec c (by
        rintro o rfl; simp only [cowStrBytes] at hc
        rw [← length_utf8, hc]; omega) as ⟨sN, hsN⟩
      rw [hc] at hsN
      obtain ⟨tN, htN⟩ := exists_eq_utf8_of_ascii (val_lt_128_of_mem_normalizePercent path.val)
      have hcnt := count_slash_normalizePercent_le path.val
      have hseglen := length_splitBytes (byte 47) (normalizePercent path.val)
      step with model.skill.prim.split_slash_spec_of_eq_utf8 sN tN (by rw [hsN, htN]) (by
        rw [hsN, hseglen]; omega) as ⟨segments, hsegs⟩
      rw [hsN] at hsegs
      set segs := splitBytes (byte 47) (normalizePercent path.val) with hsegsdef
      have hsegsne : segs ≠ [] := splitBytes_ne_nil _ _
      have hsegments_ne : segments.val ≠ [] := by
        intro h; rw [h, List.map_nil] at hsegs; exact hsegsne hsegs.symm
      have hsegsz : ∀ x ∈ segments.val, x.utf8ByteSize ≤ maxStringBytes := by
        intro x hx
        have := length_le_of_mem_splitBytes (byte 47) (normalizePercent path.val) (utf8 x)
          (by rw [← hsegsdef, ← hsegs]; exact List.mem_map_of_mem hx)
        rw [← length_utf8]; omega
      -- the expected key
      have hmk : manifestKey skill_uri.val resource_uri.val =
          if segs.getLast hsegsne = [] ∨ segs.getLast hsegsne = Defs.utf8Bytes "." ∨
              segs.getLast hsegsne = Defs.utf8Bytes ".." then none
          else (removeDotSegments segs.dropLast).bind fun dirs =>
            some (List.intercalate [asciiByte '/'] (dirs ++ [segs.getLast hsegsne]) ++
              suffix.val) := by
        rw [manifestKey, hss, Option.bind_eq_bind, Option.bind_some, hsp, Option.bind_some]
        simp only [takeWhile_not_isQueryOrFragmentStart, dropWhile_not_isQueryOrFragmentStart,
          ← hJdef, ← hpath, ← hsuffix, asciiByte_slash, ← splitBytes_eq_splitOn, ← hsegsdef,
          List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hsegsne, Option.getD_some]
        rfl
      step as ⟨o3, seg1, ho3, hseg1⟩
      step as ⟨cf2, hcf2⟩
      subst hcf2
      rw [List.getLast?_eq_some_getLast hsegments_ne] at ho3
      subst ho3
      dsimp only
      set val2 := segments.val.getLast hsegments_ne with hval2
      have hfile : utf8 val2 = segs.getLast hsegsne := by
        simp only [hval2, ← hsegs]
        rw [List.getLast_map]
      have hval2sz := hsegsz val2 (List.getLast_mem _)
      step as ⟨s1, hs1⟩
      rw [hfile] at hs1
      step as ⟨b, hb⟩
      rw [toStr_empty_val] at hb
      split
      · rename_i hbt
        rw [WP.spec_ok, Option.map_none, hmk, ite_eq_left (Or.inl (by rw [← hs1]; exact hb.1 hbt))]
      · rename_i hbf
        have h1 : segs.getLast hsegsne ≠ [] := fun h => hbf (hb.2 (by rw [hs1, h]))
        step as ⟨b1, hb1⟩
        rw [toStr_dot_val] at hb1
        split
        · rename_i hb1t
          rw [WP.spec_ok, Option.map_none, hmk,
            ite_eq_left (Or.inr (Or.inl (by rw [← hs1]; exact hb1.1 hb1t)))]
        · rename_i hb1f
          have h2 : segs.getLast hsegsne ≠ Defs.utf8Bytes "." :=
            fun h => hb1f (hb1.2 (by rw [hs1, h]))
          step as ⟨b2, hb2⟩
          rw [toStr_dotdot_val] at hb2
          split
          · rename_i hb2t
            rw [WP.spec_ok, Option.map_none, hmk,
              ite_eq_left (Or.inr (Or.inr (by rw [← hs1]; exact hb2.1 hb2t)))]
          · rename_i hb2f
            have h3 : segs.getLast hsegsne ≠ Defs.utf8Bytes ".." :=
              fun h => hb2f (hb2.2 (by rw [hs1, h]))
            rw [ite_eq_right (fun h => h.elim h1 (fun h => h.elim h2 h3))] at hmk
            step with resolve_segments_spec seg1.deref (by
              intro x hx
              rw [alloc.vec.Vec.deref, Slice.from_val, hseg1] at hx
              have := hsegsz x (List.mem_of_mem_dropLast hx)
              omega) as ⟨o4, ho4⟩
            rw [alloc.vec.Vec.deref, Slice.from_val, hseg1, List.map_dropLast, hsegs] at ho4
            step as ⟨cf3, hcf3⟩
            subst hcf3
            cases o4 with
            | none =>
              step as ⟨r, hr'⟩
              subst hr'
              rw [Option.map_none, eq_comm] at ho4
              rw [Option.map_none, hmk, ho4, Option.bind_none]
            | some val3 =>
              rw [Option.map_some, eq_comm] at ho4
              have hsub := sublist_of_removeDotSegments_eq_some ho4
              have hsumN := sum_length_splitBytes (byte 47) (normalizePercent path.val)
              rw [← hsegsdef] at hsumN
              have hkey := length_intercalate_le hsegsne hsub
              have hv3len : val3.length < Usize.max := by
                have := hsub.length_le
                simp only [vecBytes, List.length_map, List.length_dropLast] at this
                simp only [alloc.vec.Vec.length]
                omega
              step as ⟨val4, hval4⟩
              have hv4 : val4.val.map utf8 = vecBytes val3 ++ [segs.getLast hsegsne] := by
                rw [hval4, List.map_append, List.map_singleton, hfile]; rfl
              step with model.skill.prim.join_slash_spec val4 (by
                rw [← length_utf8, utf8_intercalate_slash, hv4]; omega) as ⟨key, hkey'⟩
              step with alloc.string.String.push_str_spec key suffix sv hsv as ⟨key1, hk1, hk1'⟩
              · rw [hkey', ← length_utf8, utf8_intercalate_slash, hv4]; omega
              rw [Option.map_some, hmk, ho4, Option.bind_some, hk1', hkey',
                utf8_intercalate_slash, hv4, asciiByte_slash]

/-- The loop of `is_valid_skill_name` (patched lines 360–378) is `nameLoop` with the letters and
digits of `isNameAlnum`. -/
theorem is_valid_skill_name_loop_spec (needs_alphanumeric : Bool) (chars : alloc.vec.Vec Char)
    (index : Usize) (hidx : index.val ≤ chars.length) :
    is_valid_skill_name_loop needs_alphanumeric chars index ⦃ (result : Bool) =>
      result = nameLoop isNameAlnum needs_alphanumeric index.val (chars.val.drop index.val) ⦄ := by
  unfold is_valid_skill_name_loop
  apply loop.spec_decr_nat (fun st : Bool × Usize => chars.length - st.2.val)
    (fun st => st.2.val ≤ chars.length ∧
      nameLoop isNameAlnum st.1 st.2.val (chars.val.drop st.2.val) =
        nameLoop isNameAlnum needs_alphanumeric index.val (chars.val.drop index.val))
  · rintro ⟨needs, j⟩ ⟨hj, heq⟩
    dsimp only at hj heq ⊢
    unfold is_valid_skill_name_loop.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : j.val < chars.val.length := by scalar_tac
      have hdrop := List.drop_eq_getElem_cons hlt'
      rw [hdrop] at heq
      step as ⟨ch, hch⟩
      subst hch
      split
      · rename_i h64
        rw [WP.spec_ok, ← heq, nameLoop, ite_eq_left (by scalar_tac)]
      · rename_i h64
        have h64' : ¬ 64 ≤ j.val := by scalar_tac
        rw [nameLoop, ite_eq_right h64'] at heq
        step as ⟨gc, hgc⟩
        have hlen : j.val + 1 ≤ chars.length := by simp only [alloc.vec.Vec.length]; omega
        -- the six letter and number categories of `isNameAlnum` take the first branch of
        -- `nameLoop`, every other category the `-` branch
        cases gc with
        | LowercaseLetter | ModifierLetter | OtherLetter | DecimalNumber | LetterNumber
        | OtherNumber =>
          rw [isNameAlnum, ← hgc, ite_eq_left rfl] at heq
          dsimp only
          step as ⟨j2, hj2⟩
          exact ⟨by omega, by rw [hj2, ← heq], by omega⟩
        | _ =>
          rw [isNameAlnum, ← hgc, ite_eq_right Bool.false_ne_true] at heq
          dsimp only
          split
          · rename_i hd
            rw [ite_eq_left hd] at heq
            split
            · rename_i hn
              rw [WP.spec_ok, ← heq, ite_eq_left hn]
            · rename_i hn
              rw [ite_eq_right hn] at heq
              step as ⟨j2, hj2⟩
              exact ⟨by omega, by rw [hj2, ← heq], by omega⟩
          · rename_i hd
            rw [WP.spec_ok, ← heq, ite_eq_right hd]
    · rename_i hge
      have hge' : chars.val.length ≤ j.val := by scalar_tac
      rw [WP.spec_ok, ← heq, List.drop_eq_nil_of_le hge', nameLoop]
      cases needs <;> rfl
  · exact ⟨hidx, rfl⟩

/-- **Spec theorem for `rmcp::model::skill::is_valid_skill_name`**: `isSkillName` of the name
(patched lines 354–378), for a `&str` whose NFKC form fits the `Vec<char>` of `prim::nfkc`.
Not tagged `@[step]`: `step` cannot infer the string `t` of the premise; use it with
`step with`. -/
theorem is_valid_skill_name_spec («name» : Str) (t : String) (ht : «name».val = utf8 t)
    (hlen : 4 * (ExtModel.nfkc t.toList).length ≤ maxStringBytes) :
    is_valid_skill_name «name» ⦃ (result : Bool) => result = isSkillName t ⦄ := by
  unfold is_valid_skill_name
  step with model.skill.prim.nfkc_spec «name» t ht hlen as ⟨chars, hchars⟩
  step with is_valid_skill_name_loop_spec true chars 0#usize (Nat.zero_le _) as ⟨r, hr⟩
  rw [hr, isSkillName, nameCharsValid_eq_nameLoop, ← hchars]
  rfl

end rmcp.model.skill
