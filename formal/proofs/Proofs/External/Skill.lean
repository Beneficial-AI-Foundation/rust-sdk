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

@[expose] public section

/-!
# Specs of the externals of the public `skill.rs` API (K01–K20, translation patch 04)

Spec theorems for the models of `formal/trusted/Rmcp/FunsExternal.lean`, section "Public
`skill.rs` API": the twelve `skill::prim` wrappers that translation patch 04 adds
(`crates/rmcp/src/model/skill.rs` in the patched copy) and the standard-library and crate
functions that the twenty targets reach. Each external has a theorem named after it with
`_spec`; where the external takes a trait instance whose behaviour is not fixed, the theorem
takes the behaviour of the instance as a hypothesis (as `Option`'s `eq_spec` does) and is not a
`step` lemma; `into_owned_str_spec` and `deref_str_spec` give the `Cow<str>` instance of the
translation, and `as_deref_string_spec` the `Option<String>` instance of K01. The three
opaque values (`ExtModel.sha256`, `ExtModel.nfkc`, `ExtModel.generalCategory`) appear in the
postconditions unopened: their laws are hypotheses of the statements that need them (human
decision 2026-11-25), under the review rule of `formal/docs/STATUS.md`, "Trusted base".

Section "UTF-8 facts" (with the character-level facts of `Proofs.External.String`, such as
`utf8_ofList` and `le_val_of_mem_utf8_ofList_singleton`) proves the facts that every Rust `&str`
gives for free: the parts of the UTF-8 bytes of a string split at an ASCII byte are UTF-8
(`exists_eq_utf8_of_mem_splitBytes_utf8`),
and so are its bytes with ASCII lowercase letters mapped to uppercase
(`exists_map_asciiUppercase_utf8_eq_utf8`); the `_of_eq_utf8` variants of the split and
uppercase specs use them. Section "`serde_json::Map`" proves that the `BTreeMap` model keeps its
entries sorted by key and returns the old value of the key.

Section "Char boundaries" proves that the sub-slices the targets take of a `&str` are `&str`s:
the parts at a char boundary (`split_at`, `split_at_checked`:
`exists_eq_utf8_take_of_isCharBoundary`, `exists_eq_utf8_drop_of_isCharBoundary`), the rest
after a prefix and before a suffix (`strip_prefix`, `strip_suffix`:
`exists_eq_utf8_drop_of_prefix`, `exists_eq_utf8_take_of_suffix`), and the parts before and after
an ASCII byte (`split_once_percent`, `find_query_or_fragment`:
`exists_eq_utf8_take_and_drop_add_one_of_findIdx?_eq_some`), so that the `s.val = utf8 t`
premises of the specs can be discharged on them.

Section "Evaluation of the models" checks the exact models on small inputs by kernel
evaluation (`decide`, `rfl`): the models are structurally recursive and use no classical choice;
the wrapper `prim::percent_encode_controls` is evaluated on its three arms.
-/

open Aeneas Aeneas.Std Result
open rmcp

namespace Proofs.External.Skill

open ExtModel Proofs.External.Byte Proofs.External.Utf8

/-- The bytes a `Cow<str>` holds: the borrowed bytes, or the UTF-8 bytes of the owned
string. -/
def cowStrBytes : alloc.borrow.Cow Str String → List U8
  | alloc.borrow.Cow.Borrowed b => b.val
  | alloc.borrow.Cow.Owned o => utf8 o

/-- `ExtModel.usize n` has the value `n` for `n ≤ Usize.max`. -/
theorem usize_val {n : Nat} (h : n ≤ Usize.max) : (usize n).val = n := by
  have hlt : n < 2 ^ UScalarTy.Usize.numBits := by
    rw [Usize.max_def, Usize.numBits_def] at h
    have hpos : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
    omega
  show (BitVec.ofNat _ n).toNat = n
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- `collectVec` succeeds with the given elements when they fit. -/
theorem exists_collectVec_eq_ok {α : Type} (elemSize : Nat) (l : List α) (hsize : 1 ≤ elemSize)
    (h : elemSize * l.length ≤ maxStringBytes) :
    ∃ v, collectVec elemSize l = ok v ∧ v.val = l := by
  have hl : l.length ≤ Usize.max := by
    have := maxStringBytes_le_usize_max
    have : l.length ≤ elemSize * l.length := Nat.le_mul_of_pos_left _ hsize
    omega
  exact ⟨_, by rw [collectVec, dite_eq_left ⟨h, hl⟩], alloc.vec.Vec.from_val _ _⟩

/-- `collectVec` panics when the elements do not fit. -/
theorem collectVec_eq_fail {α : Type} (elemSize : Nat) (l : List α)
    (h : maxStringBytes < elemSize * l.length) :
    collectVec elemSize l = fail Error.panic := by
  rw [collectVec, dite_eq_right (fun h' => absurd h'.1 (Nat.not_le.2 h))]

/-- `stringsOfBytes` succeeds on UTF-8 parts with the strings they encode. -/
theorem exists_stringsOfBytes_eq_ok : ∀ (ps : List (List U8)), (∀ p ∈ ps, ∃ t, p = utf8 t) →
    ∃ strs, stringsOfBytes ps = ok strs ∧ strs.map utf8 = ps
  | [], _ => ⟨[], rfl, rfl⟩
  | p :: ps, h => by
    obtain ⟨t, ht⟩ := h p List.mem_cons_self
    obtain ⟨strs, hs, hm⟩ := exists_stringsOfBytes_eq_ok ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
    refine ⟨t :: strs, ?_, ?_⟩
    · rw [stringsOfBytes, ht, strOfBytes?_utf8]
      simp only [hs, bind_ok]
    · rw [List.map_cons, hm, ← ht]

/-- Without a byte that needs encoding, `percentEncodeControls` is the identity. -/
theorem percentEncodeControls_eq_self_of_forall : ∀ (l : List U8),
    (∀ b ∈ l, isControlOrNonAscii b = false) → percentEncodeControls l = l
  | [], _ => rfl
  | b :: rest, h => by
    rw [percentEncodeControls,
      ite_eq_right (by rw [h b List.mem_cons_self]; exact Bool.false_ne_true),
      percentEncodeControls_eq_self_of_forall rest (fun c hc => h c (List.mem_cons_of_mem _ hc))]

/-- The output of `percentEncodeControls` is ASCII. -/
theorem val_lt_128_of_mem_percentEncodeControls : ∀ (l : List U8),
    ∀ b ∈ percentEncodeControls l, b.val < 128
  | [], b, hb => by simp [percentEncodeControls] at hb
  | c :: rest, b, hb => by
    rw [percentEncodeControls] at hb
    split at hb
    · rcases List.mem_append.1 hb with hb | hb
      · simp only [percentEncodeByte, upperHexDigit, List.mem_cons, List.not_mem_nil,
          or_false] at hb
        have h16 : c.val / 16 < 16 := by have := val_lt c; omega
        have h16' : c.val % 16 < 16 := Nat.mod_lt _ (by decide)
        rcases hb with rfl | rfl | rfl
        · rw [byte_val]; decide
        · split <;> rw [byte_val] <;> omega
        · split <;> rw [byte_val] <;> omega
      · exact val_lt_128_of_mem_percentEncodeControls rest b hb
    · rename_i hc
      rcases List.mem_cons.1 hb with rfl | hb
      · simp only [isControlOrNonAscii, decide_eq_true_eq] at hc
        omega
      · exact val_lt_128_of_mem_percentEncodeControls rest b hb

/-- `Iterator::all` on a list, with a closure that does not change its state, computes
`List.all`. -/
theorem exists_sliceIterAll_eq_ok {T F : Type} (inst : core.ops.function.FnMut F T Bool) (p : T → Bool)
    (f : F) (hp : ∀ x, inst.call_mut f x = ok (p x, f)) :
    ∀ l : List T, ∃ n, sliceIterAll inst l f = ok (l.all p, n)
  | [] => ⟨0, rfl⟩
  | x :: rest => by
    obtain ⟨n, hn⟩ := exists_sliceIterAll_eq_ok inst p f hp rest
    simp only [sliceIterAll, hp, bind_ok, List.all_cons]
    cases hpx : p x
    · exact ⟨1, by
        simp only [uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte, Bool.false_and]⟩
    · exact ⟨n + 1, by
        simp only [uncurry_apply_pair, ↓reduceIte, hn, bind_ok, Bool.true_and]⟩

/-- `listContainsEq` decides membership for an instance that decides equality. -/
theorem exists_listContainsEq_eq_ok {T : Type} (inst : core.cmp.Eq T) (value : T)
    (heq : ∀ a b, inst.partialEqInst.eq a b ⦃ (r : Bool) => (r = true ↔ a = b) ⦄) :
    ∀ l : List T, ∃ b, listContainsEq inst value l = ok b ∧ (b = true ↔ value ∈ l)
  | [] => ⟨false, rfl, by simp⟩
  | x :: rest => by
    obtain ⟨r, hr, hrv⟩ := Proofs.External.WP.exists_ok_of_spec (heq value x)
    obtain ⟨b, hb, hbv⟩ := exists_listContainsEq_eq_ok inst value heq rest
    rw [listContainsEq, hr, bind_ok]
    cases r
    · refine ⟨b, by simpa using hb, ?_⟩
      rw [hbv, List.mem_cons]
      have : value ≠ x := fun h => absurd (hrv.2 h) Bool.false_ne_true
      tauto
    · exact ⟨true, rfl, by simp [hrv.1 rfl]⟩

/-- The digit loop of `u8::from_str_radix` returns at most 255. -/
theorem u8DigitLoop_le (radix : Nat) : ∀ (acc : Nat) (l : List U8) (v : Nat), acc ≤ 255 →
    u8DigitLoop radix acc l = .ok v → v ≤ 255
  | acc, [], v, hacc, h => by
    simp only [u8DigitLoop, Except.ok.injEq] at h; omega
  | acc, c :: rest, v, _, h => by
    simp only [u8DigitLoop] at h
    split at h
    · simp at h
    · split at h
      · exact u8DigitLoop_le radix _ rest v (by assumption) h
      · simp at h

/-- `u8FromAscii` returns at most 255. -/
theorem u8FromAscii_le {radix : Nat} {l : List U8} {v : Nat} (h : u8FromAscii radix l = .ok v) :
    v ≤ 255 := by
  unfold u8FromAscii at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · exact u8DigitLoop_le radix 0 _ v (by omega) h
  · split at h
    · exact u8DigitLoop_le radix 0 _ v (by omega) h
    · exact u8DigitLoop_le radix 0 _ v (by omega) h

/-! ### UTF-8 facts -/

/-- Bytes without `sep` in front of `rest` extend the first part of the split of `rest`. -/
theorem splitBytes_append_of_forall_ne (sep : U8) : ∀ (bs rest : List U8), (∀ b ∈ bs, b ≠ sep) →
    ∀ p ps, splitBytes sep rest = p :: ps → splitBytes sep (bs ++ rest) = (bs ++ p) :: ps
  | [], _, _, _, _, h => h
  | b :: bs, rest, hne, p, ps, h => by
    rw [List.cons_append, splitBytes, ite_eq_right (hne b List.mem_cons_self),
      splitBytes_append_of_forall_ne sep bs rest
        (fun c hc => hne c (List.mem_cons_of_mem _ hc)) p ps h]
    rfl

/-- The split of the UTF-8 bytes of a string at an ASCII byte: a first part and further parts,
each the UTF-8 bytes of a string. -/
theorem exists_splitBytes_utf8_ofList (sep : U8) (hsep : sep.val < 128) : ∀ cs : List Char,
    ∃ (h : String) (ps : List (List U8)), splitBytes sep (utf8 (String.ofList cs)) = utf8 h :: ps ∧
      ∀ p ∈ ps, ∃ u, p = utf8 u
  | [] => ⟨"", [], by rw [utf8_ofList, List.flatMap_nil]; rfl, by simp⟩
  | c :: cs => by
    obtain ⟨h, ps, hs, hps⟩ := exists_splitBytes_utf8_ofList sep hsep cs
    rw [utf8_ofList_cons]
    by_cases hc : utf8 (String.ofList [c]) = [sep]
    · refine ⟨"", utf8 h :: ps, ?_, ?_⟩
      · rw [hc, List.singleton_append, splitBytes, ite_eq_left rfl, hs, utf8_empty]
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨h, rfl⟩
        · exact hps p hp
    · have hne : ∀ b ∈ utf8 (String.ofList [c]), b ≠ sep := by
        intro b hb hbs
        subst hbs
        by_cases hlt : c.toNat < 128
        · rw [utf8_ofList_singleton_ascii c hlt] at hb hc
          rw [List.mem_singleton] at hb
          exact hc (by rw [hb])
        · have := le_val_of_mem_utf8_ofList_singleton (Nat.not_lt.1 hlt) b hb
          omega
      refine ⟨String.ofList [c] ++ h, ps, ?_, hps⟩
      rw [splitBytes_append_of_forall_ne sep _ _ hne _ _ hs, utf8_append]

/-- **Splitting a `&str` at an ASCII byte gives `&str` parts**: every part of the UTF-8 bytes of
a string, split at a byte below 128, is the UTF-8 encoding of a string. -/
theorem exists_eq_utf8_of_mem_splitBytes_utf8 (sep : U8) (hsep : sep.val < 128) (t : String) :
    ∀ p ∈ splitBytes sep (utf8 t), ∃ u, p = utf8 u := by
  obtain ⟨h, ps, hs, hps⟩ := exists_splitBytes_utf8_ofList sep hsep t.toList
  rw [String.ofList_toList] at hs
  rw [hs]
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact ⟨h, rfl⟩
  · exact hps p hp

/-- `asciiUppercase` leaves a byte of at least 128 unchanged. -/
theorem asciiUppercase_eq_self_of_le {b : U8} (h : 128 ≤ b.val) : asciiUppercase b = b := by
  rw [asciiUppercase, ite_eq_right (by omega)]

/-- `asciiUppercase` maps an ASCII byte to an ASCII byte. -/
theorem val_asciiUppercase_lt {b : U8} (h : b.val < 128) : (asciiUppercase b).val < 128 := by
  unfold asciiUppercase
  split
  · rw [byte_val]; omega
  · exact h

/-- The bytes of a string of characters, with ASCII lowercase letters mapped to uppercase, are
the UTF-8 bytes of a string. -/
theorem exists_map_asciiUppercase_utf8_ofList_eq_utf8 : ∀ cs : List Char,
    ∃ u, (utf8 (String.ofList cs)).map asciiUppercase = utf8 u
  | [] => ⟨"", by rw [utf8_ofList, List.flatMap_nil]; rfl⟩
  | c :: cs => by
    obtain ⟨u, hu⟩ := exists_map_asciiUppercase_utf8_ofList_eq_utf8 cs
    have hc : ∃ v, (utf8 (String.ofList [c])).map asciiUppercase = utf8 v := by
      by_cases hlt : c.toNat < 128
      · rw [utf8_ofList_singleton_ascii c hlt, List.map_cons, List.map_nil]
        have hb0 : (byte c.toNat).val < 128 := by rw [byte_val]; omega
        have hx : ∀ b ∈ [asciiUppercase (byte c.toNat)], b.val < 128 := by
          intro b hb
          rw [List.mem_singleton] at hb
          rw [hb]; exact val_asciiUppercase_lt hb0
        exact ⟨_, (utf8_ofList_ascii [asciiUppercase (byte c.toNat)] hx).symm⟩
      · refine ⟨String.ofList [c], ?_⟩
        conv => rhs; rw [← List.map_id (utf8 (String.ofList [c]))]
        apply List.map_congr_left
        intro b hb
        exact asciiUppercase_eq_self_of_le
          (le_val_of_mem_utf8_ofList_singleton (Nat.not_lt.1 hlt) b hb)
    obtain ⟨v, hv⟩ := hc
    exact ⟨v ++ u, by rw [utf8_ofList_cons, List.map_append, hv, hu, utf8_append]⟩

/-- **`to_ascii_uppercase` keeps UTF-8**: the UTF-8 bytes of a string with ASCII lowercase
letters mapped to uppercase are the UTF-8 bytes of a string. -/
theorem exists_map_asciiUppercase_utf8_eq_utf8 (t : String) :
    ∃ u, (utf8 t).map asciiUppercase = utf8 u := by
  have := exists_map_asciiUppercase_utf8_ofList_eq_utf8 t.toList
  rwa [String.ofList_toList] at this

/-! ### Char boundaries -/

/-- A UTF-8 continuation byte `x &&& 0x3f ||| 0x80` is below 192 (and at least 128 by
`toNat_le_toNat_or`). -/
theorem toNat_and_or_lt (x : UInt8) : (x &&& 0x3f ||| 0x80).toNat < 192 := by
  rw [UInt8.toNat_or, UInt8.toNat_and]
  have h1 : x.toNat &&& 63 < 64 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have h2 : ∀ y, y < 64 → y ||| 128 < 192 := by decide
  exact h2 _ h1

/-- The bytes after the first of a character's UTF-8 encoding are continuation bytes
(`128..191`). -/
theorem le_toNat_and_toNat_lt_of_mem_tail_utf8EncodeChar (c : Char) :
    ∀ x ∈ (String.utf8EncodeChar c).tail, 128 ≤ x.toNat ∧ x.toNat < 192 := by
  have hpos := Char.utf8Size_pos c
  have hle := Char.utf8Size_le_four c
  have hx : ∀ y : UInt8,
      128 ≤ (y &&& 0x3f ||| 0x80).toNat ∧ (y &&& 0x3f ||| 0x80).toNat < 192 :=
    fun y => ⟨toNat_le_toNat_or _ 0x80, toNat_and_or_lt y⟩
  intro x hm
  rcases (by omega : c.utf8Size = 1 ∨ c.utf8Size = 2 ∨ c.utf8Size = 3 ∨ c.utf8Size = 4)
    with h | h | h | h
  · rw [String.utf8EncodeChar_eq_singleton h] at hm
    simp at hm
  · rw [String.utf8EncodeChar_eq_cons_cons h] at hm
    simp only [List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm; exact hx _
  · rw [String.utf8EncodeChar_eq_cons_cons_cons h] at hm
    simp only [List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> exact hx _
  · rw [String.utf8EncodeChar_eq_cons_cons_cons_cons h] at hm
    simp only [List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> exact hx _

/-- The first byte of a character's UTF-8 encoding is ASCII or at least 192 (not a continuation
byte). -/
theorem toNat_lt_or_le_of_mem_head?_utf8EncodeChar (c : Char) :
    ∀ x ∈ (String.utf8EncodeChar c).head?, x.toNat < 128 ∨ 192 ≤ x.toNat := by
  have hpos := Char.utf8Size_pos c
  have hle := Char.utf8Size_le_four c
  intro x hm
  rcases (by omega : c.utf8Size = 1 ∨ c.utf8Size = 2 ∨ c.utf8Size = 3 ∨ c.utf8Size = 4)
    with h | h | h | h
  · rw [String.utf8EncodeChar_eq_singleton h] at hm
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hm
    subst hm
    left
    have h' := UInt32.le_iff_toNat_le.1 (Char.utf8Size_eq_one_iff.1 h)
    have : (127 : UInt32).toNat = 127 := rfl
    simp only [UInt32.toNat_toUInt8]
    omega
  · rw [String.utf8EncodeChar_eq_cons_cons h] at hm
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hm
    subst hm; exact Or.inr (toNat_le_toNat_or _ 0xc0)
  · rw [String.utf8EncodeChar_eq_cons_cons_cons h] at hm
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hm
    subst hm; exact Or.inr (le_trans (by decide) (toNat_le_toNat_or _ 0xe0))
  · rw [String.utf8EncodeChar_eq_cons_cons_cons_cons h] at hm
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hm
    subst hm; exact Or.inr (le_trans (by decide) (toNat_le_toNat_or _ 0xf0))

/-- The UTF-8 bytes of one character: its encoding. -/
theorem utf8_ofList_singleton (c : Char) :
    utf8 (String.ofList [c]) = (String.utf8EncodeChar c).map (fun x => byte x.toNat) := by
  rw [utf8_ofList, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The empty list of characters has no bytes. -/
theorem utf8_ofList_nil : utf8 (String.ofList []) = [] := by
  rw [utf8_ofList, List.flatMap_nil]

/-- At a char boundary (`ExtModel.isCharBoundary`, Rust's `str::is_char_boundary`) the UTF-8
bytes of a string of characters are those of two strings, the first with `i` bytes. -/
theorem exists_utf8_ofList_eq_append_of_isCharBoundary : ∀ (cs : List Char) (i : Nat),
    isCharBoundary (utf8 (String.ofList cs)) i = true →
    ∃ u v, utf8 (String.ofList cs) = utf8 u ++ utf8 v ∧ (utf8 u).length = i
  | [], i, h => by
    rw [utf8_ofList_nil] at h ⊢
    have hi : i = 0 := by
      unfold isCharBoundary at h
      split at h
      · assumption
      · simpa using h
    exact ⟨"", "", by simp, by simp [hi]⟩
  | c :: cs, i, h => by
    rw [utf8_ofList_cons] at h ⊢
    have hn : 0 < (utf8 (String.ofList [c])).length := by
      rw [utf8_ofList_singleton, List.length_map, String.length_utf8EncodeChar]
      exact Char.utf8Size_pos c
    rcases Nat.lt_trichotomy i (utf8 (String.ofList [c])).length with hlt | heq | hgt
    · by_cases h0 : i = 0
      · subst h0
        exact ⟨"", String.ofList [c] ++ String.ofList cs, by rw [utf8_empty, List.nil_append,
          utf8_append], by rw [utf8_empty]; rfl⟩
      · exfalso
        unfold isCharBoundary at h
        rw [ite_eq_right h0, ite_eq_right (by rw [List.length_append]; omega)] at h
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at h
        rw [utf8_ofList_singleton] at hlt h
        obtain ⟨a, rest, hE⟩ : ∃ a rest, String.utf8EncodeChar c = a :: rest := by
          cases hE : String.utf8EncodeChar c with
          | nil => rw [hE] at hlt; simp at hlt
          | cons a rest => exact ⟨a, rest, rfl⟩
        rw [hE] at hlt h
        simp only [List.length_map, List.length_cons] at hlt
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [List.map_cons, List.getElem?_cons_succ, List.getElem?_map,
          List.getElem?_eq_getElem (by omega)] at h
        have hm : rest[j] ∈ (String.utf8EncodeChar c).tail := by
          rw [hE, List.tail_cons]; exact List.getElem_mem _
        have hb := le_toNat_and_toNat_lt_of_mem_tail_utf8EncodeChar c _ hm
        simp only [Option.map_some, Option.getD_some, byte_val,
          Nat.mod_eq_of_lt (rest[j]).toNat_lt, decide_eq_true_eq] at h
        omega
    · exact ⟨String.ofList [c], String.ofList cs, rfl, heq.symm⟩
    · have h' : isCharBoundary (utf8 (String.ofList cs)) (i - (utf8 (String.ofList [c])).length)
          = true := by
        unfold isCharBoundary at h ⊢
        rw [ite_eq_right (by omega)] at h
        rw [ite_eq_right (by omega)]
        rw [List.length_append] at h
        by_cases hL : (utf8 (String.ofList cs)).length ≤ i - (utf8 (String.ofList [c])).length
        · rw [ite_eq_left (by omega)] at h
          rw [ite_eq_left hL]
          simp only [decide_eq_true_eq] at h ⊢
          omega
        · rw [ite_eq_right (by omega)] at h
          rw [ite_eq_right hL]
          rwa [List.getD_append_right _ _ _ _ (by omega)] at h
      obtain ⟨u, v, huv, hu⟩ := exists_utf8_ofList_eq_append_of_isCharBoundary cs _ h'
      refine ⟨String.ofList [c] ++ u, v, ?_, ?_⟩
      · rw [huv, utf8_append, List.append_assoc]
      · rw [utf8_append, List.length_append, hu]; omega


/-- **A char boundary splits a `&str` into two `&str`s**: at a byte index `i` that
`str::is_char_boundary` accepts, the UTF-8 bytes of `t` are those of two strings, the first with
`i` bytes. -/
theorem exists_utf8_eq_append_of_isCharBoundary {t : String} {i : Nat}
    (h : isCharBoundary (utf8 t) i = true) :
    ∃ u v, utf8 t = utf8 u ++ utf8 v ∧ (utf8 u).length = i := by
  have := exists_utf8_ofList_eq_append_of_isCharBoundary t.toList i
  rw [String.ofList_toList] at this
  exact this h

/-- The bytes of a `&str` before a char boundary are a `&str` (the first part of `split_at`,
`split_at_checked`). -/
theorem exists_eq_utf8_take_of_isCharBoundary {t : String} {i : Nat}
    (h : isCharBoundary (utf8 t) i = true) : ∃ u, (utf8 t).take i = utf8 u := by
  obtain ⟨u, v, huv, hu⟩ := exists_utf8_eq_append_of_isCharBoundary h
  exact ⟨u, by rw [huv, ← hu, List.take_left]⟩

/-- The bytes of a `&str` from a char boundary are a `&str` (the second part of `split_at`,
`split_at_checked`). -/
theorem exists_eq_utf8_drop_of_isCharBoundary {t : String} {i : Nat}
    (h : isCharBoundary (utf8 t) i = true) : ∃ v, (utf8 t).drop i = utf8 v := by
  obtain ⟨u, v, huv, hu⟩ := exists_utf8_eq_append_of_isCharBoundary h
  exact ⟨v, by rw [huv, ← hu, List.drop_left]⟩

/-- An index at an ASCII byte is a char boundary. -/
theorem isCharBoundary_of_val_lt {l : List U8} {i : Nat} (hi : i < l.length)
    (hb : l[i].val < 128) : isCharBoundary l i = true := by
  unfold isCharBoundary
  split
  · rfl
  · rw [ite_eq_right (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
    exact decide_eq_true (Or.inl hb)

/-- The index after any bytes that the UTF-8 bytes of a string follow is a char boundary (the
first byte of a string is not a continuation byte). -/
theorem isCharBoundary_append_utf8 (r : List U8) (s : String) :
    isCharBoundary (r ++ utf8 s) r.length = true := by
  unfold isCharBoundary
  split
  · rfl
  · rename_i h0
    split
    · rename_i hle
      rw [List.length_append] at hle ⊢
      have : (utf8 s).length = 0 := by omega
      exact decide_eq_true (by omega)
    · rename_i hlt
      rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
      have hs : s.toList ≠ [] := by
        intro hn
        rw [← String.ofList_toList (s := s), hn, utf8_ofList_nil] at hlt
        simp at hlt
      obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil hs
      rw [← String.ofList_toList (s := s), hc, utf8_ofList_cons, utf8_ofList_singleton]
      obtain ⟨a, rest, hE⟩ : ∃ a rest, String.utf8EncodeChar c = a :: rest := by
        cases hE : String.utf8EncodeChar c with
        | nil =>
          have := Char.utf8Size_pos c
          rw [← String.length_utf8EncodeChar, hE] at this; simp at this
        | cons a rest => exact ⟨a, rest, rfl⟩
      have ha := toNat_lt_or_le_of_mem_head?_utf8EncodeChar c a (by rw [hE]; rfl)
      rw [hE, List.map_cons, List.cons_append, List.getD_cons_zero, byte_val,
        Nat.mod_eq_of_lt a.toNat_lt]
      exact decide_eq_true ha

/-- The bytes of a `&str` before a `&str` suffix are a `&str`. -/
theorem exists_eq_utf8_of_append_utf8_eq_utf8 {r : List U8} {s t : String}
    (h : r ++ utf8 s = utf8 t) : ∃ u, r = utf8 u := by
  have hb := isCharBoundary_append_utf8 r s
  rw [h] at hb
  obtain ⟨u, hu⟩ := exists_eq_utf8_take_of_isCharBoundary hb
  exact ⟨u, by rw [← hu, ← h, List.take_left]⟩

/-- The bytes of a `&str` after a `&str` prefix are a `&str` (UTF-8 is prefix-free:
`List.isPrefix_of_utf8Encode_append_eq_utf8Encode`). -/
theorem exists_eq_utf8_of_utf8_append_eq_utf8 {p t : String} {r : List U8}
    (h : utf8 p ++ r = utf8 t) : ∃ u, r = utf8 u := by
  have hb : p.toList.utf8Encode ++ (⟨(r.map (fun b => b.val.toUInt8)).toArray⟩ : ByteArray) =
      t.toList.utf8Encode := by
    rw [← String.toByteArray_ofList, ← String.toByteArray_ofList, String.ofList_toList,
      String.ofList_toList, ← bytes_utf8, ← bytes_utf8, ← h]
    apply ByteArray.ext
    simp [ByteArray.data_append, List.map_append]
  obtain ⟨m, hm⟩ := List.isPrefix_of_utf8Encode_append_eq_utf8Encode _ hb
  refine ⟨String.ofList m, ?_⟩
  have ht : t = p ++ String.ofList m := by
    rw [← String.ofList_toList (s := t), ← hm, String.ofList_append, String.ofList_toList]
  rw [ht, utf8_append] at h
  exact List.append_cancel_left h

/-- **`strip_prefix` gives a `&str`**: the bytes of `t` after a prefix `p` are a `&str`
(`prim::strip_prefix_spec`). -/
theorem exists_eq_utf8_drop_of_prefix {p t : String} (h : utf8 p <+: utf8 t) :
    ∃ u, (utf8 t).drop (utf8 p).length = utf8 u := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨u, hu⟩ := exists_eq_utf8_of_utf8_append_eq_utf8 hr
  exact ⟨u, by rw [← hr, List.drop_left, hu]⟩

/-- **`strip_suffix` gives a `&str`**: the bytes of `t` before a suffix `s` are a `&str`
(`prim::strip_suffix_spec`). -/
theorem exists_eq_utf8_take_of_suffix {s t : String} (h : utf8 s <:+ utf8 t) :
    ∃ u, (utf8 t).take ((utf8 t).length - (utf8 s).length) = utf8 u := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨u, hu⟩ := exists_eq_utf8_of_append_utf8_eq_utf8 hr
  refine ⟨u, ?_⟩
  rw [← hr, List.length_append, Nat.add_sub_cancel, List.take_left, hu]

/-- The index after an ASCII byte of a `&str` is a char boundary. -/
theorem isCharBoundary_add_one_of_val_lt {t : String} {i : Nat} (hi : i < (utf8 t).length)
    (hb : ((utf8 t)[i]).val < 128) : isCharBoundary (utf8 t) (i + 1) = true := by
  obtain ⟨u, hu⟩ := exists_eq_utf8_take_of_isCharBoundary (isCharBoundary_of_val_lt hi hb)
  have hb' : ∀ b ∈ [(utf8 t)[i]], b.val < 128 := by
    intro b hm; rw [List.mem_singleton] at hm; rw [hm]; exact hb
  have htake : (utf8 t).take (i + 1) =
      utf8 (u ++ String.ofList ([(utf8 t)[i]].map (fun b => Char.ofNat b.val))) := by
    rw [utf8_append, utf8_ofList_ascii _ hb', ← hu, List.take_add_one,
      List.getElem?_eq_getElem hi]
    rfl
  obtain ⟨v, hv⟩ := exists_eq_utf8_of_utf8_append_eq_utf8
    (by rw [← htake, List.take_append_drop] : utf8 (u ++ String.ofList
      ([(utf8 t)[i]].map (fun b => Char.ofNat b.val))) ++ (utf8 t).drop (i + 1) = utf8 t)
  have hlen : ((utf8 t).take (i + 1)).length = i + 1 := by
    rw [List.length_take]; omega
  have := isCharBoundary_append_utf8 ((utf8 t).take (i + 1)) v
  rwa [← hv, List.take_append_drop, hlen] at this

/-- The bytes of a `&str` before an ASCII byte are a `&str`. -/
theorem exists_eq_utf8_take_of_val_lt {t : String} {i : Nat} (hi : i < (utf8 t).length)
    (hb : ((utf8 t)[i]).val < 128) : ∃ u, (utf8 t).take i = utf8 u :=
  exists_eq_utf8_take_of_isCharBoundary (isCharBoundary_of_val_lt hi hb)

/-- The bytes of a `&str` after an ASCII byte are a `&str` (e.g. after a `%`). -/
theorem exists_eq_utf8_drop_add_one_of_val_lt {t : String} {i : Nat} (hi : i < (utf8 t).length)
    (hb : ((utf8 t)[i]).val < 128) : ∃ u, (utf8 t).drop (i + 1) = utf8 u :=
  exists_eq_utf8_drop_of_isCharBoundary (isCharBoundary_add_one_of_val_lt hi hb)

/-- **`split_once` at an ASCII byte gives two `&str`s**: for the first byte that an ASCII
predicate accepts (e.g. `%` for `prim::split_once_percent_spec`, `?`/`#` for
`prim::find_query_or_fragment_spec`), the bytes before it and the bytes after it are `&str`s. -/
theorem exists_eq_utf8_take_and_drop_add_one_of_findIdx?_eq_some {t : String} {p : U8 → Bool}
    (hp : ∀ b, p b = true → b.val < 128) {i : Nat} (h : (utf8 t).findIdx? p = some i) :
    (∃ u, (utf8 t).take i = utf8 u) ∧ ∃ v, (utf8 t).drop (i + 1) = utf8 v := by
  obtain ⟨hi, hpi, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  exact ⟨exists_eq_utf8_take_of_val_lt hi (hp _ hpi),
    exists_eq_utf8_drop_add_one_of_val_lt hi (hp _ hpi)⟩

/-! ### `serde_json::Map` -/

/-- No byte list is less than itself. -/
theorem bytesLt_self : ∀ l : List U8, bytesLt l l = false
  | [] => rfl
  | a :: l => by
    rw [bytesLt, ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl]
    exact bytesLt_self l

/-- `bytesLt` is transitive. -/
theorem bytesLt_trans : ∀ {a b c : List U8}, bytesLt a b = true → bytesLt b c = true →
    bytesLt a c = true
  | [], [], _, h, _ => by simp [bytesLt] at h
  | [], _ :: _, [], _, h => by simp [bytesLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [bytesLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [bytesLt] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [bytesLt] at h1 h2 ⊢
    by_cases hxy : x.val < y.val
    · by_cases hyz : y.val < z.val
      · rw [ite_eq_left (by omega)]
      · rw [ite_eq_right hyz] at h2
        by_cases hyz' : y.val = z.val
        · rw [ite_eq_left (by omega)]
        · rw [ite_eq_right hyz'] at h2; exact absurd h2 Bool.false_ne_true
    · rw [ite_eq_right hxy] at h1
      by_cases hxy' : x.val = y.val
      · rw [ite_eq_left hxy'] at h1
        by_cases hyz : y.val < z.val
        · rw [ite_eq_left (by omega)]
        · rw [ite_eq_right hyz] at h2
          by_cases hyz' : y.val = z.val
          · rw [ite_eq_left hyz'] at h2
            rw [ite_eq_right (by omega), ite_eq_left (by omega)]
            exact bytesLt_trans h1 h2
          · rw [ite_eq_right hyz'] at h2; exact absurd h2 Bool.false_ne_true
      · rw [ite_eq_right hxy'] at h1; exact absurd h1 Bool.false_ne_true

/-- Of two distinct byte lists, one is less than the other. -/
theorem bytesLt_or_bytesLt_of_ne : ∀ {a b : List U8}, a ≠ b →
    bytesLt a b = true ∨ bytesLt b a = true
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => Or.inl rfl
  | _ :: _, [], _ => Or.inr rfl
  | x :: xs, y :: ys, h => by
    simp only [bytesLt]
    by_cases hxy : x.val < y.val
    · exact Or.inl (ite_eq_left hxy)
    · by_cases hyx : y.val < x.val
      · exact Or.inr (ite_eq_left hyx)
      · have hv : x.val = y.val := by omega
        rw [ite_eq_right hxy, ite_eq_left hv, ite_eq_right hyx, ite_eq_left hv.symm]
        have hx : x = y := by
          cases x; cases y; simp only [UScalar.val] at hv; congr; exact BitVec.eq_of_toNat_eq hv
        have hne : xs ≠ ys := fun he => h (by rw [hx, he])
        exact bytesLt_or_bytesLt_of_ne hne

/-- The entries of a `serde_json::Map` are sorted: each key is less than every later key in
Rust's `String` order (`ExtModel.bytesLt` on the UTF-8 bytes), so the keys are distinct. -/
def SortedByKey {V : Type} (l : List (String × V)) : Prop :=
  l.Pairwise (fun a b => bytesLt (utf8 a.1) (utf8 b.1) = true)

/-- Every key of `mapInsert k v l` is `k` or a key of `l`. -/
theorem forall_mem_mapInsert {V : Type} (k : String) (v : V) (P : String → Prop) (hk : P k) :
    ∀ l : List (String × V), (∀ e ∈ l, P e.1) → ∀ e ∈ (mapInsert k v l).2, P e.1
  | [], _, e, he => by
    simp only [mapInsert, List.mem_singleton] at he; rw [he]; exact hk
  | (k', v') :: rest, hl, e, he => by
    rw [mapInsert] at he
    split at he
    · rcases List.mem_cons.1 he with rfl | he
      · exact hl (k', v') List.mem_cons_self
      · exact hl e (List.mem_cons_of_mem _ he)
    · split at he
      · rcases List.mem_cons.1 he with rfl | he
        · exact hk
        · exact hl e he
      · rcases List.mem_cons.1 he with rfl | he
        · exact hl (k', v') List.mem_cons_self
        · exact forall_mem_mapInsert k v P hk rest
            (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) e he

/-- `mapInsert` keeps the entries sorted by key. -/
theorem sortedByKey_mapInsert {V : Type} (k : String) (v : V) :
    ∀ l : List (String × V), SortedByKey l → SortedByKey (mapInsert k v l).2
  | [], _ => List.pairwise_singleton _ _
  | (k', v') :: rest, hl => by
    unfold SortedByKey at hl ⊢
    rw [List.pairwise_cons] at hl
    rw [mapInsert]
    split
    · rename_i h
      exact List.pairwise_cons.2 ⟨fun e he => hl.1 e he, hl.2⟩
    · rename_i hne
      split
      · rename_i hlt
        refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 hl⟩
        intro e he
        rcases List.mem_cons.1 he with rfl | he
        · exact hlt
        · exact bytesLt_trans hlt (hl.1 e he)
      · rename_i hnlt
        have hlt : bytesLt (utf8 k') (utf8 k) = true := by
          rcases bytesLt_or_bytesLt_of_ne (a := utf8 k') (b := utf8 k)
              (fun h => hne (utf8_injective h)) with h | h
          · exact h
          · exact absurd h hnlt
        refine List.pairwise_cons.2 ⟨?_, sortedByKey_mapInsert k v rest hl.2⟩
        exact forall_mem_mapInsert k v (fun x => bytesLt (utf8 k') (utf8 x) = true) hlt rest hl.1

/-- On sorted entries, `mapInsert` returns the old value of the key (`none` if it has none). -/
theorem mapInsert_fst_of_sortedByKey {V : Type} (k : String) (v : V) :
    ∀ l : List (String × V), SortedByKey l →
      (mapInsert k v l).1 = (l.find? (fun e => e.1 == k)).map Prod.snd
  | [], _ => rfl
  | (k', v') :: rest, hl => by
    unfold SortedByKey at hl
    rw [List.pairwise_cons] at hl
    rw [mapInsert]
    by_cases h : k' = k
    · simp [h]
    · have hb : (k' == k) = false := beq_eq_false_iff_ne.2 h
      rw [ite_eq_right h, List.find?_cons, hb]
      split
      · rename_i hlt
        dsimp only
        rw [List.find?_eq_none.2, Option.map_none]
        intro e he hek
        have hek' : e.1 = k := beq_iff_eq.1 hek
        have := bytesLt_trans hlt (hl.1 e he)
        rw [hek', bytesLt_self] at this
        exact Bool.false_ne_true this
      · exact mapInsert_fst_of_sortedByKey k v rest hl.2

end Proofs.External.Skill

/-! ## The `skill::prim` wrappers -/

namespace model.skill.prim

open ExtModel Proofs.External.Utf8 Proofs.External.Skill

/-- **Spec theorem for `rmcp::model::skill::prim::sha256`**

Always succeeds with the SHA-256 digest `sha256 bytes` (an opaque value). -/
@[step]
theorem sha256_spec (bytes : Slice U8) :
    sha256 bytes ⦃ (result : Std.Array U8 32#usize) =>
      result = ExtModel.sha256 bytes.val ⦄ := by
  simp only [sha256, WP.spec_ok]

/-- **Spec theorem for `rmcp::model::skill::prim::find_query_or_fragment`**

Always succeeds with the index of the first `?` or `#` byte, `none` if there is none. -/
@[step]
theorem find_query_or_fragment_spec (s : Str) :
    find_query_or_fragment s ⦃ (result : Option Usize) =>
      result.map (·.val) = s.val.findIdx? (fun b => decide (b.val = 63 ∨ b.val = 35)) ⦄ := by
  simp only [find_query_or_fragment, WP.spec_ok, Option.map_map]
  cases h : s.val.findIdx? (fun b => decide (b.val = 63 ∨ b.val = 35)) with
  | none => rfl
  | some i =>
    have hi : i < s.val.length := (List.findIdx?_eq_some_iff_findIdx_eq.1 h).1
    simp only [Option.map_some, Function.comp_apply]
    rw [usize_val (by have := s.property; omega)]

/-- **Spec theorem for `rmcp::model::skill::prim::strip_suffix`**

Always succeeds: `some` of the bytes before `suffix` if `s` ends with `suffix`, otherwise
`none`. -/
@[step]
theorem strip_suffix_spec (s : Str) (suffix : Str) :
    strip_suffix s suffix ⦃ (result : Option Str) =>
      result.map (·.val) = if suffix.val <:+ s.val then
        some (s.val.take (s.val.length - suffix.val.length)) else none ⦄ := by
  unfold strip_suffix
  have hiff : s.val.drop (s.val.length - suffix.val.length) = suffix.val ↔ suffix.val <:+ s.val :=
    ⟨fun h => List.suffix_iff_eq_drop.2 h.symm, fun h => (List.suffix_iff_eq_drop.1 h).symm⟩
  by_cases h : suffix.val <:+ s.val
  · rw [ite_eq_left (hiff.2 h)]
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_left h]
    exact congrArg some (Slice.from_val _ _)
  · rw [ite_eq_right (mt hiff.1 h)]
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_right h, Option.map_none]

/-- **Spec theorem for `rmcp::model::skill::prim::strip_prefix`**

Always succeeds: `some` of the bytes after `prefix` if `s` starts with `prefix`, otherwise
`none`. -/
@[step]
theorem strip_prefix_spec (s : Str) («prefix» : Str) :
    strip_prefix s «prefix» ⦃ (result : Option Str) =>
      result.map (·.val) = if «prefix».val <+: s.val then
        some (s.val.drop «prefix».val.length) else none ⦄ := by
  unfold strip_prefix
  have hiff : s.val.take «prefix».val.length = «prefix».val ↔ «prefix».val <+: s.val :=
    ⟨fun h => List.prefix_iff_eq_take.2 h.symm, fun h => (List.prefix_iff_eq_take.1 h).symm⟩
  by_cases h : «prefix».val <+: s.val
  · rw [ite_eq_left (hiff.2 h)]
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_left h]
    exact congrArg some (Slice.from_val _ _)
  · rw [ite_eq_right (mt hiff.1 h)]
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_right h, Option.map_none]

/-- **Spec theorem for `rmcp::model::skill::prim::last_slash_segment`**

Always succeeds with the bytes after the last `/`, all of `s` if there is none. -/
@[step]
theorem last_slash_segment_spec (s : Str) :
    last_slash_segment s ⦃ (result : Str) =>
      result.val = s.val.drop (lastSegmentStart (byte 47) s.val) ⦄ := by
  exact (WP.spec_ok (p := fun result : Str =>
    result.val = s.val.drop (lastSegmentStart (byte 47) s.val)) _).2 (Slice.from_val _ _)

/-- **Spec theorem for `rmcp::model::skill::prim::split_slash`**

For parts that are UTF-8 (as every part of a Rust `&str` split at `/` is) and a `Vec` that fits,
succeeds with the strings whose bytes are the parts of `s` between the `/` bytes. -/
@[step]
theorem split_slash_spec (s : Str)
    (hutf8 : ∀ p ∈ splitBytes (byte 47) s.val, ∃ t, p = utf8 t)
    (hlen : 24 * (splitBytes (byte 47) s.val).length ≤ maxStringBytes) :
    split_slash s ⦃ (result : alloc.vec.Vec String) =>
      result.val.map utf8 = splitBytes (byte 47) s.val ⦄ := by
  obtain ⟨strs, hs, hm⟩ := exists_stringsOfBytes_eq_ok _ hutf8
  have hl : 24 * strs.length ≤ maxStringBytes := by
    rw [← List.length_map (f := utf8), hm]; exact hlen
  obtain ⟨v, hv, hvv⟩ := exists_collectVec_eq_ok 24 strs (by decide) hl
  simp only [split_slash, hs, bind_ok, hv, WP.spec_ok, hvv, hm]

/-- `split_slash` on the bytes of a string `t` (every Rust `&str`): its parts are UTF-8
(`exists_eq_utf8_of_mem_splitBytes_utf8`), so only the `Vec` size is a premise. -/
theorem split_slash_spec_of_eq_utf8 (s : Str) (t : String) (ht : s.val = utf8 t)
    (hlen : 24 * (splitBytes (byte 47) s.val).length ≤ maxStringBytes) :
    split_slash s ⦃ (result : alloc.vec.Vec String) =>
      result.val.map utf8 = splitBytes (byte 47) s.val ⦄ :=
  split_slash_spec s (by rw [ht]; exact exists_eq_utf8_of_mem_splitBytes_utf8 _ (by decide) t)
    hlen

/-- **Spec theorem for `rmcp::model::skill::prim::join_slash`**

Succeeds with the segments joined by `/` if the result fits in a `String`. -/
@[step]
theorem join_slash_spec (segments : alloc.vec.Vec String)
    (h : (String.intercalate "/" segments.val).utf8ByteSize ≤ maxStringBytes) :
    join_slash segments ⦃ (result : String) =>
      result = String.intercalate "/" segments.val ⦄ := by
  simp only [join_slash, growString, ite_eq_left h, WP.spec_ok]

/-- **Spec theorem for `rmcp::model::skill::prim::split_once_percent`**

Always succeeds: `some` of the bytes before and after the first `%`, `none` if there is
none. -/
@[step]
theorem split_once_percent_spec (s : Str) :
    split_once_percent s ⦃ (result : Option (Str × Str)) =>
      result.map (fun p => (p.1.val, p.2.val)) =
        (s.val.findIdx? (fun b => decide (b.val = 37))).map
          (fun i => (s.val.take i, s.val.drop (i + 1))) ⦄ := by
  unfold split_once_percent
  split <;> rename_i h <;> simp only [h, WP.spec_ok, Option.map_none, Option.map_some,
    Slice.from_val]

/-- **Spec theorem for `rmcp::model::skill::prim::split_percent`**

As `split_slash_spec`, at the `%` bytes. -/
@[step]
theorem split_percent_spec (s : Str)
    (hutf8 : ∀ p ∈ splitBytes (byte 37) s.val, ∃ t, p = utf8 t)
    (hlen : 24 * (splitBytes (byte 37) s.val).length ≤ maxStringBytes) :
    split_percent s ⦃ (result : alloc.vec.Vec String) =>
      result.val.map utf8 = splitBytes (byte 37) s.val ⦄ := by
  obtain ⟨strs, hs, hm⟩ := exists_stringsOfBytes_eq_ok _ hutf8
  have hl : 24 * strs.length ≤ maxStringBytes := by
    rw [← List.length_map (f := utf8), hm]; exact hlen
  obtain ⟨v, hv, hvv⟩ := exists_collectVec_eq_ok 24 strs (by decide) hl
  simp only [split_percent, hs, bind_ok, hv, WP.spec_ok, hvv, hm]

/-- `split_percent` on the bytes of a string `t` (every Rust `&str`), as
`split_slash_spec_of_eq_utf8`. -/
theorem split_percent_spec_of_eq_utf8 (s : Str) (t : String) (ht : s.val = utf8 t)
    (hlen : 24 * (splitBytes (byte 37) s.val).length ≤ maxStringBytes) :
    split_percent s ⦃ (result : alloc.vec.Vec String) =>
      result.val.map utf8 = splitBytes (byte 37) s.val ⦄ :=
  split_percent_spec s (by rw [ht]; exact exists_eq_utf8_of_mem_splitBytes_utf8 _ (by decide) t)
    hlen

/-- **Spec theorem for `rmcp::model::skill::prim::percent_encode_controls`**

If the encoded string fits in a `String`, succeeds with a `Cow` whose bytes are the
percent-encoding of the controls and non-ASCII bytes of `value`; it is `value` itself, borrowed,
when no byte needs encoding. -/
@[step]
theorem percent_encode_controls_spec (value : Str)
    (h : (percentEncodeControls value.val).length ≤ maxStringBytes) :
    percent_encode_controls value ⦃ (result : alloc.borrow.Cow Str String) =>
      cowStrBytes result = percentEncodeControls value.val ∧
        ((∀ b ∈ value.val, isControlOrNonAscii b = false) →
          result = alloc.borrow.Cow.Borrowed value) ⦄ := by
  unfold percent_encode_controls
  by_cases hall : value.val.all (fun b => !isControlOrNonAscii b) = true
  · have hall' : ∀ b ∈ value.val, isControlOrNonAscii b = false := by
      intro b hb; have := List.all_eq_true.1 hall b hb; simpa using this
    rw [ite_eq_left hall, WP.spec_ok]
    exact ⟨(percentEncodeControls_eq_self_of_forall _ hall').symm, fun _ => rfl⟩
  · have hnot : ¬ ∀ b ∈ value.val, isControlOrNonAscii b = false := by
      intro h'; apply hall; rw [List.all_eq_true]; intro b hb; simp [h' b hb]
    rw [ite_eq_right hall]
    split
    · rename_i b hb
      rw [WP.spec_ok]
      refine ⟨?_, fun h' => absurd h' hnot⟩
      have hb' : isControlOrNonAscii b = true := by
        rw [hb] at hnot; simpa using hnot
      simp only [cowStrBytes, Slice.from_val, hb, percentEncodeControls, hb', ↓reduceIte,
        List.append_nil]
    · have hascii := val_lt_128_of_mem_percentEncodeControls value.val
      have hu : utf8 (String.ofList ((percentEncodeControls value.val).map
          (fun b => Char.ofNat b.val))) = percentEncodeControls value.val :=
        utf8_ofList_ascii _ hascii
      have hsz : (String.ofList ((percentEncodeControls value.val).map
          (fun b => Char.ofNat b.val))).utf8ByteSize ≤ maxStringBytes := by
        rw [← length_utf8, hu]; exact h
      simp only [growString, ite_eq_left hsz, bind_ok, WP.spec_ok, cowStrBytes, hu, true_and]
      exact fun h' => absurd h' hnot

/-- **Spec theorem for `rmcp::model::skill::prim::percent_decode_utf8`**

Always succeeds: `some s` exactly when the percent-decoded bytes are the UTF-8 encoding of
`s`. -/
@[step]
theorem percent_decode_utf8_spec (s : Str) :
    percent_decode_utf8 s ⦃ (result : Option String) =>
      result = strOfBytes? (percentDecode s.val) ⦄ := by
  simp only [percent_decode_utf8, WP.spec_ok]

/-- **Spec theorem for `rmcp::model::skill::prim::nfkc`**

For the bytes of a string `t` (as every Rust `&str` is) and a `Vec` that fits, succeeds with
the characters of the NFKC form of `t` (an opaque value). -/
@[step]
theorem nfkc_spec (s : Str) (t : String) (ht : s.val = utf8 t)
    (hlen : 4 * (ExtModel.nfkc t.toList).length ≤ maxStringBytes) :
    nfkc s ⦃ (result : alloc.vec.Vec Char) => result.val = ExtModel.nfkc t.toList ⦄ := by
  obtain ⟨v, hv, hvv⟩ := exists_collectVec_eq_ok 4 _ (by decide) hlen
  simp only [nfkc, ht, strOfBytes?_utf8, hv, WP.spec_ok, hvv]

end model.skill.prim

/-! ## Standard library and crates -/

open ExtModel Proofs.External.Utf8 Proofs.External.Skill

/-- **Spec theorem for `unicode_general_category::get_general_category`**

Always succeeds with the general category `generalCategory c` (an opaque value). -/
@[step]
theorem unicode_general_category.category.get_general_category_spec (c : Char) :
    unicode_general_category.category.get_general_category c
      ⦃ (result : rmcp.unicode_general_category.tables.GeneralCategory) =>
        result = generalCategory c ⦄ := by
  simp only [unicode_general_category.category.get_general_category, WP.spec_ok]

/-- **Spec theorem for `<[T; N] as IntoIterator>::into_iter`**

Always succeeds with the iterator over the whole array. -/
@[step]
theorem Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter_spec {T : Type}
    {N : Usize} (self : Std.Array T N) :
    Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter self
      ⦃ (result : core.array.iter.IntoIter T N) =>
        result.data = self ∧ result.aliveStart = 0 ∧ result.aliveEnd = N.val ⦄ := by
  simp only [Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter, WP.spec_ok,
    and_self]

/-- **Spec theorem for `<array::IntoIter<T, N> as Iterator>::next`**

Before the end of the alive range, yields the element at its start and moves the start one on;
at the end, yields `None` and leaves the iterator unchanged. Never fails. -/
@[step]
theorem core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next_spec {T : Type}
    {N : Usize} [Inhabited T] (it : core.array.iter.IntoIter T N) :
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next it
      ⦃ (result : Option T × core.array.iter.IntoIter T N) =>
        (it.aliveStart < it.aliveEnd ∧ result.1 = some it.data.val[it.aliveStart]! ∧
          result.2.data = it.data ∧ result.2.aliveStart = it.aliveStart + 1 ∧
          result.2.aliveEnd = it.aliveEnd) ∨
        (it.aliveEnd ≤ it.aliveStart ∧ result = (none, it)) ⦄ := by
  unfold core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
  split
  · rename_i h
    rw [WP.spec_ok]
    have hlt : it.aliveStart < it.data.val.length := by
      have := it.data.property; have := it.aliveEnd_le; omega
    exact Or.inl ⟨h, by rw [getElem!_pos it.data.val it.aliveStart hlt], rfl, rfl, rfl⟩
  · rename_i h
    rw [WP.spec_ok]
    exact Or.inr ⟨Nat.not_lt.1 h, rfl⟩

/-- **Spec theorem for `bool::then_some`**: `Some t` if `self`, otherwise `None`. -/
@[step]
theorem core.bool.Bool.then_some_spec {T : Type} (self : Bool) (t : T) :
    core.bool.Bool.then_some self t ⦃ (result : Option T) =>
      result = if self then some t else none ⦄ := by
  cases self <;> simp only [core.bool.Bool.then_some, Bool.false_eq_true, ↓reduceIte,
    WP.spec_ok]

/-- **Spec theorem for `<char as From<u8>>::from`**: the character whose code point is the
byte's value. -/
@[step]
theorem Char.Insts.CoreConvertFromU8.from_spec (i : U8) :
    Char.Insts.CoreConvertFromU8.from i ⦃ (result : Char) =>
      result = Char.ofNat i.val ∧ result.toNat = i.val ⦄ := by
  simp only [Char.Insts.CoreConvertFromU8.from, WP.spec_ok, true_and]
  have : i.val < 256 := Proofs.External.Byte.val_lt i
  rw [Char.toNat_ofNat, ite_eq_left (by unfold Nat.isValidChar; omega)]

/-- **Spec theorem for `<char as PartialEq>::eq`**: equality of the characters. -/
@[step]
theorem Char.Insts.CoreCmpPartialEqChar.eq_spec (self : Char) (other : Char) :
    Char.Insts.CoreCmpPartialEqChar.eq self other ⦃ (result : Bool) =>
      (result = true ↔ self = other) ⦄ := by
  simp only [Char.Insts.CoreCmpPartialEqChar.eq, WP.spec_ok, decide_eq_true_eq]

/-- **Spec theorem for the default `Iterator::all`**

For an iterator whose `next` yields the elements of `rest it` in order (and no element when
`rest it` is empty) and a closure that computes `p` without changing its state, the result is
whether `p` holds for every remaining element. -/
theorem core.iter.traits.iterator.Iterator.all.default_spec {Self : Type} {F : Type}
    {Item : Type} (IteratorInst : core.iter.traits.iterator.Iterator Self Item)
    (FnMutInst : core.ops.function.FnMut F Item Bool) (rest : Self → List Item)
    (p : Item → Bool) (self : Self) (f : F)
    (hnext : ∀ it, IteratorInst.next it ⦃ (r : Option Item × Self) =>
      match r.1 with
      | none => rest it = []
      | some x => rest it = x :: rest r.2 ⦄)
    (hf : ∀ x, FnMutInst.call_mut f x = ok (p x, f)) :
    core.iter.traits.iterator.Iterator.all.default IteratorInst FnMutInst self f
      ⦃ (result : Bool × Self) => result.1 = (rest self).all p ⦄ := by
  unfold core.iter.traits.iterator.Iterator.all.default
  apply loop.spec_decr_nat (fun st : Self × F => (rest st.1).length)
    (fun st => st.2 = f ∧ (rest st.1).all p = (rest self).all p)
  · rintro ⟨it, g⟩ ⟨hg, hinv⟩
    dsimp only at hg hinv
    subst hg
    obtain ⟨⟨o, it'⟩, hr, hpost⟩ := Proofs.External.WP.exists_ok_of_spec (hnext it)
    dsimp only
    rw [hr, bind_ok]
    cases o with
    | none =>
      refine (WP.spec_ok _).2 ?_
      dsimp only at hpost ⊢
      rw [← hinv, hpost, List.all_nil]
    | some x =>
      dsimp only at hpost
      simp only [hf, bind_ok, uncurry_apply_pair]
      rw [hpost, List.all_cons] at hinv
      cases hpx : p x
      · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        rw [← hinv, hpx, Bool.false_and]
      · simp only [↓reduceIte, WP.spec_ok]
        refine ⟨⟨by trivial, ?_⟩, ?_⟩
        · rw [← hinv, hpx, Bool.true_and]
        · rw [hpost, List.length_cons]; omega
  · exact ⟨rfl, rfl⟩

/-- **Spec theorem for `<ParseIntError as Debug>::fmt`** (total model): `Ok(())` and the
formatter unchanged. -/
@[step]
theorem core.num.error.ParseIntError.Insts.CoreFmtDebug.fmt_spec
    (e : core.num.error.ParseIntError) (f : core.fmt.Formatter) :
    core.num.error.ParseIntError.Insts.CoreFmtDebug.fmt e f
      ⦃ (result : (core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) =>
        result = (core.result.Result.Ok (), f) ⦄ := by
  simp only [core.num.error.ParseIntError.Insts.CoreFmtDebug.fmt, WP.spec_ok]

/-- **Spec theorem for `u8::is_ascii_alphanumeric`**: `0`–`9`, `A`–`Z`, `a`–`z`. -/
@[step]
theorem core.num.U8.is_ascii_alphanumeric_spec (self : U8) :
    core.num.U8.is_ascii_alphanumeric self ⦃ (result : Bool) =>
      (result = true ↔ (48 ≤ self.val ∧ self.val ≤ 57) ∨
        (65 ≤ self.val ∧ self.val ≤ 90) ∨
        (97 ≤ self.val ∧ self.val ≤ 122)) ⦄ := by
  simp only [core.num.U8.is_ascii_alphanumeric, WP.spec_ok, decide_eq_true_eq]

/-- **Spec theorem for `u8::is_ascii_hexdigit`**: `0`–`9`, `A`–`F`, `a`–`f`. -/
@[step]
theorem core.num.U8.is_ascii_hexdigit_spec (self : U8) :
    core.num.U8.is_ascii_hexdigit self ⦃ (result : Bool) =>
      (result = true ↔ (48 ≤ self.val ∧ self.val ≤ 57) ∨
        (65 ≤ self.val ∧ self.val ≤ 70) ∨
        (97 ≤ self.val ∧ self.val ≤ 102)) ⦄ := by
  simp only [core.num.U8.is_ascii_hexdigit, WP.spec_ok, decide_eq_true_eq]

/-- **Spec theorem for `u8::from_str_radix`**

For a radix in `2..=36`, always succeeds: `Ok v` with `v` the number that `u8FromAscii` reads,
`Err` with the error kind it reports. -/
@[step]
theorem core.num.U8.from_str_radix_spec (src : Str) (radix : U32)
    (h : 2 ≤ radix.val ∧ radix.val ≤ 36) :
    core.num.U8.from_str_radix src radix
      ⦃ (result : core.result.Result U8 core.num.error.ParseIntError) =>
        match u8FromAscii radix.val src.val with
        | .ok v => ∃ x : U8, result = core.result.Result.Ok x ∧ x.val = v
        | .error kind => result = core.result.Result.Err { kind } ⦄ := by
  unfold core.num.U8.from_str_radix
  rw [ite_eq_right (by omega)]
  split <;> rename_i heq
  · rw [heq]
    simp only [WP.spec_ok, core.result.Result.Ok.injEq, exists_eq_left']
    rw [Proofs.External.Byte.byte_val]
    exact Nat.mod_eq_of_lt (Nat.lt_succ_of_le (Proofs.External.Skill.u8FromAscii_le heq))
  · rw [heq]; simp only [WP.spec_ok]

/-- `u8::from_str_radix` with a radix outside `2..=36` panics. -/
theorem core.num.U8.from_str_radix_fail (src : Str) (radix : U32)
    (h : radix.val < 2 ∨ 36 < radix.val) :
    core.num.U8.from_str_radix src radix = fail Error.panic := by
  rw [core.num.U8.from_str_radix, ite_eq_left h]

/-- **Spec theorem for `Option::as_deref`**

If `self` is `Some t` and the `Deref` instance returns `g t` on that `t`, `Some (g t)`; `None`
for `None` (`self.as_ref().map(Deref::deref)`, `core/src/option.rs`). Only the dereferenced
value is constrained, so the premise holds for instances that fail on other values. -/
theorem core.option.Option.as_deref_spec {T : Type} {Target : Type}
    (inst : core.ops.deref.Deref T Target) (g : T → Target) (self : Option T)
    (hderef : ∀ t, self = some t → inst.deref t ⦃ (r : Target) => r = g t ⦄) :
    core.option.Option.as_deref inst self ⦃ (result : Option Target) =>
      result = self.map g ⦄ := by
  cases self with
  | none => simp only [core.option.Option.as_deref, WP.spec_ok, Option.map_none]
  | some t =>
    obtain ⟨r, hr, hrg⟩ := Proofs.External.WP.exists_ok_of_spec (hderef t rfl)
    simp only [core.option.Option.as_deref, hr, bind_ok, WP.spec_ok, Option.map_some, hrg]

/-- `Option<String>::as_deref` (the instance of K01): the UTF-8 bytes of the string, for a
string of at most `Usize.max` bytes (as every Rust `String`). -/
@[step]
theorem core.option.Option.as_deref_string_spec (self : Option String)
    (h : ∀ t, self = some t → t.utf8ByteSize ≤ Usize.max) :
    core.option.Option.as_deref alloc.string.String.Insts.CoreOpsDerefDerefStr self
      ⦃ (result : Option Str) => result.map (·.val) = self.map utf8 ⦄ := by
  cases self with
  | none => simp only [core.option.Option.as_deref, WP.spec_ok, Option.map_none]
  | some t =>
    obtain ⟨r, hr, hrv⟩ := Proofs.External.WP.exists_ok_of_spec
      (alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec t (h t rfl))
    simp only [core.option.Option.as_deref, hr, bind_ok, WP.spec_ok, Option.map_some, hrv]

/-- **Spec theorem for `<Option<T> as Try>::branch`**: `Some v ↦ Continue v`,
`None ↦ Break None`. -/
@[step]
theorem core.option.Option.Insts.CoreOpsTry_traitTry.branch_spec {T : Type} (self : Option T) :
    core.option.Option.Insts.CoreOpsTry_traitTry.branch self
      ⦃ (result : core.ops.control_flow.ControlFlow (Option Never) T) =>
        result = match self with
          | some v => core.ops.control_flow.ControlFlow.Continue v
          | none => core.ops.control_flow.ControlFlow.Break none ⦄ := by
  cases self <;> simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch, WP.spec_ok]

/-- **Spec theorem for `<Option<T> as FromResidual<Option<!>>>::from_residual`**: `None`. -/
@[step]
theorem core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual_spec
    (T : Type) (residual : Option Never) :
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual T residual
      ⦃ (result : Option T) => result = none ⦄ := by
  match residual with
  | none =>
    simp only [core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,
      WP.spec_ok]
  | some n => exact nomatch n

/-- **Spec theorem for `<Bytes as Iterator>::all`**

For a closure that computes `p` without changing its state, the result is whether `p` holds
for every remaining byte. -/
theorem core.str.iter.Bytes.Insts.CoreIterTraitsIteratorIteratorU8.all_spec {F : Type}
    (inst : core.ops.function.FnMut F U8 Bool) (p : U8 → Bool) (self : core.str.iter.Bytes)
    (f : F) (hf : ∀ x, inst.call_mut f x = ok (p x, f)) :
    core.str.iter.Bytes.Insts.CoreIterTraitsIteratorIteratorU8.all inst self f
      ⦃ (result : Bool × core.str.iter.Bytes) =>
        result.1 = (self.inner.slice.val.drop self.inner.i).all p ⦄ := by
  obtain ⟨n, hn⟩ := exists_sliceIterAll_eq_ok inst p f hf (self.inner.slice.val.drop self.inner.i)
  simp only [core.str.iter.Bytes.Insts.CoreIterTraitsIteratorIteratorU8.all, hn, bind_ok]
  exact (WP.spec_ok _).2 rfl

/-- **Spec theorem for `str::is_empty`**: `true` exactly for no bytes. -/
@[step]
theorem core.str.Str.is_empty_spec (self : Str) :
    core.str.Str.is_empty self ⦃ (result : Bool) => (result = true ↔ self.val = []) ⦄ := by
  simp only [core.str.Str.is_empty, WP.spec_ok, List.isEmpty_iff]

/-- **Spec theorem for `str::split_at_checked`**: `some` of the bytes before and from `mid` if
`mid` is a char boundary, otherwise `none`. -/
@[step]
theorem core.str.Str.split_at_checked_spec (self : Str) (mid : Usize) :
    core.str.Str.split_at_checked self mid ⦃ (result : Option (Str × Str)) =>
      result.map (fun p => (p.1.val, p.2.val)) =
        if isCharBoundary self.val mid.val then
          some (self.val.take mid.val, self.val.drop mid.val) else none ⦄ := by
  unfold core.str.Str.split_at_checked
  split <;> simp only [WP.spec_ok, Option.map_some, Option.map_none, Slice.from_val]

/-- **Spec theorem for `str::split_at`**: at a char boundary, the bytes before and from `mid`
(otherwise it panics, `split_at_fail`). -/
@[step]
theorem core.str.Str.split_at_spec (self : Str) (mid : Usize)
    (h : isCharBoundary self.val mid.val = true) :
    core.str.Str.split_at self mid ⦃ (result : Str × Str) =>
      result.1.val = self.val.take mid.val ∧ result.2.val = self.val.drop mid.val ⦄ := by
  simp only [core.str.Str.split_at, h, ↓reduceIte, WP.spec_ok, Slice.from_val, and_self]

/-- `str::split_at` off a char boundary panics. -/
theorem core.str.Str.split_at_fail (self : Str) (mid : Usize)
    (h : isCharBoundary self.val mid.val = false) :
    core.str.Str.split_at self mid = fail Error.panic := by
  simp only [core.str.Str.split_at, h, Bool.false_eq_true, ↓reduceIte]

/-- **Spec theorem for `str::bytes`**: the byte iterator at the first byte. -/
@[step]
theorem core.str.Str.bytes_spec (self : Str) :
    core.str.Str.bytes self ⦃ (result : core.str.iter.Bytes) =>
      result.inner.slice = self ∧ result.inner.i = 0 ⦄ := by
  exact (WP.spec_ok _).2 ⟨rfl, rfl⟩

/-- **Spec theorem for `HashSet::with_capacity`**: the empty set. -/
@[step]
theorem std.collections.hash.set.HashSetTRandomStateGlobal.with_capacity_spec (T : Type)
    (capacity : Usize) :
    std.collections.hash.set.HashSetTRandomStateGlobal.with_capacity T capacity
      ⦃ (result : std.collections.hash.set.HashSet T std.hash.random.RandomState
          alloc.alloc.Global) => result.elements = [] ⦄ := by
  simp only [std.collections.hash.set.HashSetTRandomStateGlobal.with_capacity, WP.spec_ok]

/-- **Spec theorem for `HashSet::insert`**

For an `Eq` instance that decides equality: if `value` is present, `false` and the set
unchanged; otherwise `true` and `value` added. -/
theorem std.collections.hash.set.HashSet.insert_spec {T : Type} {S : Type} {A : Type}
    {Hasher : Type} (eqInst : core.cmp.Eq T) (hashInst : core.hash.Hash T)
    (buildHasherInst : core.hash.BuildHasher S Hasher)
    (self : std.collections.hash.set.HashSet T S A) (value : T)
    (heq : ∀ a b, eqInst.partialEqInst.eq a b ⦃ (r : Bool) => (r = true ↔ a = b) ⦄) :
    std.collections.hash.set.HashSet.insert eqInst hashInst buildHasherInst self value
      ⦃ (result : Bool × std.collections.hash.set.HashSet T S A) =>
        (value ∈ self.elements ∧ result = (false, self)) ∨
        (value ∉ self.elements ∧
          result = (true, { self with elements := self.elements ++ [value] })) ⦄ := by
  obtain ⟨b, hb, hbv⟩ := exists_listContainsEq_eq_ok eqInst value heq self.elements
  simp only [std.collections.hash.set.HashSet.insert, hb, bind_ok]
  cases b
  · rw [ite_eq_right Bool.false_ne_true]
    exact (WP.spec_ok _).2 (Or.inr ⟨fun h => absurd (hbv.2 h) Bool.false_ne_true, rfl⟩)
  · rw [ite_eq_left rfl]
    exact (WP.spec_ok _).2 (Or.inl ⟨hbv.1 rfl, rfl⟩)

/-- **Spec theorem for `Cow::into_owned`**

For a postcondition `P` that `to_owned` meets on a borrowed value and that an owned value
meets. -/
theorem alloc.borrow.Cow.into_owned_spec {B : Type} {Owned : Type}
    (inst : rmcp.alloc.borrow.ToOwned B Owned) (self : rmcp.alloc.borrow.Cow B Owned)
    (P : Owned → Prop)
    (hBorrowed : ∀ b, self = rmcp.alloc.borrow.Cow.Borrowed b → inst.to_owned b ⦃ P ⦄)
    (hOwned : ∀ o, self = rmcp.alloc.borrow.Cow.Owned o → P o) :
    alloc.borrow.Cow.into_owned inst self ⦃ P ⦄ := by
  cases self with
  | Borrowed b => exact hBorrowed b rfl
  | Owned o => simp only [alloc.borrow.Cow.into_owned, WP.spec_ok]; exact hOwned o rfl

/-- `Cow<str>::into_owned` for a `Cow` whose bytes are those of a string `t`: `t`. -/
theorem alloc.borrow.Cow.into_owned_str_spec (self : rmcp.alloc.borrow.Cow Str String)
    (t : String) (ht : cowStrBytes self = utf8 t) :
    alloc.borrow.Cow.into_owned rmcp.Str.Insts.AllocBorrowToOwnedString self
      ⦃ (result : String) => result = t ⦄ := by
  apply alloc.borrow.Cow.into_owned_spec
  · rintro b rfl
    simp only [cowStrBytes] at ht
    simp only [Str.Insts.AllocBorrowToOwnedString.to_owned, ht, strOfBytes?_utf8, WP.spec_ok]
  · rintro o rfl
    exact utf8_injective ht

/-- **Spec theorem for `<Cow<B> as Deref>::deref`**

For a postcondition `P` that a borrowed value meets and that `borrow` meets on an owned
value. -/
theorem alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref_spec {B : Type} {Owned : Type}
    (inst : rmcp.alloc.borrow.ToOwned B Owned) (self : rmcp.alloc.borrow.Cow B Owned)
    (P : B → Prop)
    (hBorrowed : ∀ b, self = rmcp.alloc.borrow.Cow.Borrowed b → P b)
    (hOwned : ∀ o, self = rmcp.alloc.borrow.Cow.Owned o →
      inst.coreborrowBorrowInst.borrow o ⦃ P ⦄) :
    alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref inst self ⦃ P ⦄ := by
  cases self with
  | Borrowed b =>
    simp only [alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref, WP.spec_ok]; exact hBorrowed b rfl
  | Owned o => exact hOwned o rfl

/-- `<Cow<str> as Deref>::deref`: the bytes the `Cow` holds (for an owned string of at most
`Usize.max` bytes, as every Rust `String` is). -/
theorem alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref_str_spec
    (self : rmcp.alloc.borrow.Cow Str String)
    (h : ∀ o, self = rmcp.alloc.borrow.Cow.Owned o → o.utf8ByteSize ≤ Usize.max) :
    alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref rmcp.Str.Insts.AllocBorrowToOwnedString self
      ⦃ (result : Str) => result.val = cowStrBytes self ⦄ := by
  apply alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref_spec
  · rintro b rfl; rfl
  · rintro o rfl
    exact alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec o (h o rfl)

/-- **Spec theorem for `str::to_ascii_uppercase`**: when the bytes with `a`–`z` mapped to
`A`–`Z` are the UTF-8 encoding of a string `u` (as they are for every Rust `&str`), the result
is `u`. -/
@[step]
theorem alloc.str.Str.to_ascii_uppercase_spec (self : Str) (u : String)
    (hu : self.val.map asciiUppercase = utf8 u) :
    alloc.str.Str.to_ascii_uppercase self ⦃ (result : String) =>
      result = u ∧ utf8 result = self.val.map asciiUppercase ⦄ := by
  simp only [alloc.str.Str.to_ascii_uppercase, hu, strOfBytes?_utf8, WP.spec_ok, and_self]

/-- `str::to_ascii_uppercase` on the bytes of a string `t` (every Rust `&str`): the mapped bytes
are UTF-8 (`exists_map_asciiUppercase_utf8_eq_utf8`), so the result is the string they encode. -/
theorem alloc.str.Str.to_ascii_uppercase_spec_of_eq_utf8 (self : Str) (t : String)
    (ht : self.val = utf8 t) :
    alloc.str.Str.to_ascii_uppercase self ⦃ (result : String) =>
      utf8 result = self.val.map asciiUppercase ⦄ := by
  obtain ⟨u, hu⟩ := exists_map_asciiUppercase_utf8_eq_utf8 t
  rw [← ht] at hu
  simp only [alloc.str.Str.to_ascii_uppercase, hu, strOfBytes?_utf8, WP.spec_ok]

/-- **Spec theorem for `<str as ToOwned>::to_owned`**: for the bytes of a string `t` (every
Rust `&str`), `t`. -/
@[step]
theorem Str.Insts.AllocBorrowToOwnedString.to_owned_spec (self : Str) (t : String)
    (ht : self.val = utf8 t) :
    Str.Insts.AllocBorrowToOwnedString.to_owned self ⦃ (result : String) => result = t ⦄ := by
  simp only [Str.Insts.AllocBorrowToOwnedString.to_owned, ht, strOfBytes?_utf8, WP.spec_ok]

/-- **Spec theorem for `<String as Borrow<str>>::borrow`**: the UTF-8 bytes of the string (at
most `Usize.max` bytes, as every Rust `String`). -/
@[step]
theorem alloc.string.String.Insts.CoreBorrowBorrowStr.borrow_spec (self : String)
    (h : self.utf8ByteSize ≤ Usize.max) :
    alloc.string.String.Insts.CoreBorrowBorrowStr.borrow self ⦃ (result : Str) =>
      result.val = utf8 self ⦄ :=
  alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec self h

/-- **Spec theorem for `String::as_str`**: the UTF-8 bytes of the string (at most `Usize.max`
bytes, as every Rust `String`). -/
@[step]
theorem alloc.string.String.as_str_spec (self : String) (h : self.utf8ByteSize ≤ Usize.max) :
    alloc.string.String.as_str self ⦃ (result : Str) => result.val = utf8 self ⦄ :=
  alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec self h

/-- **Spec theorem for `Vec::pop`**: `None` and the vector unchanged if it is empty; otherwise
the last element and the vector without it. -/
@[step]
theorem alloc.vec.Vec.pop_spec {T : Type} (A : Type) (self : alloc.vec.Vec T) :
    alloc.vec.Vec.pop A self ⦃ (result : Option T × alloc.vec.Vec T) =>
      result.1 = self.val.getLast? ∧ result.2.val = self.val.dropLast ⦄ := by
  unfold alloc.vec.Vec.pop
  split
  · rename_i h
    simp only [WP.spec_ok, h, List.getLast?_nil, List.dropLast_nil, and_self]
  · rename_i h
    simp only [WP.spec_ok, List.getLast?_eq_some_getLast h, alloc.vec.Vec.from_val, and_self]

/-- **Spec theorem for `serde_json::Map::new`**: the empty map. -/
@[step]
theorem serde_json.map.MapStringValue.new_spec :
    serde_json.map.MapStringValue.new
      ⦃ (result : serde_json.map.Map String serde_json.value.Value) =>
        result.entries = [] ⦄ := by
  simp only [serde_json.map.MapStringValue.new, WP.spec_ok]

/-- **Spec theorem for `serde_json::Map::insert`**: for entries sorted by key (every map built
by `Map::new` and `Map::insert`), returns the old value of `k` (`none` if `k` had none) and the
entries with `k` mapped to `v` at its sorted position (`ExtModel.mapInsert`), still sorted. -/
@[step]
theorem serde_json.map.MapStringValue.insert_spec
    (self : serde_json.map.Map String serde_json.value.Value) (k : String)
    (v : serde_json.value.Value) (hsorted : SortedByKey self.entries) :
    serde_json.map.MapStringValue.insert self k v
      ⦃ (result : Option serde_json.value.Value ×
          serde_json.map.Map String serde_json.value.Value) =>
        result.1 = (self.entries.find? (fun e => e.1 == k)).map Prod.snd ∧
          result.2.entries = (mapInsert k v self.entries).2 ∧ SortedByKey result.2.entries ⦄ := by
  simp only [serde_json.map.MapStringValue.insert, WP.spec_ok,
    mapInsert_fst_of_sortedByKey k v _ hsorted, sortedByKey_mapInsert k v _ hsorted, and_self]

/-! ## Evaluation of the models

Kernel evaluation (`decide`) of the exact models on small inputs; each value is the one Rust
computes (checked against the Rust documentation and the crate sources cited at each model). -/

namespace Proofs.External.Skill

/-- `%41` decodes to `A`; a `%` without two hexadecimal digits is kept; lowercase hex is
accepted; in `%%41` the first `%` is kept and `%41` is decoded. -/
example : percentDecode [37#u8, 52#u8, 49#u8, 37#u8, 55#u8] = [65#u8, 37#u8, 55#u8] := by
  decide

example : percentDecode [37#u8, 50#u8, 102#u8] = [47#u8] := by decide

example : percentDecode [37#u8, 37#u8, 52#u8, 49#u8] = [37#u8, 65#u8] := by decide

example : percentDecode [37#u8, 52#u8, 120#u8] = [37#u8, 52#u8, 120#u8] := by decide

example : percentDecode [37#u8, 52#u8, 37#u8, 52#u8, 49#u8] = [37#u8, 52#u8, 65#u8] := by decide

/-- `u8::from_str_radix("ff", 16) = Ok(255)`, `("100", 16)` overflows, `("1g", 16)` is an
invalid digit, `("+7", 10) = Ok(7)`, `("-1", 10)` is an invalid digit, `("", 10)` is empty. -/
example : u8FromAscii 16 [102#u8, 102#u8] = .ok 255 := by rfl

example : u8FromAscii 16 [49#u8, 48#u8, 48#u8] = .error .PosOverflow := by rfl

example : u8FromAscii 16 [49#u8, 103#u8] = .error .InvalidDigit := by rfl

example : u8FromAscii 10 [43#u8, 55#u8] = .ok 7 := by rfl

example : u8FromAscii 10 [45#u8, 49#u8] = .error .InvalidDigit := by rfl

example : u8FromAscii 10 [] = .error .Empty := by rfl

/-- `"a/b//c".split('/')` is `["a", "b", "", "c"]`; `"".split('/')` is `[""]`. -/
example : splitBytes 47#u8 [97#u8, 47#u8, 98#u8, 47#u8, 47#u8, 99#u8] =
    [[97#u8], [98#u8], [], [99#u8]] := by decide

example : splitBytes 47#u8 [] = [[]] := by decide

/-- `"a/bc".rsplit('/').next()` is `"bc"` (from index 2); `"ab/"` gives `""` (index 3). -/
example : lastSegmentStart 47#u8 [97#u8, 47#u8, 98#u8, 99#u8] = 2 := by decide

example : lastSegmentStart 47#u8 [97#u8, 98#u8, 47#u8] = 3 := by decide

/-- `utf8_percent_encode("a\n", CONTROLS)` is `"a%0A"`. -/
example : percentEncodeControls [97#u8, 10#u8] = [97#u8, 37#u8, 48#u8, 65#u8] := by decide

/-- Rust's `String` order: `"a" < "b"`, `"a" < "ab"`, `"B" < "a"` (bytes 66 < 97), `"z" < "é"`
(122 < 195); no list is less than itself. -/
example : bytesLt [97#u8] [98#u8] = true ∧ bytesLt [97#u8] [97#u8, 98#u8] = true ∧
    bytesLt [66#u8] [97#u8] = true ∧ bytesLt [122#u8] [195#u8, 169#u8] = true ∧
    bytesLt [97#u8, 98#u8] [97#u8, 98#u8] = false := by decide

/-- `BTreeMap::insert` into the sorted entries: a new key goes to its position in Rust's
`String` order (`"B" < "a" < "b" < "c"`), an existing key keeps its position and gets the new
value, and the old value is returned. (Kernel reduction: the `String` literals are encoded by
`utf8`.) -/
example : mapInsert "b" 1 [("a", 0), ("c", 2)] = (none, [("a", 0), ("b", 1), ("c", 2)]) := by
  decide +kernel

example : mapInsert "c" 5 [("a", 0), ("c", 2)] = (some 2, [("a", 0), ("c", 5)]) := by
  decide +kernel

example : mapInsert "B" 1 [("a", 0)] = (none, [("B", 1), ("a", 0)]) := by decide +kernel

/-- Byte index 1 of `"é"` (`C3 A9`) is not a char boundary; 0 and 2 are, 3 is not. -/
example : isCharBoundary [195#u8, 169#u8] 1 = false := by decide

example : isCharBoundary [195#u8, 169#u8] 2 = true ∧ isCharBoundary [195#u8, 169#u8] 3 = false :=
  by decide

/-- The wrapper `prim::percent_encode_controls` (`utf8_percent_encode(value, CONTROLS).into()`)
on `""`, `"a"`, `"\n"` and `"a\n"`: no chunk and one plain chunk give `Cow::Borrowed` of the
input; one byte that needs encoding gives `Cow::Borrowed("%0A")` (the static `%XX` chunk);
two chunks give `Cow::Owned("a%0A")` (`percent-encoding-2.3.2/src/lib.rs` lines 194–209). The
owned case also evaluates the `String` length check of `ExtModel.growString`, whose bound
`isize::MAX` depends on the platform word size and is only bounded below here. -/
example : model.skill.prim.percent_encode_controls (Slice.from [] (by simp)) =
    ok (alloc.borrow.Cow.Borrowed (Slice.from [] (by simp))) := by
  rfl

example : model.skill.prim.percent_encode_controls (Slice.from [97#u8] (by simp; scalar_tac)) =
    ok (alloc.borrow.Cow.Borrowed (Slice.from [97#u8] (by simp; scalar_tac))) := by
  rfl

example : model.skill.prim.percent_encode_controls (Slice.from [10#u8] (by simp; scalar_tac)) =
    ok (alloc.borrow.Cow.Borrowed (Slice.from [37#u8, 48#u8, 65#u8] (by simp; scalar_tac))) := by
  rfl

example : model.skill.prim.percent_encode_controls
      (Slice.from [97#u8, 10#u8] (by simp; scalar_tac)) =
    ok (alloc.borrow.Cow.Owned "a%0A") := by
  have h31 : 2 ^ 31 - 1 ≤ maxStringBytes := by
    simp only [maxStringBytes, Isize.max, Isize.numBits]
    rcases System.Platform.numBits_eq with h | h <;>
      simp only [IScalarTy.Isize_numBits_eq, h] <;> decide
  have h : (String.ofList ((percentEncodeControls [97#u8, 10#u8]).map
      (fun b => Char.ofNat b.val))).utf8ByteSize ≤ maxStringBytes :=
    le_trans (by decide +kernel) h31
  unfold model.skill.prim.percent_encode_controls
  simp only [Slice.from_val]
  rw [ite_eq_right (by decide +kernel)]
  simp only [growString, ite_eq_left h, bind_ok]
  rfl

end Proofs.External.Skill
