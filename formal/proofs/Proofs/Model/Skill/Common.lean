/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Defs.Skill
public import Proofs.External.Byte
public import Proofs.External.Skill
public import Proofs.External.Std
public import Proofs.External.String
public import Proofs.External.WP
public import Proofs.Model.RequestStateWire.Common

@[expose] public section

/-!
# Shared lemmas for the `skill.rs` proofs (K01–K20)

Lemmas used by more than one of the files `Proofs/Model/Skill/{Basic,Verify,Model,ValidateHelpers,
Validate}.lean`, all in the namespace `Proofs.Model.Skill`:

* the bytes of `/`, `%`, `?` and `#`, and `isQueryOrFragmentStart` as a test on the byte value;
* the last `/`-separated part of a byte list (`lastSegment`, `skill_name_from_uri`), characterised
  without `List.splitOn` and as the bytes from `lastSegmentStart` on;
* the skill-name rule of `nameCharsValid` as a condition `NameRule` on indices, with its
  recursive form `nameRule_cons` (used for the loop of `is_valid_skill_name` and for the
  description of a skill name as words);
* `Vec<char>` and `String` equality (the standard `PartialEq` instances).

Source: "crates/rmcp/src/model/skill.rs" (patched copy, translation patch 04).
-/

open Aeneas Aeneas.Std Result
open rmcp
open Defs.Skill

namespace Proofs.Model.Skill

open ExtModel Proofs.External.Byte

/-! ## Bytes -/

/-- The byte of `%` is `37`. -/
theorem asciiByte_percent : asciiByte '%' = byte 37 := rfl

/-- The byte of `/` is `47`. -/
theorem asciiByte_slash : asciiByte '/' = byte 47 := rfl

/-- A byte is `byte n` (`n < 256`) exactly when its value is `n`. -/
theorem eq_byte_iff (b : U8) (n : Nat) (hn : n < 256) : b = byte n ↔ b.val = n := by
  constructor
  · rintro rfl
    rw [byte_val, Nat.mod_eq_of_lt hn]
  · intro h
    exact (byte_eq h.symm).symm

/-- `Defs.Wire.byteOf` is the model's `byte`. -/
theorem byteOf_eq (n : Nat) : Defs.Wire.byteOf n = byte n := rfl

/-- `isQueryOrFragmentStart` tests for the bytes `?` (63) and `#` (35). -/
theorem isQueryOrFragmentStart_eq_decide (b : U8) :
    isQueryOrFragmentStart b = decide (b.val = 63 ∨ b.val = 35) := by
  have e1 : asciiByte '?' = byte 63 := rfl
  have e2 : asciiByte '#' = byte 35 := rfl
  rw [Bool.eq_iff_iff]
  simp only [isQueryOrFragmentStart, Bool.or_eq_true, beq_iff_eq, e1, e2, decide_eq_true_eq,
    eq_byte_iff b 63 (by decide), eq_byte_iff b 35 (by decide)]

/-! ## The last `a`-separated part of a list -/

/-- The last `a`-separated part of `l ++ s` is `s` when `s` has no `a` and `l` is empty or ends
in `a`. -/
theorem getLastD_splitOn_append {α : Type*} [BEq α] [LawfulBEq α] (a : α) (l s : List α)
    (hs : a ∉ s) (hd : l = [] ∨ l.getLast? = some a) :
    ((l ++ s).splitOn a).getLastD [] = s := by
  rcases hd with rfl | hd
  · rw [List.nil_append, List.splitOn_eq_singleton hs]
    rfl
  · obtain ⟨d, rfl⟩ := List.getLast?_eq_some_iff.1 hd
    rw [List.append_assoc, List.singleton_append, List.splitOn_append_cons_self,
      List.splitOn_eq_singleton hs, List.getLastD_eq_getLast?, List.getLast?_append]
    simp only [List.getLast?_singleton, Option.some_or, Option.getD_some]

/-- The last `a`-separated part of a list of length `n` has no `a`, and what precedes it is
empty or ends in `a`. -/
theorem exists_eq_append_getLastD_splitOn {α : Type*} [BEq α] [LawfulBEq α] (a : α) :
    ∀ (n : Nat) (l : List α), l.length = n →
      a ∉ (l.splitOn a).getLastD [] ∧ ∃ dir, l = dir ++ (l.splitOn a).getLastD [] ∧
        (dir = [] ∨ dir.getLast? = some a) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hl
    by_cases ha : a ∈ l
    · obtain ⟨d, t, rfl⟩ := List.append_of_mem ha
      have hlt : t.length < n := by simp only [List.length_append, List.length_cons] at hl; omega
      obtain ⟨h1, dir, h2, h3⟩ := ih _ hlt t rfl
      have hsp : ((d ++ a :: t).splitOn a).getLastD [] = (t.splitOn a).getLastD [] := by
        rw [List.splitOn_append_cons_self, List.getLastD_eq_getLast?, List.getLastD_eq_getLast?,
          List.getLast?_append]
        obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1
          (List.getLast?_eq_none_iff.not.2 (List.splitOn_ne_nil a t))
        simp only [hx, Option.some_or, Option.getD_some]
      rw [hsp]
      refine ⟨h1, d ++ a :: dir, ?_, Or.inr ?_⟩
      · conv_lhs => rw [h2]
        simp only [List.getLastD_eq_getLast?, List.append_assoc, List.cons_append]
      · rcases h3 with rfl | h3
        · simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
        · rw [← List.singleton_append, ← List.append_assoc, List.getLast?_append, h3]
          rfl
    · rw [List.splitOn_eq_singleton ha]
      exact ⟨ha, [], rfl, Or.inl rfl⟩

/-- The last `a`-separated part of `l`, characterised without `splitOn`. -/
theorem getLastD_splitOn_eq_iff {α : Type*} [BEq α] [LawfulBEq α] (a : α) (l s : List α) :
    (l.splitOn a).getLastD [] = s ↔
      a ∉ s ∧ ∃ dir, l = dir ++ s ∧ (dir = [] ∨ dir.getLast? = some a) := by
  constructor
  · rintro rfl
    exact exists_eq_append_getLastD_splitOn a _ l rfl
  · rintro ⟨hs, dir, rfl, hd⟩
    exact getLastD_splitOn_append a dir s hs hd

/-- An item before a list that contains `a` does not change the last `a`-separated part. -/
theorem getLastD_splitOn_cons_of_mem {α : Type*} [BEq α] [LawfulBEq α] (a b : α) (l : List α)
    (h : a ∈ l) : ((b :: l).splitOn a).getLastD [] = (l.splitOn a).getLastD [] := by
  obtain ⟨hs, dir, hl, hd⟩ := (getLastD_splitOn_eq_iff a l _).1 rfl
  have hdir : dir.getLast? = some a := by
    rcases hd with rfl | hd
    · rw [List.nil_append] at hl
      rw [← hl] at hs
      exact absurd h hs
    · exact hd
  conv_lhs => rw [hl, ← List.cons_append]
  refine getLastD_splitOn_append a (b :: dir) _ hs (Or.inr ?_)
  rw [← List.singleton_append, List.getLast?_append, hdir]
  rfl

/-- The bytes from `lastSegmentStart sep l` on are the last part of the split of `l` at `sep`. -/
theorem drop_lastSegmentStart (sep : U8) :
    ∀ l : List U8, l.drop (lastSegmentStart sep l) = (l.splitOn sep).getLastD []
  | [] => by simp only [lastSegmentStart, List.reverse_nil, List.findIdx?_nil, List.length_nil,
      Std.le_refl, List.drop_of_length_le, List.splitOn_nil, List.getLastD_eq_getLast?,
      List.getLast?_singleton, Option.getD_some]
  | a :: rest => by
    have ih := drop_lastSegmentStart sep rest
    unfold lastSegmentStart at ih ⊢
    rw [List.reverse_cons, List.findIdx?_append]
    cases hr : rest.reverse.findIdx? (fun b => decide (b = sep)) with
    | some j =>
      rw [hr] at ih
      obtain ⟨hjl, hpj, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hr
      have hmem : sep ∈ rest := by
        have := List.getElem_mem hjl
        rw [List.mem_reverse] at this
        simp only [decide_eq_true_eq] at hpj
        rw [hpj] at this
        exact this
      rw [Option.some_or, getLastD_splitOn_cons_of_mem sep a rest hmem, ← ih]
      simp only [List.length_reverse] at hjl
      simp only [List.length_cons]
      rw [show rest.length + 1 - j = (rest.length - j) + 1 by omega, List.drop_succ_cons]
    | none =>
      have hno : sep ∉ rest := by
        intro hm
        rw [List.findIdx?_eq_none_iff] at hr
        have := hr sep (List.mem_reverse.2 hm)
        simp only [decide_true, Bool.true_eq_false] at this
      rw [Option.none_or]
      by_cases ha : a = sep
      · subst ha
        simp only [List.length_reverse, List.findIdx?_singleton, decide_true, ↓reduceIte,
          Option.map_some, zero_add, List.length_cons, add_tsub_cancel_left, List.drop_succ_cons,
          List.drop_zero, List.splitOn_cons_eq_ite_modifyHead, BEq.rfl,
          List.splitOn_eq_singleton hno, List.getLastD_eq_getLast?, List.getLast?_cons_cons,
          List.getLast?_singleton, Option.getD_some]
      · have hno' : sep ∉ a :: rest := by
          simp only [List.mem_cons, not_or]
          exact ⟨fun h => ha h.symm, hno⟩
        simp only [List.length_reverse, List.findIdx?_singleton, ha, decide_false,
          Bool.false_eq_true, ↓reduceIte, Option.map_none, List.drop_zero,
          List.splitOn_eq_singleton hno', List.getLastD_eq_getLast?, List.getLast?_singleton,
          Option.getD_some]

/-! ## The skill-name rule -/

/-- The skill-name rule of `nameCharsValid` on indices, from a virtual previous character: each
character is a letter or digit (`alnum`), or a `-` followed by a letter or digit and preceded by
one (at index `0`, `first` says whether the virtual previous character is one). `nameCharsValid`
uses `first = false`. -/
def NameRule (alnum : Char → Bool) (first : Bool) (cs : List Char) : Prop :=
  ∀ i < cs.length, alnum (cs.getD i ' ') = true ∨
    (cs.getD i ' ' = '-' ∧ i + 1 < cs.length ∧
      (if i = 0 then first = true else alnum (cs.getD (i - 1) ' ') = true) ∧
      alnum (cs.getD (i + 1) ' ') = true)

/-- The empty list satisfies the rule. -/
theorem nameRule_nil (alnum : Char → Bool) (first : Bool) : NameRule alnum first [] := by
  intro i hi
  simp only [List.length_nil, not_lt_zero] at hi

/-- The rule on `c :: r`: the condition on `c`, then the rule on `r` from `c`. -/
theorem nameRule_cons (alnum : Char → Bool) (first : Bool) (c : Char) (r : List Char) :
    NameRule alnum first (c :: r) ↔
      (alnum c = true ∨ (c = '-' ∧ r ≠ [] ∧ first = true ∧ alnum (r.getD 0 ' ') = true)) ∧
        NameRule alnum (alnum c) r := by
  constructor
  · intro h
    refine ⟨?_, fun i hi => ?_⟩
    · rcases h 0 (Nat.succ_pos _) with h0 | ⟨h1, h2, h3, h4⟩
      · rw [List.getD_cons_zero] at h0
        exact Or.inl h0
      · rw [List.getD_cons_zero] at h1
        rw [ite_eq_left rfl] at h3
        rw [List.getD_cons_succ] at h4
        rw [List.length_cons] at h2
        exact Or.inr ⟨h1, List.ne_nil_of_length_pos (by omega), h3, h4⟩
    · rcases h (i + 1) (by rw [List.length_cons]; omega) with h0 | ⟨h1, h2, h3, h4⟩
      · rw [List.getD_cons_succ] at h0
        exact Or.inl h0
      · rw [List.getD_cons_succ] at h1 h4
        rw [List.length_cons] at h2
        rw [ite_eq_right (Nat.succ_ne_zero i), Nat.add_sub_cancel] at h3
        refine Or.inr ⟨h1, by omega, ?_, h4⟩
        cases i with
        | zero =>
          rw [ite_eq_left rfl]
          rwa [List.getD_cons_zero] at h3
        | succ j =>
          rw [ite_eq_right (Nat.succ_ne_zero j), Nat.add_sub_cancel]
          rwa [List.getD_cons_succ] at h3
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero =>
      rw [List.getD_cons_zero, List.getD_cons_succ, ite_eq_left rfl, List.length_cons]
      rcases h0 with h0 | ⟨h1, h2, h3, h4⟩
      · exact Or.inl h0
      · exact Or.inr ⟨h1, by have := List.length_pos_iff.2 h2; omega, h3, h4⟩
    | succ i =>
      rw [List.length_cons] at hi
      rw [List.getD_cons_succ, List.getD_cons_succ, ite_eq_right (Nat.succ_ne_zero i),
        Nat.add_sub_cancel, List.length_cons]
      rcases h i (by omega) with h5 | ⟨h1, h2, h3, h4⟩
      · exact Or.inl h5
      · refine Or.inr ⟨h1, by omega, ?_, h4⟩
        cases i with
        | zero =>
          rw [List.getD_cons_zero]
          rwa [ite_eq_left rfl] at h3
        | succ j =>
          rw [List.getD_cons_succ]
          rwa [ite_eq_right (Nat.succ_ne_zero j), Nat.add_sub_cancel] at h3

/-- `nameCharsValid` as a condition on indices: 1 to 64 characters that satisfy `NameRule`. -/
theorem nameCharsValid_eq_true_iff (alnum : Char → Bool) (cs : List Char) :
    nameCharsValid alnum cs = true ↔ cs ≠ [] ∧ cs.length ≤ 64 ∧ NameRule alnum false cs := by
  simp only [nameCharsValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, beq_iff_eq, and_assoc]
  constructor
  · rintro ⟨hne, hl, h⟩
    refine ⟨hne, hl, ?_⟩
    intro i hi
    rcases h i hi with h0 | ⟨h1, h2, h3, h4, h5⟩
    · exact Or.inl h0
    · refine Or.inr ⟨h1, h3, ?_, h5⟩
      rw [ite_eq_right (by omega)]
      exact h4
  · rintro ⟨hne, hl, h⟩
    refine ⟨hne, hl, ?_⟩
    intro i hi
    rcases h i hi with h0 | ⟨h1, h3, h4, h5⟩
    · exact Or.inl h0
    · by_cases hi0 : i = 0
      · rw [ite_eq_left hi0] at h4
        cases h4
      · rw [ite_eq_right hi0] at h4
        exact Or.inr ⟨h1, by omega, h3, h4, h5⟩

/-! ## Equality of `Vec<char>` and `String` -/

/-- `allM` of `char` equality is `all` of decided equality. -/
theorem allM_char_eq (l : List (Char × Char)) :
    List.allM (fun (x : Char × Char) => Char.Insts.CoreCmpPartialEqChar.eq x.1 x.2) l =
      ok (l.all fun p => decide (p.1 = p.2)) :=
  List.allM_pure (m := Result) (p := fun (x : Char × Char) => decide (x.1 = x.2))

/-- Pointwise equality of two lists of the same length is their equality. -/
theorem all_zip_eq_decide_eq : ∀ (a b : List Char), a.length = b.length →
    ((a.zip b).all fun p => decide (p.1 = p.2)) = decide (a = b)
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    have hl : xs.length = ys.length := Nat.succ.inj h
    simp only [List.zip_cons_cons, List.all_cons, all_zip_eq_decide_eq xs ys hl, List.cons.injEq]
    by_cases hxy : x = y
    · simp only [hxy, decide_true, Bool.true_and, true_and]
    · simp only [hxy, decide_false, Bool.false_and, false_and]
  | [], _ :: _, h => by simp only [List.length_nil, List.length_cons, Nat.right_eq_add,
      Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false] at h
  | _ :: _, [], h => by simp only [List.length_cons, List.length_nil, Nat.add_eq_zero_iff,
      List.length_eq_zero_iff, one_ne_zero, and_false] at h

/-- `Vec<char>` equality (`PartialEq for Vec`, through `char`'s `PartialEq`). -/
@[step]
theorem vec_char_eq_spec (v v1 : alloc.vec.Vec Char) :
    alloc.vec.partial_eq.PartialEqVec.eq Char.Insts.CoreCmpPartialEqChar v v1
      ⦃ (result : Bool) => result = decide (v.val = v1.val) ⦄ := by
  unfold alloc.vec.partial_eq.PartialEqVec.eq
  by_cases h : v.length = v1.length
  · rw [ite_eq_left h, allM_char_eq, WP.spec_ok, all_zip_eq_decide_eq _ _ h]
  · rw [ite_eq_right h, WP.spec_ok, eq_comm, decide_eq_false_iff_not]
    intro he
    exact h (by simp only [alloc.vec.Vec.length, he])

/-- `String`'s `Eq` instance decides equality (the premise of `HashSet::insert_spec`). -/
theorem string_eq_inst_spec (a b : String) :
    alloc.string.String.Insts.CoreCmpEq.partialEqInst.eq a b ⦃ (r : Bool) =>
      (r = true ↔ a = b) ⦄ := by
  have := alloc.string.String.Insts.CoreCmpPartialEqString.eq_spec a b
  obtain ⟨r, hr, hrv⟩ := Proofs.External.WP.exists_ok_of_spec this
  show alloc.string.String.Insts.CoreCmpPartialEqString.eq a b ⦃ (r : Bool) => (r = true ↔ a = b) ⦄
  rw [hr, WP.spec_ok, hrv, decide_eq_true_iff]

end Proofs.Model.Skill
