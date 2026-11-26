/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Defs
public import Proofs.External.String
public import Proofs.Model.Skill.Common

@[expose] public section

/-!
# Consequences of the model of the public `skill.rs` API (K01–K20)

The pure consequences of the definitions `Defs.Skill` (signed off 2026-11-25; restated in
`formal/specs/Specs/Model/Skill.lean`, section "Consequences of the model"): what `skillNameOfUri`
accepts, the skill-name rule as words, the characterisation of every result of `validateResult`
and of `Ok` of `validateSkillsResult`, sublists and prefixes of listings, and the bridge lemma
`NfkcFits.of_utf8ByteSize_le`. No translated function appears; the opaque `ExtModel.nfkc`,
`ExtModel.sha256` and `ExtModel.generalCategory` are never opened.
-/

open Aeneas Aeneas.Std
open rmcp.model.skill (Skill SkillResource SkillValidationError)
open Defs (utf8Bytes)
open Defs.Skill

/-! ## Helpers -/

namespace Proofs.Model.Skill

/-! ### Skill names -/

/-- A single letter or digit passes the rule. -/
theorem NameRule.singleton {alnum : Char → Bool} {c : Char} (hc : alnum c = true) :
    NameRule alnum false [c] :=
  (nameRule_cons alnum false c []).2 ⟨Or.inl hc, nameRule_nil _ _⟩

/-- Prepending a letter or digit to a passing list that starts with one. -/
theorem NameRule.cons_cons {alnum : Char → Bool} {c d : Char} {r : List Char}
    (hc : alnum c = true) (hd : alnum d = true) (h : NameRule alnum false (d :: r)) :
    NameRule alnum false (c :: d :: r) := by
  obtain ⟨-, h2⟩ := (nameRule_cons alnum false d r).1 h
  refine (nameRule_cons alnum false c (d :: r)).2 ⟨Or.inl hc, ?_⟩
  rw [hc]
  exact (nameRule_cons alnum true d r).2 ⟨Or.inl hd, h2⟩

/-- Prepending a letter or digit and a `-` to a passing list that starts with a letter or
digit. -/
theorem NameRule.cons_hyphen {alnum : Char → Bool} {c e : Char} {r : List Char}
    (hc : alnum c = true) (he : alnum e = true) (h : NameRule alnum false (e :: r)) :
    NameRule alnum false (c :: '-' :: e :: r) := by
  obtain ⟨-, h2⟩ := (nameRule_cons alnum false e r).1 h
  refine (nameRule_cons alnum false c ('-' :: e :: r)).2 ⟨Or.inl hc, ?_⟩
  rw [hc]
  refine (nameRule_cons alnum true '-' (e :: r)).2
    ⟨Or.inr ⟨rfl, List.cons_ne_nil e r, rfl, he⟩, ?_⟩
  exact (nameRule_cons alnum _ e r).2 ⟨Or.inl he, h2⟩

/-- A passing list starts with a letter or digit. -/
theorem NameRule.alnum_head {alnum : Char → Bool} {c : Char} {r : List Char}
    (h : NameRule alnum false (c :: r)) : alnum c = true := by
  rcases ((nameRule_cons alnum false c r).1 h).1 with h1 | ⟨-, -, h2, -⟩
  · exact h1
  · cases h2

/-- The tail of a passing list is passing when it starts with a letter or digit. -/
theorem NameRule.of_cons_cons {alnum : Char → Bool} {c d : Char} {r : List Char}
    (h : NameRule alnum false (c :: d :: r)) (hd : alnum d = true) :
    NameRule alnum false (d :: r) := by
  obtain ⟨-, h1⟩ := (nameRule_cons alnum false c (d :: r)).1 h
  obtain ⟨-, h2⟩ := (nameRule_cons alnum _ d r).1 h1
  exact (nameRule_cons alnum false d r).2 ⟨Or.inl hd, h2⟩

/-- In a passing list, a second character that is not a letter or digit is a `-` followed by a
passing list. -/
theorem NameRule.of_cons_hyphen {alnum : Char → Bool} {c d : Char} {r : List Char}
    (h : NameRule alnum false (c :: d :: r)) (hd : alnum d = false) :
    d = '-' ∧ ∃ e t, r = e :: t ∧ alnum e = true ∧ NameRule alnum false (e :: t) := by
  obtain ⟨-, h1⟩ := (nameRule_cons alnum false c (d :: r)).1 h
  obtain ⟨h2, h3⟩ := (nameRule_cons alnum _ d r).1 h1
  rw [hd] at h3
  rcases h2 with h2 | ⟨hd', hr, -, he⟩
  · rw [hd] at h2
    cases h2
  · obtain ⟨e, t, rfl⟩ := List.exists_cons_of_ne_nil hr
    exact ⟨hd', e, t, rfl, he, h3⟩

/-- A non-empty passing list is words joined by `-`. -/
theorem exists_words_of_nameRule (alnum : Char → Bool) :
    ∀ (n : Nat) (cs : List Char), cs.length = n → cs ≠ [] → NameRule alnum false cs →
      ∃ words : List (List Char), words ≠ [] ∧
        (∀ w ∈ words, w ≠ [] ∧ ∀ c ∈ w, alnum c = true) ∧ cs = List.intercalate ['-'] words := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro cs hl hne h
    match cs with
    | [] => exact absurd rfl hne
    | [c] =>
      refine ⟨[[c]], List.cons_ne_nil _ _, fun w hw => ?_, rfl⟩
      rw [List.mem_singleton.1 hw]
      exact ⟨List.cons_ne_nil _ _, fun x hx => List.mem_singleton.1 hx ▸ h.alnum_head⟩
    | c :: d :: r =>
      have hc := h.alnum_head
      rw [List.length_cons, List.length_cons] at hl
      cases hd : alnum d
      · obtain ⟨rfl, e, t, rfl, he, h'⟩ := h.of_cons_hyphen hd
        obtain ⟨words, hw1, hw2, hw3⟩ :=
          ih (e :: t).length (by rw [List.length_cons] at hl ⊢; omega) (e :: t) rfl
            (List.cons_ne_nil _ _) h'
        obtain ⟨v, vs, rfl⟩ := List.exists_cons_of_ne_nil hw1
        refine ⟨[c] :: v :: vs, List.cons_ne_nil _ _, fun w hw => ?_, ?_⟩
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact ⟨List.cons_ne_nil _ _, fun x hx => List.mem_singleton.1 hx ▸ hc⟩
          · exact hw2 w hw
        · rw [List.intercalate_cons_cons, ← hw3]
          rfl
      · obtain ⟨words, hw1, hw2, hw3⟩ :=
          ih (d :: r).length (by rw [List.length_cons]; omega) (d :: r) rfl
            (List.cons_ne_nil _ _) (h.of_cons_cons hd)
        obtain ⟨v, vs, rfl⟩ := List.exists_cons_of_ne_nil hw1
        have hv := hw2 v List.mem_cons_self
        refine ⟨(c :: v) :: vs, List.cons_ne_nil _ _, fun w hw => ?_, ?_⟩
        · rcases List.mem_cons.1 hw with rfl | hw
          · refine ⟨List.cons_ne_nil _ _, fun x hx => ?_⟩
            rcases List.mem_cons.1 hx with rfl | hx
            · exact hc
            · exact hv.2 x hx
          · exact hw2 w (List.mem_cons_of_mem _ hw)
        · cases vs with
          | nil =>
            rw [List.intercalate_singleton] at hw3 ⊢
            rw [hw3]
          | cons u us =>
            rw [List.intercalate_cons_cons] at hw3 ⊢
            rw [hw3]
            rfl

/-- A word followed by nothing or by `-` and a passing list that starts with a letter or digit
is passing and starts with a letter or digit. -/
theorem nameRule_append (alnum : Char → Bool) (R : List Char)
    (hR : R = [] ∨ ∃ e t, R = '-' :: e :: t ∧ alnum e = true ∧ NameRule alnum false (e :: t)) :
    ∀ w : List Char, w ≠ [] → (∀ c ∈ w, alnum c = true) →
      NameRule alnum false (w ++ R) ∧ ∃ c t, w ++ R = c :: t ∧ alnum c = true
  | [], hw, _ => absurd rfl hw
  | [c], _, hc => by
    have hc' : alnum c = true := hc c List.mem_cons_self
    refine ⟨?_, c, R, rfl, hc'⟩
    rcases hR with rfl | ⟨e, t, rfl, he, h⟩
    · exact NameRule.singleton hc'
    · exact NameRule.cons_hyphen hc' he h
  | c :: d :: w, _, hc => by
    have hc' : alnum c = true := hc c List.mem_cons_self
    obtain ⟨h1, -⟩ := nameRule_append alnum R hR (d :: w) (List.cons_ne_nil _ _)
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    have hd : alnum d = true := hc d (List.mem_cons_of_mem _ List.mem_cons_self)
    refine ⟨?_, c, _, rfl, hc'⟩
    rw [List.cons_append] at h1 ⊢
    exact NameRule.cons_cons hc' hd h1

/-- Words joined by `-` are passing and start with a letter or digit. -/
theorem nameRule_intercalate (alnum : Char → Bool) :
    ∀ words : List (List Char), words ≠ [] →
      (∀ w ∈ words, w ≠ [] ∧ ∀ c ∈ w, alnum c = true) →
      NameRule alnum false (List.intercalate ['-'] words) ∧
        ∃ c t, List.intercalate ['-'] words = c :: t ∧ alnum c = true
  | [], hw, _ => absurd rfl hw
  | [w], _, hw => by
    have := nameRule_append alnum [] (Or.inl rfl) w (hw w List.mem_cons_self).1
      (hw w List.mem_cons_self).2
    rw [List.intercalate_singleton]
    rwa [List.append_nil] at this
  | w :: v :: vs, _, hw => by
    obtain ⟨h1, e, t, het, he⟩ := nameRule_intercalate alnum (v :: vs) (List.cons_ne_nil _ _)
      (fun u hu => hw u (List.mem_cons_of_mem _ hu))
    rw [List.intercalate_cons_cons, List.append_assoc]
    apply nameRule_append alnum _ _ w (hw w List.mem_cons_self).1 (hw w List.mem_cons_self).2
    refine Or.inr ⟨e, t, ?_, he, het ▸ h1⟩
    rw [het]
    rfl

/-! ### `validateResult` and `validateSkillsResult` -/

/-- A file fault is of one of the three per-file kinds. -/
theorem fileFault_eq_some_kind {skillUri : String} {earlier : List SkillResource}
    {file : SkillResource} {e : SkillValidationError}
    (h : fileFault skillUri earlier file = some e) :
    (∃ uri u, e = .ResourceOutsideSkill uri u) ∨ (∃ uri, e = .DuplicateResource uri) ∨
      (∃ uri digest, e = .MalformedDigest uri digest) := by
  unfold fileFault at h
  split at h
  · cases h
    exact Or.inl ⟨_, _, rfl⟩
  · split_ifs at h
    · cases h
      exact Or.inr (Or.inl ⟨_, rfl⟩)
    · cases h
      exact Or.inr (Or.inr ⟨_, _, rfl⟩)

/-- The first file fault is of one of the three per-file kinds. -/
theorem firstFileFault_eq_some_kind {skillUri : String} :
    ∀ {earlier files : List SkillResource} {e : SkillValidationError},
      firstFileFault skillUri earlier files = some e →
        (∃ uri u, e = .ResourceOutsideSkill uri u) ∨ (∃ uri, e = .DuplicateResource uri) ∨
          (∃ uri digest, e = .MalformedDigest uri digest)
  | _, [], _, h => nomatch h
  | earlier, file :: rest, e, h => by
    rw [firstFileFault] at h
    cases hf : fileFault skillUri earlier file with
    | none =>
      rw [hf, Option.none_or] at h
      exact firstFileFault_eq_some_kind h
    | some e' =>
      rw [hf, Option.some_or, Option.some.injEq] at h
      subst h
      exact fileFault_eq_some_kind hf

/-- `firstFileFault` is `none` exactly when every file has a key and a well-formed digest, the
keys are pairwise distinct, and no key is that of an earlier file. -/
theorem firstFileFault_eq_none_iff {skillUri : String} :
    ∀ {earlier files : List SkillResource},
      firstFileFault skillUri earlier files = none ↔
        (∀ f ∈ files, (fileKey skillUri f).isSome ∧ isSha256Digest (utf8Bytes f.digest)) ∧
          (files.map (fileKey skillUri)).Nodup ∧
          ∀ f ∈ files, ∀ g ∈ earlier, fileKey skillUri g ≠ fileKey skillUri f
  | _, [] => by simp only [firstFileFault, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      List.map_nil, List.nodup_nil, ne_eq, and_self]
  | earlier, file :: rest => by
    rw [firstFileFault, Option.or_eq_none_iff, firstFileFault_eq_none_iff]
    unfold fileFault
    cases hk : fileKey skillUri file with
    | none => simp only [reduceCtorEq, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        ne_eq, false_and, forall_eq_or_imp, hk, Option.isSome_none, Bool.false_eq_true,
        List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and, and_assoc]
    | some key =>
      simp only [List.any_eq_true, beq_iff_eq]
      by_cases hd : isSha256Digest (utf8Bytes file.digest) = true
      · simp only [hd]
        constructor
        · rintro ⟨h1, ⟨h2, h3, h4⟩⟩
          refine ⟨?_, ?_, ?_⟩
          · intro f hf
            rcases List.mem_cons.1 hf with rfl | hf
            · simp only [hk, Option.isSome_some, hd, and_self]
            · exact h2 f hf
          · rw [List.map_cons, List.nodup_cons]
            refine ⟨?_, h3⟩
            simp only [List.mem_map, not_exists, not_and]
            intro f hf hfk
            exact h4 f hf file (List.mem_append_right _ (List.mem_singleton_self _)) hfk.symm
          · intro f hf g hg
            rcases List.mem_cons.1 hf with rfl | hf
            · intro hgk
              rw [ite_eq_left ⟨g, hg, hgk.trans hk⟩] at h1
              cases h1
            · exact h4 f hf g (List.mem_append_left _ hg)
        · rintro ⟨h2, h3, h4⟩
          rw [List.map_cons, List.nodup_cons] at h3
          refine ⟨?_, ?_, h3.2, ?_⟩
          · have hne : ¬∃ g ∈ earlier, fileKey skillUri g = some key := by
              rintro ⟨g, hg, hgk⟩
              exact h4 file List.mem_cons_self g hg (hgk.trans hk.symm)
            simp only [hne, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
          · exact fun f hf => h2 f (List.mem_cons_of_mem _ hf)
          · intro f hf g hg
            rcases List.mem_append.1 hg with hg | hg
            · exact h4 f (List.mem_cons_of_mem _ hf) g hg
            · rw [List.mem_singleton.1 hg]
              intro hfk
              exact h3.1 (List.mem_map.2 ⟨f, hf, hfk.symm⟩)
      · simp only [Bool.not_eq_true] at hd
        constructor
        · rintro ⟨h1, -⟩
          split at h1
          · simp only [reduceCtorEq] at h1
          · simp only [hd, Bool.not_false, ↓reduceIte, reduceCtorEq] at h1
        · rintro ⟨h2, -⟩
          have := (h2 file List.mem_cons_self).2
          rw [hd] at this
          exact absurd this Bool.false_ne_true

/-- Every `Err` of `validateResult`, by the check that gives it. -/
theorem validateResult_eq_err_iff (s : Skill) (e : SkillValidationError) :
    validateResult s = .Err e ↔
      (skillNameOfUri (utf8Bytes s.uri) = none ∧ SkillValidationError.UriNotSkillMd s.uri = e) ∨
      (∃ encoded, skillNameOfUri (utf8Bytes s.uri) = some encoded ∧
        isSkillName s.frontmatter.«name» = false ∧
        SkillValidationError.InvalidName s.frontmatter.«name» = e) ∨
      (∃ encoded, skillNameOfUri (utf8Bytes s.uri) = some encoded ∧
        isSkillName s.frontmatter.«name» = true ∧
        nameMatchesSegment encoded s.frontmatter.«name» = false ∧
        SkillValidationError.NameMismatch s.uri s.frontmatter.«name» = e) ∨
      (∃ encoded files, skillNameOfUri (utf8Bytes s.uri) = some encoded ∧
        isSkillName s.frontmatter.«name» = true ∧
        nameMatchesSegment encoded s.frontmatter.«name» = true ∧
        s.resources = .Files files ∧ (∀ f ∈ files.val, f.uri ≠ s.uri) ∧
        SkillValidationError.MissingSkillMd s.uri = e) ∨
      (∃ encoded files, skillNameOfUri (utf8Bytes s.uri) = some encoded ∧
        isSkillName s.frontmatter.«name» = true ∧
        nameMatchesSegment encoded s.frontmatter.«name» = true ∧
        s.resources = .Files files ∧ (∃ f ∈ files.val, f.uri = s.uri) ∧
        firstFileFault s.uri [] files.val = some e) := by
  obtain ⟨uri, ⟨nm, desc, extra⟩, res, mt⟩ := s
  cases hu : skillNameOfUri (utf8Bytes uri) with
  | none => simp only [validateResult, hu, core.result.Result.Err.injEq, true_and, reduceCtorEq,
      false_and, exists_const, ne_eq, or_self, or_false]
  | some enc =>
    by_cases hn : isSkillName nm = true
    · by_cases hm : nameMatchesSegment enc nm = true
      · cases res with
        | Dynamic => simp only [validateResult, hu, hn, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, hm, reduceCtorEq, false_and, Option.some.injEq, Bool.true_eq_false,
            and_false, exists_const, true_and, exists_eq_left', ne_eq, or_self]
        | Files files =>
          by_cases hf : files.val.any (fun f => f.uri == uri) = true
          · have hf' : ∃ f ∈ files.val, f.uri = uri := by
              obtain ⟨f, hf1, hf2⟩ := List.any_eq_true.1 hf
              exact ⟨f, hf1, beq_iff_eq.1 hf2⟩
            have hf'' : ¬∀ f ∈ files.val, f.uri ≠ uri := by
              obtain ⟨f, hf1, hf2⟩ := hf'
              exact fun h => h f hf1 hf2
            cases hff : firstFileFault uri [] files.val with
            | none => simp only [validateResult, hu, hn, Bool.not_true, Bool.false_eq_true,
                ↓reduceIte, hm, hf, hff, reduceCtorEq, false_and, Option.some.injEq,
                Bool.true_eq_false, and_false, exists_const, true_and, exists_eq_left',
                rmcp.model.skill.SkillResources.Files.injEq, ne_eq, exists_and_left, ↓existsAndEq,
                hf'', hf', or_self]
            | some e => simp only [validateResult, hu, hn, Bool.not_true, Bool.false_eq_true,
                ↓reduceIte, hm, hf, hff, core.result.Result.Err.injEq, reduceCtorEq, false_and,
                Option.some.injEq, Bool.true_eq_false, and_false, exists_const, true_and,
                exists_eq_left', rmcp.model.skill.SkillResources.Files.injEq, ne_eq,
                exists_and_left, ↓existsAndEq, hf'', hf', false_or]
          · have hf' : ¬∃ f ∈ files.val, f.uri = uri := by simpa only [not_exists, not_and,
              List.any_eq_true, beq_iff_eq] using hf
            simp only [Bool.not_eq_true] at hf
            have hf'' : ∀ f ∈ files.val, f.uri ≠ uri := by simpa only [ne_eq, not_exists,
                not_and] using hf'
            simp only [validateResult, hu, hn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hm,
              hf, Bool.not_false, core.result.Result.Err.injEq, reduceCtorEq, false_and,
              Option.some.injEq, Bool.true_eq_false, and_false, exists_const, true_and,
              exists_eq_left', rmcp.model.skill.SkillResources.Files.injEq, ne_eq, exists_and_left,
              ↓existsAndEq, hf', or_false, false_or, iff_and_self]
            exact fun _ => hf''
      · simp only [Bool.not_eq_true] at hm
        simp only [validateResult, hu, hn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hm,
          Bool.not_false, core.result.Result.Err.injEq, reduceCtorEq, false_and, Option.some.injEq,
          Bool.true_eq_false, and_false, exists_const, true_and, exists_eq_left', ne_eq,
          exists_and_left, or_self, or_false, false_or]
    · simp only [Bool.not_eq_true] at hn
      simp only [validateResult, hu, hn, Bool.not_false, ↓reduceIte, core.result.Result.Err.injEq,
        reduceCtorEq, false_and, Option.some.injEq, true_and, exists_and_right, ↓existsAndEq,
        Bool.false_eq_true, and_false, exists_const, ne_eq, or_self, or_false, false_or]

/-- `firstSkillFault` is `none` exactly when every skill validates, the keys are pairwise
distinct, and no key is that of an earlier skill. -/
theorem firstSkillFault_eq_none_iff :
    ∀ {earlier skills : List Skill},
      firstSkillFault earlier skills = none ↔
        (∀ s ∈ skills, validateResult s = .Ok ()) ∧ (skills.map skillKey).Nodup ∧
          ∀ s ∈ skills, ∀ t ∈ earlier, skillKey t ≠ skillKey s
  | _, [] => by simp only [firstSkillFault, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      List.map_nil, List.nodup_nil, ne_eq, and_self]
  | earlier, s :: rest => by
    rw [firstSkillFault]
    cases hv : validateResult s with
    | Err e => simp only [reduceCtorEq, List.mem_cons, forall_eq_or_imp, hv, false_and,
        List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and, ne_eq, and_assoc]
    | Ok u =>
      cases u
      by_cases hd : earlier.any (fun t => skillKey t == skillKey s) = true
      · simp only [hd, ↓reduceIte, reduceCtorEq, false_iff]
        rintro ⟨-, -, h3⟩
        obtain ⟨t, ht, htk⟩ := List.any_eq_true.1 hd
        exact h3 s List.mem_cons_self t ht (beq_iff_eq.1 htk)
      · simp only [Bool.not_eq_true] at hd
        simp only [hd, Bool.false_eq_true, ↓reduceIte]
        rw [firstSkillFault_eq_none_iff]
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨?_, ?_, ?_⟩
          · intro t ht
            rcases List.mem_cons.1 ht with rfl | ht
            · exact hv
            · exact h1 t ht
          · rw [List.map_cons, List.nodup_cons]
            refine ⟨?_, h2⟩
            simp only [List.mem_map, not_exists, not_and]
            intro t ht htk
            exact h3 t ht s (List.mem_append_right _ (List.mem_singleton_self _)) htk.symm
          · intro t ht r hr
            rcases List.mem_cons.1 ht with rfl | ht
            · intro hrk
              have := List.any_eq_false.1 hd r hr
              simp only [hrk, BEq.rfl, not_true_eq_false] at this
            · exact h3 t ht r (List.mem_append_left _ hr)
        · rintro ⟨h1, h2, h3⟩
          rw [List.map_cons, List.nodup_cons] at h2
          refine ⟨fun t ht => h1 t (List.mem_cons_of_mem _ ht), h2.2, ?_⟩
          intro t ht r hr
          rcases List.mem_append.1 hr with hr | hr
          · exact h3 t (List.mem_cons_of_mem _ ht) r hr
          · rw [List.mem_singleton.1 hr]
            intro htk
            exact h2.1 (List.mem_map.2 ⟨t, ht, htk.symm⟩)

/-- The fault of a prefix is the fault of the listing. -/
theorem firstSkillFault_append_of_eq_some {e : SkillValidationError} (l₂ : List Skill) :
    ∀ {earlier l₁ : List Skill}, firstSkillFault earlier l₁ = some e →
      firstSkillFault earlier (l₁ ++ l₂) = some e
  | _, [], h => by simp only [firstSkillFault, reduceCtorEq] at h
  | earlier, s :: rest, h => by
    rw [List.cons_append, firstSkillFault]
    rw [firstSkillFault] at h
    cases hv : validateResult s with
    | Err e' => rw [hv] at h; exact h
    | Ok u =>
      cases u
      rw [hv] at h
      dsimp only at h ⊢
      by_cases hd : earlier.any (fun t => skillKey t == skillKey s) = true
      · rw [ite_eq_left hd] at h ⊢
        exact h
      · rw [ite_eq_right hd] at h ⊢
        exact firstSkillFault_append_of_eq_some l₂ h

/-! ### Lengths -/

/-- A string has at most as many characters as UTF-8 bytes. -/
theorem length_toList_le_utf8ByteSize (s : String) : s.toList.length ≤ s.utf8ByteSize := by
  calc s.toList.length ≤ (s.toList.flatMap String.utf8EncodeChar).length := by
        induction s.toList with
        | nil => simp only [List.length_nil, List.flatMap_nil, Std.le_refl]
        | cons c cs ih =>
          rw [List.flatMap_cons, List.length_append, List.length_cons]
          have := String.utf8EncodeChar_ne_nil (c := c)
          have : 0 < (String.utf8EncodeChar c).length := List.length_pos_iff.2 this
          omega
    _ = (String.ofList s.toList).utf8ByteSize := by
        rw [← String.size_toByteArray, String.toByteArray_ofList, List.utf8Encode]
        simp only [List.length_flatMap, String.length_utf8EncodeChar, List.size_toByteArray]
    _ = s.utf8ByteSize := by rw [String.ofList_toList]

/-- `decodePart` adds at most the `%` byte. -/
theorem length_decodePart_le (part : List U8) : (decodePart part).length ≤ part.length + 1 := by
  unfold decodePart
  split
  · split <;> simp only [List.length_cons, add_le_add_iff_right, le_add_iff_nonneg_right, zero_le,
      ↓Char.isValue, Std.le_refl]
  · simp only [↓Char.isValue, List.length_cons, Std.le_refl]

/-- `intercalate [a]` of a non-empty list: the first part, then `a` before each later part. -/
theorem intercalate_singleton_cons {α : Type*} (a : α) (ys : List (List α)) :
    ∀ x : List α, [a].intercalate (x :: ys) = x ++ ys.flatMap (a :: ·) := by
  induction ys with
  | nil => simp only [List.intercalate_singleton, List.flatMap_nil, List.append_nil, implies_true]
  | cons y ys ih =>
    intro x
    rw [List.intercalate_cons_cons, ih]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.flatMap_cons]

/-- **Percent-decoding never lengthens**. -/
theorem length_decodePercent_le (bytes : List U8) :
    (decodePercent bytes).length ≤ bytes.length := by
  have hparts : ∀ parts : List (List U8),
      (parts.flatMap decodePart).length ≤ (parts.flatMap (asciiByte '%' :: ·)).length := by
    intro parts
    induction parts with
    | nil => simp only [List.flatMap_nil, List.length_nil, ↓Char.isValue, Std.le_refl]
    | cons p ps ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have := length_decodePart_le p
      omega
  unfold decodePercent
  conv_rhs => rw [← List.intercalate_splitOn (asciiByte '%') (xs := bytes)]
  cases bytes.splitOn (asciiByte '%') with
  | nil => simp only [List.length_nil, ↓Char.isValue, List.intercalate_nil, Std.le_refl]
  | cons first parts =>
    rw [intercalate_singleton_cons, List.length_append, List.length_append]
    have := hparts parts
    omega

end Proofs.Model.Skill

namespace Defs.Skill

open Proofs.Model.Skill

/-! ## Skill URIs -/

/-- **What `skillNameOfUri` accepts**: it returns `some segment` exactly when the URI has no `?`
or `#`, and is `dir ++ segment ++ "/SKILL.md"` for a non-empty `segment` without `/` and a `dir`
that is empty or ends in `/`. So a URI that names a skill ends in `<segment>/SKILL.md`, with the
segment at the start or after a `/`. -/
theorem skillNameOfUri_eq_some_iff (uri segment : List U8) :
    skillNameOfUri uri = some segment ↔
      (∀ b ∈ uri, isQueryOrFragmentStart b = false) ∧ segment ≠ [] ∧ asciiByte '/' ∉ segment ∧
        ∃ dir, uri = dir ++ segment ++ utf8Bytes "/SKILL.md" ∧
          (dir = [] ∨ dir.getLast? = some (asciiByte '/')) := by
  have hsuf : utf8Bytes "/SKILL.md" = asciiByte '/' :: skillMd := by decide +kernel
  unfold skillNameOfUri stripSuffix lastSegment
  rw [hsuf]
  generalize asciiByte '/' :: skillMd = suf
  cases h : uri.any isQueryOrFragmentStart
  · have hq : ∀ b ∈ uri, isQueryOrFragmentStart b = false := by
      simpa only [Bool.not_eq_true] using List.any_eq_false.1 h
    rw [iff_true_intro hq, true_and]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hs : suf.isSuffixOf uri = true
    · obtain ⟨path, rfl⟩ := List.isSuffixOf_iff_suffix.1 hs
      have htake : (path ++ suf).take ((path ++ suf).length - suf.length) = path := by
        simp only [List.length_append, add_tsub_cancel_right, List.take_left']
      simp only [hs, ↓reduceIte, htake, List.append_cancel_right_eq]
      constructor
      · intro h1
        by_cases hne : (path.splitOn (asciiByte '/')).getLastD [] = []
        · rw [ite_eq_left hne] at h1
          cases h1
        · rw [ite_eq_right hne, Option.some.injEq] at h1
          subst h1
          obtain ⟨h2, d, h3, h4⟩ := (getLastD_splitOn_eq_iff (asciiByte '/') path _).1 rfl
          exact ⟨hne, h2, d, h3, h4⟩
      · rintro ⟨hne, hs', dir, rfl, hd⟩
        rw [getLastD_splitOn_append _ _ _ hs' hd]
        simp only [hne, ↓reduceIte]
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff, not_and,
        not_exists]
      rintro - - dir rfl -
      exact hs (List.isSuffixOf_iff_suffix.2 (List.suffix_append _ _))
  · simp only [↓reduceIte, reduceCtorEq, false_iff, not_and]
    intro hq
    obtain ⟨b, hb, hb'⟩ := List.any_eq_true.1 h
    rw [hq b hb] at hb'
    exact absurd hb' Bool.false_ne_true

/-- **A URI without a scheme or directory names a skill**: `billing/SKILL.md` names the skill
`billing` (the segment is at the start of the URI). -/
theorem skillNameOfUri_billing :
    skillNameOfUri (utf8Bytes "billing/SKILL.md") = some (utf8Bytes "billing") := by
  have hq : (utf8Bytes "billing/SKILL.md").all (fun b => !isQueryOrFragmentStart b) = true := by
    decide +kernel
  have hs : asciiByte '/' ∉ utf8Bytes "billing" := by decide +kernel
  have hu : utf8Bytes "billing/SKILL.md" = [] ++ utf8Bytes "billing" ++ utf8Bytes "/SKILL.md" := by
    decide +kernel
  have hne : utf8Bytes "billing" ≠ [] := by decide +kernel
  refine (skillNameOfUri_eq_some_iff _ _).2 ⟨?_, hne, hs, [], hu, Or.inl rfl⟩
  intro b hb
  simpa only [Bool.not_eq_eq_eq_not, Bool.not_true] using List.all_eq_true.1 hq b hb

/-! ## Skill names -/

/-- **The skill-name rule as words**: `cs` passes `nameCharsValid alnum` exactly when it has at
most 64 characters and is one or more non-empty words of `alnum` characters joined by single
`-`. -/
theorem nameCharsValid_iff_words (alnum : Char → Bool) (cs : List Char) :
    nameCharsValid alnum cs = true ↔
      cs.length ≤ 64 ∧ ∃ words : List (List Char), words ≠ [] ∧
        (∀ w ∈ words, w ≠ [] ∧ ∀ c ∈ w, alnum c = true) ∧ cs = List.intercalate ['-'] words := by
  rw [nameCharsValid_eq_true_iff]
  constructor
  · rintro ⟨hne, hl, h⟩
    exact ⟨hl, exists_words_of_nameRule alnum _ cs rfl hne h⟩
  · rintro ⟨hl, words, hw1, hw2, rfl⟩
    obtain ⟨h, c, t, hct, -⟩ := nameRule_intercalate alnum words hw1 hw2
    exact ⟨hct ▸ List.cons_ne_nil c t, hl, h⟩

/-! ## `validateResult` -/

/-- **`validateResult` does not depend on `_meta`**. -/
theorem validateResult_with_meta (s : Skill) (m : Option rmcp.model.meta.MetaObject) :
    validateResult { s with «meta» := m } = validateResult s := rfl

/-- **`validateResult` is `Ok` exactly for a valid skill** (`ValidSkill`): the order of the
checks matters only for which error is returned. -/
theorem validateResult_eq_ok_iff (s : Skill) : validateResult s = .Ok () ↔ ValidSkill s := by
  obtain ⟨uri, ⟨nm, desc, extra⟩, res, mt⟩ := s
  cases hu : skillNameOfUri (utf8Bytes uri) with
  | none => simp only [validateResult, hu, reduceCtorEq, ValidSkill, false_and, exists_const]
  | some enc =>
    by_cases hn : isSkillName nm = true
    · by_cases hm : nameMatchesSegment enc nm = true
      · cases res with
        | Dynamic => simp only [validateResult, hu, hn, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, hm, ValidSkill, Option.some.injEq, exists_eq_left', reduceCtorEq,
            IsEmpty.forall_iff, implies_true, and_self]
        | Files files =>
          have hv : ValidSkill ⟨uri, ⟨nm, desc, extra⟩, .Files files, mt⟩ ↔
              ValidManifest uri files.val := by
            simp only [ValidSkill, hu, hn, hm, Option.some.injEq, exists_eq_left', true_and]
            exact ⟨fun h => h files rfl, fun h files' he => by cases he; exact h⟩
          rw [hv, ValidManifest]
          simp only [validateResult, hu, hn, hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          by_cases hf : files.val.any (fun f => f.uri == uri) = true
          · have hf' : ∃ f ∈ files.val, f.uri = uri := by
              obtain ⟨f, hf1, hf2⟩ := List.any_eq_true.1 hf
              exact ⟨f, hf1, beq_iff_eq.1 hf2⟩
            simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            cases hff : firstFileFault uri [] files.val with
            | none =>
              have := firstFileFault_eq_none_iff.1 hff
              exact iff_of_true rfl ⟨hf', this.1, this.2.1⟩
            | some e =>
              refine iff_of_false nofun fun h => ?_
              have := firstFileFault_eq_none_iff (skillUri := uri) (earlier := []).2
                ⟨h.2.1, h.2.2, fun _ _ _ hg => nomatch hg⟩
              rw [hff] at this
              cases this
          · simp only [Bool.not_eq_true] at hf
            simp only [hf, Bool.not_false, ↓reduceIte]
            refine iff_of_false nofun fun h => ?_
            obtain ⟨f, hf1, hf2⟩ := h.1
            have := List.any_eq_false.1 hf f hf1
            simp only [hf2, BEq.rfl, not_true_eq_false] at this
      · simp only [validateResult, hu, hn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hm,
          Bool.not_false, reduceCtorEq, ValidSkill, Option.some.injEq, exists_eq_left', true_and,
          false_and]
    · simp only [validateResult, hu, hn, Bool.not_false, ↓reduceIte, reduceCtorEq, ValidSkill,
        Option.some.injEq, exists_eq_left', Bool.false_eq_true, false_and, and_false]

/-- **When `validate` reports `UriNotSkillMd`** (check 1): exactly when the URI names no skill,
with the skill's URI as payload. -/
theorem validateResult_eq_err_uriNotSkillMd_iff (s : Skill) (u : String) :
    validateResult s = .Err (.UriNotSkillMd u) ↔
      skillNameOfUri (utf8Bytes s.uri) = none ∧ u = s.uri := by
  obtain ⟨uri, ⟨nm, desc, extra⟩, res, mt⟩ := s
  unfold validateResult
  simp only
  cases hu : skillNameOfUri (utf8Bytes uri) with
  | none => simp only [eq_comm, core.result.Result.Err.injEq,
      SkillValidationError.UriNotSkillMd.injEq, true_and]
  | some enc =>
    simp only [reduceCtorEq, false_and, iff_false]
    split
    · simp only [core.result.Result.Err.injEq, reduceCtorEq, not_false_eq_true]
    · split
      · simp only [core.result.Result.Err.injEq, reduceCtorEq, not_false_eq_true]
      · cases res with
        | Dynamic => simp only [reduceCtorEq, not_false_eq_true]
        | Files files =>
          simp only
          split
          · simp only [core.result.Result.Err.injEq, reduceCtorEq, not_false_eq_true]
          · cases hff : firstFileFault uri [] files.val with
            | none => simp only [reduceCtorEq, not_false_eq_true]
            | some e =>
              simp only [core.result.Result.Err.injEq]
              rintro rfl
              rcases firstFileFault_eq_some_kind hff with ⟨_, _, ⟨⟩⟩ | ⟨_, ⟨⟩⟩ | ⟨_, _, ⟨⟩⟩

/-- **When `validate` reports `InvalidName`** (check 2): exactly when the URI names a skill and
the frontmatter name is not a valid skill name, with the name as payload. -/
theorem validateResult_eq_err_invalidName_iff (s : Skill) (n : String) :
    validateResult s = .Err (.InvalidName n) ↔
      (skillNameOfUri (utf8Bytes s.uri)).isSome ∧ isSkillName s.frontmatter.«name» = false ∧
        n = s.frontmatter.«name» := by
  rw [validateResult_eq_err_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨enc, h1, h2, h⟩ | ⟨_, -, -, -, h⟩ | ⟨_, _, -, -, -, -, -, h⟩ |
      ⟨_, _, -, -, -, -, -, h⟩)
    · simp only [reduceCtorEq] at h
    · simp only [SkillValidationError.InvalidName.injEq] at h
      exact ⟨by simp only [h1, Option.isSome_some], h2, h.symm⟩
    · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
    · rcases firstFileFault_eq_some_kind h with ⟨_, _, ⟨⟩⟩ | ⟨_, ⟨⟩⟩ | ⟨_, _, ⟨⟩⟩
  · rintro ⟨h1, h2, rfl⟩
    obtain ⟨enc, h1⟩ := Option.isSome_iff_exists.1 h1
    exact Or.inr (Or.inl ⟨enc, h1, h2, rfl⟩)

/-- **When `validate` reports `NameMismatch`** (check 3): exactly when the URI names a skill with
segment `encoded`, the name is valid, and the segment does not match the name, with the skill's
URI and name as payload. -/
theorem validateResult_eq_err_nameMismatch_iff (s : Skill) (u n : String) :
    validateResult s = .Err (.NameMismatch u n) ↔
      ∃ encoded, skillNameOfUri (utf8Bytes s.uri) = some encoded ∧
        isSkillName s.frontmatter.«name» = true ∧
        nameMatchesSegment encoded s.frontmatter.«name» = false ∧
        u = s.uri ∧ n = s.frontmatter.«name» := by
  rw [validateResult_eq_err_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨_, -, -, h⟩ | ⟨enc, h1, h2, h3, h⟩ | ⟨_, _, -, -, -, -, -, h⟩ |
      ⟨_, _, -, -, -, -, -, h⟩)
    · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
    · simp only [SkillValidationError.NameMismatch.injEq] at h
      exact ⟨enc, h1, h2, h3, h.1.symm, h.2.symm⟩
    · simp only [reduceCtorEq] at h
    · rcases firstFileFault_eq_some_kind h with ⟨_, _, ⟨⟩⟩ | ⟨_, ⟨⟩⟩ | ⟨_, _, ⟨⟩⟩
  · rintro ⟨enc, h1, h2, h3, rfl, rfl⟩
    exact Or.inr (Or.inr (Or.inl ⟨enc, h1, h2, h3, rfl⟩))

/-- **When `validate` reports `MissingSkillMd`** (check 5): exactly when the URI names a skill
with segment `encoded`, the name is valid and matches the segment, `resources` is a manifest
`files` (not `"dynamic"`), and no file of it has exactly the skill's URI, with the skill's URI as
payload (upstream lines 297–299, patched lines 300–311). -/
theorem validateResult_eq_err_missingSkillMd_iff (s : Skill) (u : String) :
    validateResult s = .Err (.MissingSkillMd u) ↔
      ∃ encoded files, skillNameOfUri (utf8Bytes s.uri) = some encoded ∧
        isSkillName s.frontmatter.«name» = true ∧
        nameMatchesSegment encoded s.frontmatter.«name» = true ∧
        s.resources = .Files files ∧ (∀ f ∈ files.val, f.uri ≠ s.uri) ∧ u = s.uri := by
  rw [validateResult_eq_err_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨_, -, -, h⟩ | ⟨_, -, -, -, h⟩ | ⟨enc, files, h1, h2, h3, h4, h5, h⟩ |
      ⟨_, _, -, -, -, -, -, h⟩)
    · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
    · simp only [SkillValidationError.MissingSkillMd.injEq] at h
      exact ⟨enc, files, h1, h2, h3, h4, h5, h.symm⟩
    · rcases firstFileFault_eq_some_kind h with ⟨_, _, ⟨⟩⟩ | ⟨_, ⟨⟩⟩ | ⟨_, _, ⟨⟩⟩
  · rintro ⟨enc, files, h1, h2, h3, h4, h5, rfl⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨enc, files, h1, h2, h3, h4, h5, rfl⟩)))

/-- **When `validate` reports a per-file error** (check 6): for an error `e` of the kind
`ResourceOutsideSkill`, `DuplicateResource` or `MalformedDigest`, `validate` reports `e` exactly
when checks 1–5 pass (the URI names a skill with segment `encoded`, the name is valid and matches
the segment, `resources` is a manifest `files` that has a file with exactly the skill's URI) and
`e` is the fault of the first faulty file of the manifest (`firstFileFault`, with its payload;
upstream lines 300–317, patched lines 312–337). -/
theorem validateResult_eq_err_iff_firstFileFault_eq_some (s : Skill) (e : SkillValidationError)
    (he : (∃ uri skillUri, e = .ResourceOutsideSkill uri skillUri) ∨
      (∃ uri, e = .DuplicateResource uri) ∨ (∃ uri digest, e = .MalformedDigest uri digest)) :
    validateResult s = .Err e ↔
      ∃ encoded files, skillNameOfUri (utf8Bytes s.uri) = some encoded ∧
        isSkillName s.frontmatter.«name» = true ∧
        nameMatchesSegment encoded s.frontmatter.«name» = true ∧
        s.resources = .Files files ∧ (∃ f ∈ files.val, f.uri = s.uri) ∧
        firstFileFault s.uri [] files.val = some e := by
  rw [validateResult_eq_err_iff]
  constructor
  · rintro (⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ | ⟨_, -, -, -, rfl⟩ | ⟨_, _, -, -, -, -, -, rfl⟩ | h)
    · rcases he with ⟨_, _, ⟨⟩⟩ | ⟨_, ⟨⟩⟩ | ⟨_, _, ⟨⟩⟩
    · rcases he with ⟨_, _, ⟨⟩⟩ | ⟨_, ⟨⟩⟩ | ⟨_, _, ⟨⟩⟩
    · rcases he with ⟨_, _, ⟨⟩⟩ | ⟨_, ⟨⟩⟩ | ⟨_, _, ⟨⟩⟩
    · rcases he with ⟨_, _, ⟨⟩⟩ | ⟨_, ⟨⟩⟩ | ⟨_, _, ⟨⟩⟩
    · exact h
  · exact fun h => Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- **`validate` never reports `DuplicateSkill`**: that error belongs to `validate_skills`
(upstream line 429, patched line 493). With the five `validateResult_eq_err_…` statements above,
every `Err` case of `validateResult` is characterised. -/
theorem validateResult_ne_err_duplicateSkill (s : Skill) (u : String) :
    validateResult s ≠ .Err (.DuplicateSkill u) := by
  intro h
  rw [validateResult_eq_err_iff] at h
  rcases h with ⟨-, h⟩ | ⟨_, -, -, h⟩ | ⟨_, -, -, -, h⟩ | ⟨_, _, -, -, -, -, -, h⟩ |
    ⟨_, _, -, -, -, -, -, h⟩
  · simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h
  · rcases firstFileFault_eq_some_kind h with ⟨_, _, ⟨⟩⟩ | ⟨_, ⟨⟩⟩ | ⟨_, _, ⟨⟩⟩

/-- **Well-formed digests never give `MalformedDigest`**: if every file of `files` has a
well-formed digest (e.g. an entry made by `from_bytes`, `SkillResource.isSha256Digest_from_bytes`),
the first file fault is not a `MalformedDigest`. -/
theorem firstFileFault_ne_malformedDigest (skillUri : String) (earlier files : List SkillResource)
    (h : ∀ f ∈ files, isSha256Digest (utf8Bytes f.digest) = true) (uri digest : String) :
    firstFileFault skillUri earlier files ≠ some (.MalformedDigest uri digest) := by
  induction files generalizing earlier with
  | nil => simp only [firstFileFault, ne_eq, reduceCtorEq, not_false_eq_true]
  | cons file rest ih =>
    have hd := h file List.mem_cons_self
    rw [firstFileFault]
    cases hf : fileFault skillUri earlier file with
    | none =>
      rw [Option.none_or]
      exact ih _ (fun f hf => h f (List.mem_cons_of_mem _ hf))
    | some e =>
      rw [Option.some_or]
      intro he
      rw [Option.some.injEq] at he
      subst he
      unfold fileFault at hf
      split at hf
      · cases hf
      · split_ifs at hf with h1 h2
        · cases hf
        · rw [hd, Bool.not_true] at h2
          cases h2

/-! ## `validateSkillsResult` -/

/-- **`validateSkillsResult` is `Ok` exactly for a valid listing** (`ValidSkills`). -/
theorem validateSkillsResult_eq_ok_iff (skills : List Skill) :
    validateSkillsResult skills = .Ok () ↔ ValidSkills skills := by
  have key : firstSkillFault [] skills = none ↔ ValidSkills skills := by
    rw [firstSkillFault_eq_none_iff, ValidSkills]
    simp only [validateResult_eq_ok_iff, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
  rw [← key, validateSkillsResult]
  cases firstSkillFault [] skills with
  | none => exact iff_of_true rfl rfl
  | some e => exact iff_of_false nofun nofun

/-- **One skill**: the expected result of `validate_skills` on `[s]` is that of `validate s`. -/
theorem validateSkillsResult_singleton (s : Skill) :
    validateSkillsResult [s] = validateResult s := by
  unfold validateSkillsResult firstSkillFault
  cases h : validateResult s with
  | Err e => rfl
  | Ok u => rfl

/-- **A sublist of a valid listing is valid**, in particular a prefix `l₁` of `l₁ ++ l₂`: each
skill stays valid and distinct keys stay distinct. The concatenation of two valid listings
need not be valid: they can share a key. -/
theorem ValidSkills.sublist {l₁ l₂ : List Skill} (h : l₁.Sublist l₂) (hv : ValidSkills l₂) :
    ValidSkills l₁ :=
  ⟨fun s hs => hv.1 s (h.subset hs), hv.2.sublist (h.map skillKey)⟩

/-- **An error of a prefix is the error of the listing**: the walk reaches the faulty skill of
`l₁` before any skill of `l₂`. -/
theorem validateSkillsResult_append_of_eq_err {l₁ : List Skill} (l₂ : List Skill)
    {e : SkillValidationError} (h : validateSkillsResult l₁ = .Err e) :
    validateSkillsResult (l₁ ++ l₂) = .Err e := by
  unfold validateSkillsResult at h ⊢
  cases hf : firstSkillFault [] l₁ with
  | none =>
    rw [hf] at h
    cases h
  | some e' =>
    rw [hf] at h
    rw [firstSkillFault_append_of_eq_some l₂ hf]
    exact h

/-! ## The NFKC premise -/

/-- **The NFKC premise (N) from the NFKC expansion bound** (bridge lemma). The premise `hexp` is a
law about the opaque `ExtModel.nfkc`, over every input: the NFKC form of `m` characters has at
most `18 * m` characters. It is true of the real function: NFKC is the full compatibility
decomposition of each character, then canonical ordering (a permutation), then canonical
composition (which only merges characters) (UAX #15, "Unicode Normalization Forms"), so it is at
most as long as the sum of the decompositions of the characters, and the longest compatibility
decomposition has 18 characters (`U+FDFA` ARABIC LIGATURE SALLALLAHOU ALAYHE WASALLAM; the
Unicode Normalization FAQ gives 18 as the maximum NFKC expansion factor in code points). Evidence
for the pinned `unicode-normalization 0.1.26` (Unicode 18.0.0 tables, `src/tables.rs` line 18;
`nfkc` is `Recompositions` over `Decompositions`, `src/recompose.rs`, `src/decompose.rs`), a Rust
run of 2026-11-25 against the pinned crate: over all 1,112,064 scalar values the largest
`c.to_string().nfkc().count()` and `nfkd().count()` are 18, attained at `U+FDFA`; over
2,000,000 random strings of 1 to 12 characters drawn from the 14,670 characters that decompose,
compose or combine (Hangul included), `nfkc().count() ≤ nfkd().count()`, `nfkd().count()` is the
sum over the characters and is at most `18 *` the length, with no exception. The byte premises
give `4 * 18 * chars ≤ isize::MAX` for the name, and for the URI segment, whose decoded string
has at most as many characters as bytes, at most as many as the encoded segment, at most as many
as the URI. A name and a URI of at most `isize::MAX / 72` bytes each (more than `2^56` bytes,
64 PiB) meet them. -/
theorem NfkcFits.of_utf8ByteSize_le (s : Skill)
    (hexp : ∀ cs, (ExtModel.nfkc cs).length ≤ 18 * cs.length)
    (hname : 72 * s.frontmatter.«name».utf8ByteSize ≤ ExtModel.maxStringBytes)
    (huri : 72 * s.uri.utf8ByteSize ≤ ExtModel.maxStringBytes) : NfkcFits s := by
  intro encoded he
  obtain ⟨-, -, -, dir, hu, -⟩ := (skillNameOfUri_eq_some_iff _ _).1 he
  have hlen : encoded.length ≤ s.uri.utf8ByteSize := by
    rw [← Proofs.External.Utf8.length_utf8, ← Proofs.External.Utf8.utf8Bytes_eq_utf8, hu]
    simp only [List.length_append]
    omega
  have hn1 := hexp s.frontmatter.«name».toList
  have hn2 := length_toList_le_utf8ByteSize s.frontmatter.«name»
  refine ⟨by omega, fun _ segment hseg => ?_⟩
  have hs1 := hexp segment.toList
  have hs2 := length_toList_le_utf8ByteSize segment
  have hs3 : segment.utf8ByteSize = (decodePercent encoded).length := by
    rw [(Proofs.External.Utf8.strOfBytes?_eq_some_iff _ _).1 hseg,
      Proofs.External.Utf8.length_utf8]
  have hs4 := length_decodePercent_le encoded
  omega

end Defs.Skill
