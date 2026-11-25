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
public import Proofs.Model.Skill.ValidateHelpers
public import Proofs.Model.Skill.Verify
public import Proofs.Model.Skill.Model

@[expose] public section

/-!
# Spec theorems for `Skill::validate` (K13) and `validate_skills` (K16)

`Skill::validate` checks, in order, that the URI names a skill (`skill_name_from_uri`, K14), that
the frontmatter name is a valid skill name, that the decoded URI segment matches the name in NFKC
form, and, for a manifest, that it lists the skill's own `SKILL.md` and that every file lies
within the skill's directory, is listed once (by its normalised key) and has a well-formed
digest. `validate_skills` validates each skill in order and rejects a repeated percent-normalised
URI. Both return the first error (`Defs.Skill.validateResult`, `Defs.Skill.validateSkillsResult`).

Source: "crates/rmcp/src/model/skill.rs", lines 279–338 (`validate`) and 488–497
(`validate_skills`) in the patched copy (patches 01–04 on origin/main 7caec76; upstream lines
277–319 and 424–433).

Proof: the private helpers are used through their spec theorems
(`Proofs.Model.Skill.ValidateHelpers`), K14 and K15 through theirs
(`Proofs.Model.Skill.Verify`); each extracted loop is proved with `loop.spec_decr_nat` against
`Defs.Skill.firstFileFault` (the file loop), `List.any` (the `SKILL.md` lookup) and
`Defs.Skill.firstSkillFault` (the skills loop). The corollaries combine K13 and K16 with the laws
of `Proofs.Model.Skill.Model`.
-/

open Aeneas Aeneas.Std Result
open rmcp
open Defs (utf8Bytes)
open Defs.Skill

namespace rmcp.model.skill

open ExtModel Proofs.External.Byte Proofs.External.Utf8 Proofs.External.Skill Proofs.Model.Skill

/-- The `SKILL.md` lookup of `validate` (patched lines 302–308): whether a file from index `i`
on has exactly the URI `s`. -/
theorem Skill.validate_loop0_spec (s : String) (files : alloc.vec.Vec SkillResource) (i : Usize)
    (hi : i.val ≤ files.length) :
    Skill.validate_loop0 s files i ⦃ (result : Bool) =>
      result = (files.val.drop i.val).any (fun f => f.uri == s) ⦄ := by
  unfold Skill.validate_loop0
  apply loop.spec_decr_nat (fun j : Usize => files.length - j.val)
    (fun j => j.val ≤ files.length ∧
      (files.val.drop j.val).any (fun f => f.uri == s) =
        (files.val.drop i.val).any (fun f => f.uri == s))
  · rintro j ⟨hj, heq⟩
    unfold Skill.validate_loop0.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : j.val < files.val.length := by scalar_tac
      rw [List.drop_eq_getElem_cons hlt', List.any_cons] at heq
      step as ⟨sr, hsr⟩
      subst hsr
      step as ⟨b, hb⟩
      have hbe : (files.val[j.val].uri == s) = b := by rw [hb]; rfl
      rw [hbe] at heq
      split
      · rename_i hbt
        rw [WP.spec_ok, ← heq, hbt, Bool.true_or]
      · rename_i hbf
        rw [Bool.not_eq_true] at hbf
        rw [hbf, Bool.false_or] at heq
        step as ⟨j2, hj2⟩
        exact ⟨by simp only [alloc.vec.Vec.length] at hlt' ⊢; omega, by rw [hj2, heq],
          by simp only [alloc.vec.Vec.length] at hlt' ⊢; omega⟩
    · rename_i hge
      have hge' : files.val.length ≤ j.val := by scalar_tac
      rw [WP.spec_ok, ← heq, List.drop_eq_nil_of_le hge', List.any_nil]
  · exact ⟨hi, rfl⟩

/-- The file loop of `validate` (patched lines 315–336), from index `i` with the keys of the files
before `i` in `seen`: the first faulty file (`firstFileFault`). -/
theorem Skill.validate_loop1_spec (s : String) (files : alloc.vec.Vec SkillResource)
    (seen : std.collections.hash.set.HashSet String std.hash.random.RandomState
      alloc.alloc.Global) (i : Usize)
    (hi : i.val ≤ files.length) (hs : UsizeFits s)
    (hfiles : ∀ f ∈ files.val, UriFits f.uri ∧ UsizeFits f.digest)
    (hseen : ∀ k, k ∈ seen.elements ↔ ∃ g ∈ files.val.take i.val, fileKey s g = some (utf8 k)) :
    Skill.validate_loop1 s files seen i ⦃ (result : core.result.Result Unit SkillValidationError) =>
      result = match firstFileFault s (files.val.take i.val) (files.val.drop i.val) with
        | some e => .Err e
        | none => .Ok () ⦄ := by
  unfold Skill.validate_loop1
  have hmax := maxStringBytes_le_usize_max
  apply loop.spec_decr_nat
    (fun st : std.collections.hash.set.HashSet String std.hash.random.RandomState
      alloc.alloc.Global × Usize => files.length - st.2.val)
    (fun st => st.2.val ≤ files.length ∧
      (∀ k, k ∈ st.1.elements ↔ ∃ g ∈ files.val.take st.2.val, fileKey s g = some (utf8 k)) ∧
      firstFileFault s (files.val.take st.2.val) (files.val.drop st.2.val) =
        firstFileFault s (files.val.take i.val) (files.val.drop i.val))
  · rintro ⟨seen', j⟩ ⟨hj, hseen', heq⟩
    dsimp only at hj hseen' heq ⊢
    unfold Skill.validate_loop1.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : j.val < files.val.length := by scalar_tac
      rw [List.drop_eq_getElem_cons hlt', firstFileFault] at heq
      step as ⟨file, hfile⟩
      subst hfile
      have hf := hfiles _ (List.getElem_mem hlt')
      have huri : (files.val[j.val]).uri.utf8ByteSize ≤ Usize.max := by
        have := hf.1; unfold UriFits at this; omega
      step with alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec s hs as ⟨s1, hs1⟩
      step with alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec _ huri as ⟨s2, hs2⟩
      step with manifest_resource_key_spec s1 s2 s (files.val[j.val]).uri hs1 hs2 (by
        rw [hs2, length_utf8]; exact hf.1) as ⟨o, ho⟩
      rw [hs1, hs2] at ho
      have hfk : fileKey s files.val[j.val] = o.map utf8 := ho.symm
      cases o with
      | none =>
        step as ⟨s3, hs3⟩
        step as ⟨s4, hs4⟩
        subst hs3 hs4
        rw [← heq, fileFault, hfk]
        rfl
      | some key =>
        rw [Option.map_some] at hfk
        dsimp only
        step with std.collections.hash.set.HashSet.insert_spec alloc.string.String.Insts.CoreCmpEq
            alloc.string.String.Insts.CoreHashHash
            std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher seen' key
            string_eq_inst_spec as ⟨b, seen1, hp⟩
        have hany : ((files.val.take j.val).any fun g => fileKey s g == some (utf8 key)) =
            decide (key ∈ seen'.elements) := by
          rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff, hseen' key]
          simp only [beq_iff_eq]
        rcases hp with ⟨hmem, hp⟩ | ⟨hnmem, hp⟩
        · obtain ⟨rfl, rfl⟩ := hp
          rw [ite_eq_right Bool.false_ne_true]
          step as ⟨s3, hs3⟩
          subst hs3
          rw [← heq, fileFault, hfk]
          simp only [hany, hmem, decide_true, ↓reduceIte]
          rfl
        · obtain ⟨rfl, rfl⟩ := hp
          rw [ite_eq_left rfl]
          step with alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec _ hf.2 as ⟨s3, hs3⟩
          step as ⟨b1, hb1⟩
          rw [hs3] at hb1
          have hff : ∀ e, fileFault s (files.val.take j.val) files.val[j.val] = e →
              e = if isSha256Digest (utf8 (files.val[j.val]).digest) then none
                else some (.MalformedDigest (files.val[j.val]).uri (files.val[j.val]).digest) := by
            rintro e rfl
            rw [fileFault, hfk]
            simp only [hany, hnmem, decide_false, Bool.false_eq_true, ↓reduceIte,
              utf8Bytes_eq_utf8]
            by_cases hd : isSha256Digest (utf8 (files.val[j.val]).digest) = true
            · simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            · simp only [hd, Bool.not_false, ↓reduceIte, Bool.false_eq_true]
          have hff' := hff _ rfl
          split
          · rename_i hb1t
            rw [hb1t, eq_comm] at hb1
            rw [hb1, ite_eq_left rfl] at hff'
            step as ⟨j2, hj2⟩
            refine ⟨by simp only [alloc.vec.Vec.length] at hlt' ⊢; omega, ?_, ?_, ?_⟩
            · intro k
              rw [hj2, List.take_add_one, List.getElem?_eq_getElem hlt', Option.toList_some]
              simp only [List.mem_append, List.mem_singleton, hseen' k]
              constructor
              · rintro (⟨g, hg, hgk⟩ | rfl)
                · exact ⟨g, Or.inl hg, hgk⟩
                · exact ⟨_, Or.inr rfl, hfk⟩
              · rintro ⟨g, hg, hgk⟩
                rcases hg with hg | rfl
                · exact Or.inl ⟨g, hg, hgk⟩
                · right
                  rw [hfk] at hgk
                  exact (utf8_injective (Option.some.inj hgk)).symm
            · rw [hj2, ← heq, hff', Option.none_or, List.take_add_one,
                List.getElem?_eq_getElem hlt', Option.toList_some]
            · simp only [alloc.vec.Vec.length] at hlt' ⊢; omega
          · rename_i hb1f
            step as ⟨s4, hs4⟩
            step as ⟨s5, hs5⟩
            subst hs4 hs5
            have : isSha256Digest (utf8 (files.val[j.val]).digest) = false := by
              rw [← hb1]
              exact Bool.eq_false_iff.2 hb1f
            rw [this] at hff'
            rw [← heq, hff']
            rfl
    · rename_i hge
      have hge' : files.val.length ≤ j.val := by scalar_tac
      rw [WP.spec_ok, ← heq, List.drop_eq_nil_of_le hge', firstFileFault]
  · exact ⟨hi, hseen, rfl⟩

end rmcp.model.skill

/-! ## K13: `Skill::validate` -/

namespace rmcp.model.skill.Skill

open ExtModel Proofs.External.Byte Proofs.External.Utf8 Proofs.External.Skill Proofs.Model.Skill

/-- **Spec theorem for `rmcp::model::skill::Skill::validate`** (K13)

Returns `validateResult self` (`Defs.Skill`): the error of the first failing check, in the Rust
order, with its payload, else `Ok(())` (upstream lines 277–319; patched lines 279–338, hunk H2):
1. `UriNotSkillMd(uri)` if the URI names no skill (`skillNameOfUri`, K14);
2. `InvalidName(name)` if the NFKC form of the name is not 1 to 64 characters, each a letter of
   Unicode General_Category `Ll`, `Lm` or `Lo` or a number of category `Nd`, `Nl` or `No`
   (`isNameAlnum`, upstream lines 343–349), or a `-` between two such characters (single inner
   hyphens; `isSkillName`, upstream lines 335–355);
3. `NameMismatch { uri, name }` if the percent-decoded URI segment is not UTF-8 or its NFKC form
   differs from the name's (`nameMatchesSegment`);
4. `Ok(())` if `resources` is `"dynamic"`;
5. `MissingSkillMd(uri)` if no manifest file has exactly the skill's URI;
6. for the first file, in manifest order, that is faulty (`firstFileFault`):
   `ResourceOutsideSkill { uri: file.uri, skill_uri }` (`manifest_resource_key` returns `None`:
   the URI is not a file inside the skill's directory; `manifestKey`),
   `DuplicateResource(file.uri)` (an earlier file has the same key),
   `MalformedDigest { uri: file.uri, digest }` (`isSha256Digest` fails);
7. otherwise `Ok(())`.
Premises: (V) `h_sizes`; (N) `h_nfkc` (patch-induced; see `Defs.Skill.NfkcFits.of_utf8ByteSize_le`).
Not covered: (H). -/
@[step]
theorem validate_spec (self : Skill) (h_sizes : SkillFits self) (h_nfkc : NfkcFits self) :
    validate self ⦃ (result : core.result.Result Unit SkillValidationError) =>
      result = validateResult self ⦄ := by
  obtain ⟨uri, fm, res, m⟩ := self
  obtain ⟨hu, hn, hfiles⟩ := h_sizes
  dsimp only at hu hn hfiles h_nfkc ⊢
  unfold validate validateResult
  dsimp only
  step with alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec uri hu as ⟨s, hs⟩
  step as ⟨o, ho⟩
  rw [hs] at ho
  cases o with
  | none =>
    have hnone : skillNameOfUri (utf8Bytes uri) = none := ho.symm
    rw [hnone]
    step as ⟨s1, hs1⟩
    subst hs1
    rfl
  | some enc =>
    have hsk : skillNameOfUri (utf8Bytes uri) = some enc.val := ho.symm
    rw [hsk]
    dsimp only
    obtain ⟨hn1, hn2⟩ := h_nfkc enc.val hsk
    step with name_spec ⟨uri, fm, res, m⟩ hn as ⟨nm, hnm⟩
    step with is_valid_skill_name_spec nm fm.«name» hnm hn1 as ⟨b, hb⟩
    split
    · rename_i hbt
      rw [hbt, eq_comm] at hb
      rw [hb]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      step as ⟨o1, ho1⟩
      rw [percentDecode_eq_decodePercent] at ho1
      subst ho1
      apply WP.spec_bind (Pₘ := fun r => r = nameMatchesSegment enc.val fm.«name»)
      · unfold nameMatchesSegment
        split
        · rename_i hseg
          rw [hseg]; exact (WP.spec_ok _).2 rfl
        · rename_i seg hseg
          rw [hseg]
          have hsegb := (strOfBytes?_eq_some_iff _ _).1 hseg
          have hseglen : seg.utf8ByteSize ≤ Usize.max := by
            have h1 := length_decodePercent_le enc.val
            have h2 := enc.property
            rw [← length_utf8, ← hsegb]; omega
          step with alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec seg hseglen
            as ⟨s1, hs1⟩
          step with model.skill.prim.nfkc_spec s1 seg hs1 (hn2 hb seg hseg) as ⟨v, hv⟩
          step with model.skill.prim.nfkc_spec nm fm.«name» hnm hn1 as ⟨v1, hv1⟩
          step as ⟨r, hr⟩
          rw [hr, hv, hv1]
          by_cases he : ExtModel.nfkc seg.toList = ExtModel.nfkc fm.«name».toList
          · simp only [he, decide_true, BEq.rfl]
          · simp only [he, decide_false, Bool.false_eq, beq_eq_false_iff_ne, ne_eq,
              not_false_eq_true]
      intro nmatch hnmatch
      split
      · rename_i hmt
        rw [hmt, eq_comm] at hnmatch
        rw [hnmatch]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases res with
        | Dynamic => exact (WP.spec_ok _).2 rfl
        | Files files =>
          dsimp only
          step with validate_loop0_spec uri files 0#usize (Nat.zero_le _) as ⟨listed, hlisted⟩
          rw [List.drop_zero] at hlisted
          split
          · rename_i hlt
            rw [hlt, eq_comm] at hlisted
            rw [hlisted]
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            step as ⟨seen, hseen⟩
            step with validate_loop1_spec uri files seen 0#usize (Nat.zero_le _) hu
              (hfiles files rfl) (by
                intro k
                rw [hseen, show (0#usize).val = 0 from rfl, List.take_zero]
                simp only [List.not_mem_nil, false_and, exists_false]) as ⟨r, hr⟩
            rw [hr, List.take_zero, List.drop_zero]
            cases firstFileFault uri [] files.val <;> rfl
          · rename_i hlf
            have : ((files.val.any fun f => f.uri == uri)) = false := by
              rw [← hlisted]
              exact Bool.eq_false_iff.2 hlf
            rw [this]
            step as ⟨s1, hs1⟩
            subst hs1
            rfl
      · rename_i hmf
        have : nameMatchesSegment enc.val fm.«name» = false := by
          rw [← hnmatch]
          exact Bool.eq_false_iff.2 hmf
        rw [this]
        step as ⟨s1, hs1⟩
        step as ⟨s2, hs2⟩
        subst hs1 hs2
        rfl
    · rename_i hbf
      have hb' : isSkillName fm.«name» = false := by
        rw [← hb]
        exact Bool.eq_false_iff.2 hbf
      rw [hb']
      step with Str.Insts.AllocBorrowToOwnedString.to_owned_spec nm fm.«name» hnm as ⟨s1, hs1⟩
      subst hs1
      rfl

/-- K13, corollary: `validate` returns `Ok(())` exactly for a valid skill (`ValidSkill`): the URI
has no query or fragment and ends in `<segment>/SKILL.md`, with the segment non-empty, without
`/`, and at the start of the URI or after a `/` (so `billing/SKILL.md` is accepted); the decoded
segment matches the name in NFKC form; the name is a valid skill name; and, unless `resources`
is `"dynamic"`, the manifest lists the skill's own `SKILL.md`, every file lies within the skill's
directory and has a well-formed digest, and no two files have the same key (`ValidManifest`).
Premises as K13. Not covered: (H). -/
theorem validate_eq_ok_iff (self : Skill) (h_sizes : SkillFits self) (h_nfkc : NfkcFits self) :
    validate self ⦃ (result : core.result.Result Unit SkillValidationError) =>
      (result = .Ok () ↔ ValidSkill self) ⦄ :=
  WP.spec_mono (validate_spec self h_sizes h_nfkc) fun r hr => by
    rw [hr]; exact validateResult_eq_ok_iff self

end rmcp.model.skill.Skill

/-! ## K16: `validate_skills` -/

namespace rmcp.model.skill

open ExtModel Proofs.External.Byte Proofs.External.Utf8 Proofs.External.Skill Proofs.Model.Skill

/-- **Spec theorem for `rmcp::model::skill::validate_skills`** (K16)

Returns `validateSkillsResult skills` (`Defs.Skill`): walking the skills in order, the `validate`
error (K13) of the first skill that does not validate, or `DuplicateSkill(uri)` for the first skill
whose percent-normalised URI (`skillKey`) an earlier skill has, whichever comes first; `Ok(())` if
neither occurs (upstream lines 424–433; patched lines 488–497, hunk H8). For a skill that both fails
`validate` and repeats an earlier skill's key, the `validate` error is returned: `skill.validate()?`
comes before the duplicate check (upstream line 427 before 428, patched line 491 before 492).
Premises, for every skill: (V), (N), (U). These premises are sufficient, not exact: Rust only
reaches the skills up to the first fault (and their files up to the first faulty file), and every
value held in memory meets them. Not covered: (H), for each skill validated. -/
@[step]
theorem validate_skills_spec (skills : Slice Skill)
    (h_sizes : ∀ s ∈ skills.val, SkillFits s ∧ UriFits s.uri)
    (h_nfkc : ∀ s ∈ skills.val, NfkcFits s) :
    validate_skills skills ⦃ (result : core.result.Result Unit SkillValidationError) =>
      result = validateSkillsResult skills.val ⦄ := by
  unfold validate_skills validate_skills_loop validateSkillsResult
  step as ⟨seen0, hseen0⟩
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok]
  apply loop.spec_decr_nat
    (fun st : core.slice.iter.Iter Skill × std.collections.hash.set.HashSet String
      std.hash.random.RandomState alloc.alloc.Global => skills.length - st.1.i)
    (fun st => st.1.slice = skills ∧ st.1.i ≤ skills.length ∧
      (∀ k, k ∈ st.2.elements ↔ ∃ t ∈ skills.val.take st.1.i, skillKey t = utf8 k) ∧
      firstSkillFault (skills.val.take st.1.i) (skills.val.drop st.1.i) =
        firstSkillFault [] skills.val)
  · rintro ⟨⟨sl, i⟩, seen⟩ ⟨hs, hi, hseen, heq⟩
    dsimp only at hs hi hseen heq ⊢
    subst hs
    unfold validate_skills_loop.body
    have : Inhabited Skill := ⟨⟨"", ⟨"", "", ⟨[]⟩⟩, .Dynamic, none⟩⟩
    step as ⟨o, iter1, hr⟩
    rcases hr with ⟨hlt, ho, hit⟩ | ⟨hge, ho, hit⟩
    · have hlt : i < sl.val.length := hlt
      rw [getElem!_pos sl.val i hlt] at ho
      subst ho hit
      have hmem : sl.val[i] ∈ sl.val := List.getElem_mem _
      obtain ⟨hfit, hufit⟩ := h_sizes _ hmem
      rw [List.drop_eq_getElem_cons hlt, firstSkillFault] at heq
      step with Skill.validate_spec _ hfit (h_nfkc _ hmem) as ⟨r, hr⟩
      subst hr
      cases hv : validateResult sl.val[i] with
      | Err e =>
        rw [hv] at heq
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, bind_ok, WP.spec_ok]
        rw [← heq]
      | Ok u =>
        rw [hv] at heq
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        obtain ⟨hu, -, -⟩ := hfit
        step with alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec _ hu as ⟨su, hsu⟩
        step with normalize_percent_encoding_spec su (by rw [hsu, length_utf8]; exact hufit)
          as ⟨c, hc⟩
        rw [hsu] at hc
        obtain ⟨t, ht⟩ := exists_eq_utf8_of_ascii
          (val_lt_128_of_mem_normalizePercent (utf8 (sl.val[i]).uri))
        step with alloc.borrow.Cow.into_owned_str_spec c t (by rw [hc, ht]) as ⟨s1, hs1⟩
        subst hs1
        have hkey : skillKey sl.val[i] = utf8 s1 := ht
        have hany : ((sl.val.take i).any fun t' => skillKey t' == skillKey sl.val[i]) =
            decide (s1 ∈ seen.elements) := by
          rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff, hseen s1, hkey]
          simp only [beq_iff_eq]
        rw [hany] at heq
        step with std.collections.hash.set.HashSet.insert_spec alloc.string.String.Insts.CoreCmpEq
            alloc.string.String.Insts.CoreHashHash
            std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher seen s1
            string_eq_inst_spec as ⟨b, seen1, hp⟩
        rcases hp with ⟨hmem, hp⟩ | ⟨hnmem, hp⟩
        · obtain ⟨rfl, rfl⟩ := hp
          rw [ite_eq_right Bool.false_ne_true]
          step as ⟨s2, hs2⟩
          subst hs2
          rw [← heq]
          simp only [hmem, decide_true, ↓reduceIte]
        · obtain ⟨rfl, rfl⟩ := hp
          rw [ite_eq_left rfl]
          simp only [hnmem, decide_false, Bool.false_eq_true, ↓reduceIte] at heq
          rw [WP.spec_ok]
          refine ⟨rfl, show i + 1 ≤ sl.val.length by omega, ?_, ?_,
            show sl.val.length - (i + 1) < sl.val.length - i by omega⟩
          · intro k
            rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some]
            simp only [List.mem_append, List.mem_singleton, hseen k]
            constructor
            · rintro (⟨g, hg, hgk⟩ | rfl)
              · exact ⟨g, Or.inl hg, hgk⟩
              · exact ⟨_, Or.inr rfl, hkey⟩
            · rintro ⟨g, hg, hgk⟩
              rcases hg with hg | rfl
              · exact Or.inl ⟨g, hg, hgk⟩
              · right
                rw [hkey] at hgk
                exact (utf8_injective hgk).symm
          · rw [← heq, List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some]
    · subst ho hit
      rw [WP.spec_ok]
      have : i = sl.val.length := Nat.le_antisymm hi hge
      rw [← heq, this, List.drop_length, firstSkillFault]
  · refine ⟨rfl, Nat.zero_le _, ?_, ?_⟩
    · intro k; rw [hseen0]; simp only [List.not_mem_nil, List.take_zero, false_and, exists_false]
    · simp only [List.take_zero, List.drop_zero]

/-- K16, corollary: `validate_skills` returns `Ok(())` exactly when every skill is valid
(`ValidSkill`, as K13's corollary) and the percent-normalised URIs are pairwise distinct
(`ValidSkills`). Premises as K16. Not covered: (H), for each skill validated. -/
theorem validate_skills_eq_ok_iff (skills : Slice Skill)
    (h_sizes : ∀ s ∈ skills.val, SkillFits s ∧ UriFits s.uri)
    (h_nfkc : ∀ s ∈ skills.val, NfkcFits s) :
    validate_skills skills ⦃ (result : core.result.Result Unit SkillValidationError) =>
      (result = .Ok () ↔ ValidSkills skills.val) ⦄ :=
  WP.spec_mono (validate_skills_spec skills h_sizes h_nfkc) fun r hr => by
    rw [hr]; exact validateSkillsResult_eq_ok_iff skills.val

/-! ## Compositions with K11, K14 and K16 -/

/-- **`validate` ignores `_meta`** (K11 then K13): `validate` of the skill that `with_meta`
returns gives `validateResult self`, what `validate self` gives (K13); `validateResult` reads
only the URI, the frontmatter name and the resources (`Defs.Skill.validateResult_with_meta`).
Premises: (V), (N) for `self` (`with_meta` keeps the fields they constrain). Not covered: (H). -/
theorem Skill.validate_with_meta (self : Skill) (m : rmcp.model.meta.MetaObject)
    (h_sizes : SkillFits self) (h_nfkc : NfkcFits self) :
    Skill.with_meta self m ⦃ (s : Skill) =>
      Skill.validate s ⦃ (result : core.result.Result Unit SkillValidationError) =>
        result = validateResult self ⦄ ⦄ := by
  step with Skill.with_meta_spec self m as ⟨s, h1, h2, h3, h4⟩
  have hs : s = { self with «meta» := some m } := by
    obtain ⟨u, f, r, mm⟩ := s
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    rfl
  subst hs
  exact WP.spec_mono (Skill.validate_spec _ h_sizes h_nfkc) fun r hr => by
    rw [hr, validateResult_with_meta]

/-- **`skill_name_from_uri` returns `None` exactly when `validate` reports `UriNotSkillMd`**
(K14, K13): on the bytes of the skill's URI. Premises as K13. Not covered: (H). -/
theorem Skill.skill_name_from_uri_eq_none_iff_validate_eq_err (self : Skill) (uri : Str)
    (h_uri : uri.val = utf8Bytes self.uri) (h_sizes : SkillFits self) (h_nfkc : NfkcFits self) :
    skill_name_from_uri uri ⦃ (segment : Option Str) =>
      Skill.validate self ⦃ (result : core.result.Result Unit SkillValidationError) =>
        (segment = none ↔ result = .Err (.UriNotSkillMd self.uri)) ⦄ ⦄ := by
  step as ⟨segment, hseg⟩
  rw [h_uri] at hseg
  exact WP.spec_mono (Skill.validate_spec self h_sizes h_nfkc) fun r hr => by
    rw [hr, validateResult_eq_err_uriNotSkillMd_iff, ← hseg, Option.map_eq_none_iff]
    simp only [and_true]

/-- **A skill that validates has a name segment that matches its name** (K14, K13): when
`validate` returns `Ok(())`, `skill_name_from_uri` on the bytes of the skill's URI returns
`Some(segment)` with a segment that matches the frontmatter name (`nameMatchesSegment`).
Premises as K13. Not covered: (H). -/
theorem Skill.exists_skill_name_from_uri_eq_some_of_validate_eq_ok (self : Skill) (uri : Str)
    (h_uri : uri.val = utf8Bytes self.uri) (h_sizes : SkillFits self) (h_nfkc : NfkcFits self) :
    skill_name_from_uri uri ⦃ (segment : Option Str) =>
      Skill.validate self ⦃ (result : core.result.Result Unit SkillValidationError) =>
        (result = .Ok () →
          ∃ seg, segment = some seg ∧ nameMatchesSegment seg.val self.frontmatter.«name» = true) ⦄
      ⦄ := by
  step as ⟨segment, hseg⟩
  rw [h_uri] at hseg
  exact WP.spec_mono (Skill.validate_spec self h_sizes h_nfkc) fun r hr hok => by
    rw [hr, validateResult_eq_ok_iff] at hok
    obtain ⟨⟨encoded, henc, hmatch⟩, -, -⟩ := hok
    rw [henc, Option.map_eq_some_iff] at hseg
    obtain ⟨seg, hseg1, hseg2⟩ := hseg
    exact ⟨seg, hseg1, by rw [hseg2]; exact hmatch⟩

/-- **One skill: `validate_skills` is `validate`** (K16, K13): for a listing of exactly one skill
`s`, `validate_skills` returns what `validate s` returns (no duplicate is possible). Premises: (V),
(N), (U) for `s`. They are sufficient, not exact: (U) is used only when `validate` succeeds, the
file premises of (V) only up to the first faulty file, and every value held in memory meets them.
Not covered: (H). -/
theorem validate_skills_singleton (skills : Slice Skill) (s : Skill) (h_one : skills.val = [s])
    (h_sizes : SkillFits s) (h_uri_fits : UriFits s.uri) (h_nfkc : NfkcFits s) :
    validate_skills skills ⦃ (result : core.result.Result Unit SkillValidationError) =>
      Skill.validate s ⦃ (result' : core.result.Result Unit SkillValidationError) =>
        result = result' ⦄ ⦄ := by
  step with validate_skills_spec skills
    (by
      rw [h_one]; intro t ht; rw [List.mem_singleton] at ht; subst ht
      exact ⟨h_sizes, h_uri_fits⟩)
    (by rw [h_one]; intro t ht; rw [List.mem_singleton] at ht; subst ht; exact h_nfkc) as ⟨r, hr⟩
  exact WP.spec_mono (Skill.validate_spec s h_sizes h_nfkc) fun r' hr' => by
    rw [hr, hr', h_one, validateSkillsResult_singleton]

end rmcp.model.skill
