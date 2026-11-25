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
public import Proofs.External.String
public import Proofs.External.WP
public import Proofs.Model.Skill.Basic
public import Proofs.Model.Skill.Common

@[expose] public section

/-!
# Spec theorems for `verify`, `with_field`, `skill_name_from_uri` and `is_sha256_digest`

The public `skill.rs` targets K06 (`SkillResource::verify`), K09 (`SkillFrontmatter::with_field`
and its corollary), K14 (`skill_name_from_uri`) and K15 (`is_sha256_digest`), and the
compositions `SkillResource.verify_from_bytes_self`, `SkillResource.verify_from_bytes` (K05 then
K06), `SkillResource.verify_eq_ok_iff` (K06 cor.) and `is_sha256_digest_sha256_digest` (K07 then
K15). Statements as signed off on 2026-11-25 (restated in
`formal/specs/Specs/Model/Skill.lean`). K05 and K07 are used through `Proofs.Model.Skill.Basic`.

* `verify` compares the size first, then the digest computed by `sha256_digest` (K07).
* `with_field` inserts into the `serde_json::Map` model (`ExtModel.mapInsert`); the lookups hold
  for every entry list, and `KeysSorted` is the model's `SortedByKey` (`bytesLt` is the list
  order of `U8`).
* `skill_name_from_uri` strips `SKILL.md` and then `/`, which is stripping `/SKILL.md`, and takes
  the part after the last `/`, which is the last item of `List.splitOn`.
* `is_sha256_digest` strips `sha256:` and checks the length and the bytes of the rest.
* The compositions use that `sha256Digest` is injective on SHA-256 values (two lowercase
  hexadecimal digits per byte) and that its bytes pass `isSha256Digest`.

Source: "crates/rmcp/src/model/skill.rs" at upstream `7caec76`: `verify` lines 94–112,
`with_field` lines 170–177, `skill_name_from_uri` lines 326–333, `is_sha256_digest` lines
417–421; in the patched copy (translation patches 01–04) lines 94–112, 172–179, 345–352 and
481–485.
-/

open Aeneas Aeneas.Std Result
open Defs (utf8Bytes)
open Defs.Skill

/-! ## Lemmas about the definitions and the models -/

namespace Proofs.Model.Skill

open ExtModel Proofs.External.Utf8 Proofs.External.Skill

/-! ### URIs (K14) -/

/-- `a :: S` is a suffix of `l` iff `S` is, and `a` ends what precedes it. -/
theorem cons_suffix_iff {α : Type} (a : α) (S l : List α) :
    (a :: S) <:+ l ↔ S <:+ l ∧ [a] <:+ l.take (l.length - S.length) := by
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨(List.suffix_cons a S).trans (List.suffix_append t _), ?_⟩
    rw [List.append_cons, List.take_left' (by simp only [List.length_append]; omega)]
    exact List.suffix_append t [a]
  · rintro ⟨⟨t, rfl⟩, ⟨q, hq⟩⟩
    rw [List.length_append, Nat.add_sub_cancel, List.take_left' rfl] at hq
    subst hq
    exact ⟨q, by rw [List.append_assoc, List.singleton_append]⟩

/-! ### Maps (K09) -/

/-- `bytesLt` is the lexicographic order `<` of byte lists. -/
theorem bytesLt_eq_true_iff_lt : ∀ a b : List U8, bytesLt a b = true ↔ a < b
  | [], [] => by simp only [bytesLt, Bool.false_eq_true, lt_self_iff_false]
  | [], _ :: _ => by simp only [bytesLt, List.nil_lt_cons]
  | _ :: _, [] => by simp only [bytesLt, Bool.false_eq_true, List.not_lt_nil]
  | x :: xs, y :: ys => by
    rw [List.cons_lt_cons_iff, ← bytesLt_eq_true_iff_lt xs ys, bytesLt]
    have heq : x = y ↔ x.val = y.val := ⟨fun h => h ▸ rfl, UScalar.eq_of_val_eq⟩
    rw [heq]
    by_cases h1 : x.val < y.val
    · rw [ite_eq_left h1]
      exact iff_of_true rfl (Or.inl h1)
    · rw [ite_eq_right h1]
      by_cases h2 : x.val = y.val
      · rw [ite_eq_left h2]
        exact ⟨fun h => Or.inr ⟨h2, h⟩, fun h => h.elim (fun h => absurd h h1) And.right⟩
      · rw [ite_eq_right h2]
        exact iff_of_false Bool.false_ne_true fun h => h.elim h1 fun h => h2 h.1

/-- `KeysSorted` is the model's `SortedByKey` of the entries. -/
theorem keysSorted_iff_sortedByKey (m : serde_json.map.Map String serde_json.value.Value) :
    KeysSorted m ↔ SortedByKey m.entries := by
  unfold KeysSorted SortedByKey
  simp only [bytesLt_eq_true_iff_lt, utf8Bytes_eq_utf8]

/-- After `mapInsert k v`, the first entry of `k` has value `v`, and the first entry of every
other key is unchanged; for any entry list. -/
theorem map_snd_find?_mapInsert {V : Type} (k : String) (v : V) (k' : String) :
    ∀ l : List (String × V),
      ((mapInsert k v l).2.find? (fun e => e.1 == k')).map Prod.snd =
        if k' = k then some v else (l.find? (fun e => e.1 == k')).map Prod.snd
  | [] => by
    by_cases h : k' = k
    · subst h; simp only [mapInsert, BEq.rfl, List.find?_cons_of_pos, Option.map_some, ↓reduceIte]
    · simp only [mapInsert, beq_iff_eq, Ne.symm h, not_false_eq_true, List.find?_cons_of_neg,
        List.find?_nil, Option.map_none, h, ↓reduceIte]
  | (k0, v0) :: rest => by
    have ih := map_snd_find?_mapInsert k v k' rest
    by_cases h1 : k0 = k
    · subst h1
      rw [mapInsert, ite_eq_left rfl]
      by_cases hk : k' = k0
      · subst hk; simp only [BEq.rfl, List.find?_cons_of_pos, Option.map_some, ↓reduceIte]
      · simp only [beq_iff_eq, Ne.symm hk, not_false_eq_true, List.find?_cons_of_neg, hk,
          ↓reduceIte]
    · rw [mapInsert, ite_eq_right h1]
      by_cases h3 : bytesLt (utf8 k) (utf8 k0) = true
      · rw [ite_eq_left h3]
        by_cases hk : k' = k
        · subst hk; simp only [BEq.rfl, List.find?_cons_of_pos, Option.map_some, ↓reduceIte]
        · simp only [beq_iff_eq, Ne.symm hk, not_false_eq_true, List.find?_cons_of_neg, hk,
            ↓reduceIte]
      · rw [ite_eq_right h3]
        dsimp only
        by_cases h4 : k0 = k'
        · subst h4; simp only [BEq.rfl, List.find?_cons_of_pos, Option.map_some, h1, ↓reduceIte]
        · simp only [beq_iff_eq, h4, not_false_eq_true, List.find?_cons_of_neg, ih]

/-! ### Digests (K15 and the compositions) -/

open rmcp.model.skill in
/-- The digit closure of `is_sha256_digest` computes `isLowerHexDigit` and keeps its state. -/
theorem is_sha256_digest_closure_closure_call_mut (x : U8) :
    is_sha256_digest.closure.closure.Insts.CoreOpsFunctionFnMutTupleU8Bool.call_mut () x =
      ok (isLowerHexDigit x, ()) := by
  unfold is_sha256_digest.closure.closure.Insts.CoreOpsFunctionFnMutTupleU8Bool.call_mut
  rw [isLowerHexDigit, Defs.IntParse.isAsciiDigit]
  have h48 : (48#u8 ≤ x) ↔ 48 ≤ x.val := Iff.rfl
  have h57 : (x ≤ 57#u8) ↔ x.val ≤ 57 := Iff.rfl
  have h97 : (97#u8 ≤ x) ↔ 97 ≤ x.val := Iff.rfl
  have h102 : (x ≤ 102#u8) ↔ x.val ≤ 102 := Iff.rfl
  -- the test `97 ≤ x ≤ 102`, shared by both branches of the first test
  have hhex : ¬ (48 ≤ x.val ∧ x.val ≤ 57) →
      (if 97#u8 ≤ x then (if x ≤ 102#u8 then ok (true, ()) else ok (false, ()))
        else ok (false, ()) : Result (Bool × is_sha256_digest.closure.closure)) =
      ok ((decide (48 ≤ x.val ∧ x.val ≤ 57) || (decide (97 ≤ x.val) && decide (x.val ≤ 102))),
        ()) := by
    intro hd
    rw [decide_eq_false hd, Bool.false_or]
    by_cases h3 : 97 ≤ x.val
    · rw [ite_eq_left (h97.2 h3), decide_eq_true h3, Bool.true_and]
      by_cases h4 : x.val ≤ 102
      · rw [ite_eq_left (h102.2 h4), decide_eq_true h4]
      · rw [ite_eq_right (mt h102.1 h4), decide_eq_false h4]
    · rw [ite_eq_right (mt h97.1 h3), decide_eq_false h3, Bool.false_and]
  by_cases h1 : 48 ≤ x.val
  · rw [ite_eq_left (h48.2 h1)]
    by_cases h2 : x.val ≤ 57
    · rw [ite_eq_left (h57.2 h2), decide_eq_true ⟨h1, h2⟩, Bool.true_or]
    · rw [ite_eq_right (mt h57.1 h2)]
      exact hhex fun h => h2 h.2
  · rw [ite_eq_right (mt h48.1 h1)]
    exact hhex fun h => h1 h.1

/-- `lowerHexDigit` is injective on `0`–`15`. -/
theorem lowerHexDigit_inj {m n : Nat} (hm : m < 16) (hn : n < 16)
    (h : lowerHexDigit m = lowerHexDigit n) : m = n := by
  have key : ∀ m, m < 16 → ∀ n, n < 16 → lowerHexDigit m = lowerHexDigit n → m = n := by
    decide
  exact key m hm n hn h

/-- The hexadecimal digits of a byte list determine it. -/
theorem eq_of_flatMap_lowerHexDigit_eq :
    ∀ xs ys : List U8,
      (xs.flatMap fun b => [lowerHexDigit (b.val / 16), lowerHexDigit (b.val % 16)]) =
        (ys.flatMap fun b => [lowerHexDigit (b.val / 16), lowerHexDigit (b.val % 16)]) →
      xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: xs, y :: ys, h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hx := x.hBounds
    have hy := y.hBounds
    have e1 := lowerHexDigit_inj (by scalar_tac) (by scalar_tac) h1
    have e2 := lowerHexDigit_inj (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h2
    have hxy : x = y := by
      apply UScalar.eq_of_val_eq
      have := Nat.div_add_mod x.val 16
      have := Nat.div_add_mod y.val 16
      omega
    rw [hxy, eq_of_flatMap_lowerHexDigit_eq xs ys h3]

/-- `sha256Digest` determines the SHA-256 value: equal formatted digests have equal SHA-256
values (the converse holds by congruence). -/
theorem sha256_eq_of_sha256Digest_eq {a b : List U8} (h : sha256Digest a = sha256Digest b) :
    ExtModel.sha256 a = ExtModel.sha256 b := by
  unfold sha256Digest lowerHex at h
  have h' := congrArg utf8 h
  rw [utf8_append, utf8_append] at h'
  have h'' := utf8_injective (List.append_cancel_left h')
  have := congrArg String.toList h''
  rw [String.toList_ofList, String.toList_ofList] at this
  exact Aeneas.Std.Array.ext _ _ (eq_of_flatMap_lowerHexDigit_eq _ _ this)

end Proofs.Model.Skill

/-! ## K06: `SkillResource::verify` -/

namespace rmcp.model.skill.SkillResource

open Proofs.Model.Skill

/-- **Spec theorem for `rmcp::model::skill::SkillResource::verify`** (K06)

Checks the size first, then the digest (upstream lines 94–112; patched lines 94–112, hunk H9
swaps the branches of the digest test without changing the result):
* `Ok(())` exactly when `bytes` has the promised length and its digest `sha256Digest bytes` is
  the promised one;
* `Err(Size { uri, expected: self.size, actual: bytes.len() })` when the length differs
  (upstream lines 95–102), whatever the digest;
* `Err(Digest { uri, expected: self.digest, actual: sha256Digest bytes })` when the length is
  right and the digest differs (upstream lines 103–110).
No premise. Not covered: (S). -/
@[step]
theorem verify_spec (self : SkillResource) (bytes : Slice U8) :
    verify self bytes ⦃ (result : core.result.Result Unit SkillIntegrityError) =>
      match result with
      | .Ok () =>
        bytes.val.length = self.size.val ∧ sha256Digest bytes.val = self.digest
      | .Err (.Size uri expected actual) =>
        bytes.val.length ≠ self.size.val ∧
          uri = self.uri ∧ expected = self.size ∧ actual.val = bytes.val.length
      | .Err (.Digest uri expected actual) =>
        bytes.val.length = self.size.val ∧ sha256Digest bytes.val ≠ self.digest ∧
          uri = self.uri ∧ expected = self.digest ∧ actual = sha256Digest bytes.val ⦄ := by
  unfold verify
  step as ⟨size, hsize⟩
  have hs : size.val = bytes.val.length := by
    rw [hsize, Proofs.RequestStateWire.val_cast_u64, Slice.len_val]
  by_cases hne : size = self.size
  · have hl : bytes.val.length = self.size.val := by rw [← hs, hne]
    simp only [hne, bne_self_eq_false, Bool.false_eq_true, ite_false]
    step as ⟨digest, hd⟩
    step as ⟨b, hb⟩
    subst hd hb
    by_cases hdg : sha256Digest bytes.val = self.digest
    · simp only [hdg, decide_true, ite_true, WP.spec_ok]
      exact ⟨hl, trivial⟩
    · simp only [hdg, decide_false, Bool.false_eq_true, ite_false]
      step as ⟨s1, hs1⟩
      step as ⟨s2, hs2⟩
      exact ⟨hl, hdg, hs1, hs2⟩
  · have hl : bytes.val.length ≠ self.size.val := by
      rw [← hs]; intro h; exact hne (UScalar.eq_of_val_eq h)
    have hb : (size != self.size) = true := bne_iff_ne.2 hne
    simp only [hb, ite_true]
    step as ⟨s1, hs1⟩
    exact ⟨hl, hs1, hs⟩

end rmcp.model.skill.SkillResource

/-! ## K09: `SkillFrontmatter::with_field` -/

namespace rmcp.model.skill.SkillFrontmatter

open Proofs.External.Skill Proofs.Model.Skill

/-- **Spec theorem for `rmcp::model::skill::SkillFrontmatter::with_field`** (K09)

In the Lean model a `serde_json::Map` is its list of entries; every map Rust builds is sorted
(`KeysSorted`; in the translated configuration, see (P)). `with_field` sets the extra field `k =
key.into()` to `v = value.into()`, replacing an earlier value of `k`; every other key keeps its
value, and the name and description are unchanged (`self.extra.insert(key.into(), value.into())`,
upstream lines 170–177, patched lines 172–179; `serde_json::Map` is a `BTreeMap` in the translated
configuration). The lookups hold for any entry list of `self.extra` (the insertion is described at
K09 cor.). If `self.extra` is sorted (as every map built by K08 and K09 is), so is the result, and
then the lookups determine it. Premise: caller code. Not covered: (I), (P). -/
@[step]
theorem with_field_spec {KeyLike ValueLike : Type} (keyInto : core.convert.Into KeyLike String)
    (valueInto : core.convert.Into ValueLike serde_json.value.Value) (self : SkillFrontmatter)
    (key : KeyLike) (value : ValueLike) (k : String) (v : serde_json.value.Value)
    (h_key_into : keyInto.into key = ok k) (h_value_into : valueInto.into value = ok v) :
    with_field keyInto valueInto self key value ⦃ (result : SkillFrontmatter) =>
      result.«name» = self.«name» ∧
      result.description = self.description ∧
      (KeysSorted self.extra → KeysSorted result.extra) ∧
      ∀ k', mapLookup result.extra k' = if k' = k then some v else mapLookup self.extra k' ⦄ := by
  simp only [with_field, h_key_into, h_value_into, serde_json.map.MapStringValue.insert, bind_ok]
  refine (WP.spec_ok _).2 ⟨rfl, rfl, fun h => ?_, fun k' => map_snd_find?_mapInsert k v k' _⟩
  rw [keysSorted_iff_sortedByKey] at h ⊢
  exact sortedByKey_mapInsert k v _ h

/-- K09, corollary: the entries of `extra` are `ExtModel.mapInsert k v self.extra.entries`, the
trusted model of `BTreeMap::insert`, for any entry list. `ExtModel.mapInsert k v` walks the
entries while their key differs from `k` and is not greater than it (in the byte order of
`KeysSorted`); at the entry where it stops it replaces the value if that key is `k`, and otherwise
inserts `(k, v)` before that entry (at the end if it reaches the end). So `(k, v)` precedes every
other entry with key `k`, and every other key keeps its first entry. On a sorted list this is the
`BTreeMap` insertion. Premise: caller code. Not covered: (I), (P). -/
theorem with_field_extra_entries_eq_mapInsert {KeyLike ValueLike : Type}
    (keyInto : core.convert.Into KeyLike String)
    (valueInto : core.convert.Into ValueLike serde_json.value.Value) (self : SkillFrontmatter)
    (key : KeyLike) (value : ValueLike) (k : String) (v : serde_json.value.Value)
    (h_key_into : keyInto.into key = ok k) (h_value_into : valueInto.into value = ok v) :
    with_field keyInto valueInto self key value ⦃ (result : SkillFrontmatter) =>
      result.«name» = self.«name» ∧
      result.description = self.description ∧
      result.extra.entries = (ExtModel.mapInsert k v self.extra.entries).2 ⦄ := by
  simp only [with_field, h_key_into, h_value_into, serde_json.map.MapStringValue.insert, bind_ok]
  exact (WP.spec_ok _).2 ⟨rfl, rfl, rfl⟩

end rmcp.model.skill.SkillFrontmatter

/-! ## K14, K15: `skill_name_from_uri`, `is_sha256_digest` -/

namespace rmcp.model.skill

open ExtModel Proofs.External.Utf8 Proofs.Model.Skill

/-- **Spec theorem for `rmcp::model::skill::skill_name_from_uri`** (K14)

The bytes of the returned slice are `skillNameOfUri uri`: `None` for a URI with `?` or `#`;
otherwise, for a URI ending in `/SKILL.md`, the non-empty segment before it, still
percent-encoded; `None` in every other case (upstream lines 326–333; patched lines 345–352, hunk
H3). Defined on every `Str`; no premise. -/
@[step]
theorem skill_name_from_uri_spec (uri : Str) :
    skill_name_from_uri uri ⦃ (result : Option Str) =>
      result.map (·.val) = skillNameOfUri uri.val ⦄ := by
  unfold skill_name_from_uri
  step as ⟨o, ho⟩
  have hany : uri.val.any isQueryOrFragmentStart = o.isSome := by
    rw [show isQueryOrFragmentStart = _ from funext isQueryOrFragmentStart_eq_decide,
      ← List.findIdx?_isSome, ← ho, Option.isSome_map]
  have hmd : SKILL_MD.val = skillMd := by
    rw [SKILL_MD]
    exact toStr_val _ _
  have hsl : (toStr "/").val = [byte 47] := by
    rw [toStr_val]
    decide +kernel
  unfold skillNameOfUri stripSuffix
  rw [hany]
  by_cases hs : o.isSome
  · simp only [hs, ite_true, WP.spec_ok, Option.map_none]
  simp only [hs, Bool.false_eq_true, ite_false]
  step as ⟨o1, ho1⟩
  rw [hmd] at ho1
  step as ⟨cf, hcf⟩
  subst hcf
  simp only [List.isSuffixOf_iff_suffix, asciiByte_slash, cons_suffix_iff (byte 47) skillMd uri.val]
  cases o1 with
  | none =>
    have hns : ¬ skillMd <:+ uri.val := by
      intro h
      rw [ite_eq_left h] at ho1
      cases ho1
    simp only [hns, false_and, ite_false]
    step as ⟨r, hr⟩
    rw [hr, Option.map_none]
  | some val =>
    have hS : skillMd <:+ uri.val := by
      by_contra h
      rw [ite_eq_right h] at ho1
      cases ho1
    have hv : val.val = uri.val.take (uri.val.length - skillMd.length) := by
      rw [ite_eq_left hS] at ho1
      exact Option.some.inj ho1
    simp only [hS, true_and]
    step as ⟨o2, ho2⟩
    rw [hsl, hv] at ho2
    step as ⟨cf1, hcf1⟩
    subst hcf1
    cases o2 with
    | none =>
      have hns : ¬ [byte 47] <:+ uri.val.take (uri.val.length - skillMd.length) := by
        intro h
        rw [ite_eq_left h] at ho2
        cases ho2
      simp only [hns, ite_false]
      step as ⟨r, hr⟩
      rw [hr, Option.map_none]
    | some val1 =>
      have h1 : [byte 47] <:+ uri.val.take (uri.val.length - skillMd.length) := by
        by_contra h
        rw [ite_eq_right h] at ho2
        cases ho2
      have hv1 : val1.val = uri.val.take (uri.val.length - (byte 47 :: skillMd).length) := by
        rw [ite_eq_left h1, Option.map_some] at ho2
        rw [Option.some.inj ho2, List.take_take, List.length_take, List.length_cons]
        congr 1
        rw [List.length_cons, List.length_nil]
        omega
      simp only [h1, ite_true]
      step as ⟨nm, hnm⟩
      step as ⟨b1, hb1⟩
      step as ⟨r, hr⟩
      rw [hr]
      rw [hv1, drop_lastSegmentStart] at hnm
      unfold lastSegment
      rw [asciiByte_slash, ← hnm]
      cases b1 with
      | false =>
        rw [ite_eq_right fun h => Bool.false_ne_true (hb1.2 h)]
        rfl
      | true =>
        rw [ite_eq_left (hb1.1 rfl)]
        rfl

/-- **Spec theorem for `rmcp::model::skill::is_sha256_digest`** (K15)

`true` exactly when `digest` is `sha256:` followed by 64 lowercase hexadecimal digits
(`isSha256Digest`; upstream lines 417–421, patched lines 481–485, hunk H7). No premise. -/
@[step]
theorem is_sha256_digest_spec (digest : Str) :
    is_sha256_digest digest ⦃ (result : Bool) => result = isSha256Digest digest.val ⦄ := by
  unfold is_sha256_digest
  step as ⟨o, ho⟩
  rw [toStr_val] at ho
  unfold isSha256Digest stripPrefix
  rw [utf8Bytes_eq_utf8]
  by_cases h : utf8 "sha256:" <+: digest.val
  · rw [ite_eq_left h] at ho
    rw [ite_eq_left (List.isPrefixOf_iff_prefix.2 h)]
    cases o with
    | none => cases ho
    | some hex =>
      have hv : hex.val = (digest.val).drop (utf8 "sha256:").length := Option.some.inj ho
      simp only [core.option.Option.is_some_and_some]
      unfold is_sha256_digest.closure.Insts.CoreOpsFunctionFnOnceTupleShared0StrBool.call_once
      step as ⟨i, hi⟩
      rw [← hv]
      by_cases h64 : i = 64#usize
      · rw [ite_eq_left h64]
        have hl : hex.val.length = 64 := by rw [← hi, h64]; rfl
        step as ⟨b, hb1, hb2⟩
        have hall := core.str.iter.Bytes.Insts.CoreIterTraitsIteratorIteratorU8.all_spec
          is_sha256_digest.closure.closure.Insts.CoreOpsFunctionFnMutTupleU8Bool isLowerHexDigit b
          () is_sha256_digest_closure_closure_call_mut
        obtain ⟨⟨r1, r2⟩, hr, hr2⟩ := Proofs.External.WP.exists_ok_of_spec hall
        rw [hr, bind_ok]
        apply (WP.spec_ok _).2
        rw [hb1, hb2, List.drop_zero] at hr2
        refine hr2.trans ?_
        simp only [hl, BEq.rfl, Bool.true_and]
      · rw [ite_eq_right h64]
        simp only [WP.spec_ok]
        have : hex.val.length ≠ 64 := by
          intro h
          apply h64
          apply UScalar.eq_of_val_eq
          rw [hi, h]
          rfl
        simp only [Bool.false_eq, Bool.and_eq_false_imp, beq_iff_eq, this, List.all_eq_false,
          Bool.not_eq_true, IsEmpty.forall_iff]
  · rw [ite_eq_right h] at ho
    rw [ite_eq_right (mt List.isPrefixOf_iff_prefix.1 h)]
    cases o with
    | none => simp only [core.option.Option.is_some_and_none, WP.spec_ok]
    | some hex => cases ho

end rmcp.model.skill

/-! ## Composition theorems -/

namespace rmcp.model.skill

open Proofs.External.WP Proofs.Model.Skill

/-- **When `verify` succeeds** (K06 cor.): `Ok(())` exactly when `bytes` has the promised
length and its digest `sha256Digest bytes` is the promised one. No premise. Not covered: (S). -/
theorem SkillResource.verify_eq_ok_iff (self : SkillResource) (bytes : Slice U8) :
    SkillResource.verify self bytes ⦃ (result : core.result.Result Unit SkillIntegrityError) =>
      (result = .Ok () ↔
        bytes.val.length = self.size.val ∧ sha256Digest bytes.val = self.digest) ⦄ := by
  obtain ⟨r, hr, hp⟩ := exists_ok_of_spec (SkillResource.verify_spec self bytes)
  rw [hr, WP.spec_ok]
  rcases r with ⟨⟩ | (⟨uri, expected, actual⟩ | ⟨uri, expected, actual⟩)
  · exact ⟨fun _ => hp, fun _ => rfl⟩
  · exact ⟨fun h => (by cases h), fun h => absurd h.1 hp.1⟩
  · exact ⟨fun h => (by cases h), fun h => absurd h.2 hp.2.1⟩

/-- **An entry made from bytes verifies them** (K05 then K06): `from_bytes` succeeds and
`verify` of the entry on the same bytes returns `Ok(())`. Premise: caller code (the URI
conversion). Not covered: (I), (S). -/
theorem SkillResource.verify_from_bytes_self {UriLike : Type}
    (uriInto : core.convert.Into UriLike String) (uri : UriLike) (bytes : Slice U8) (u : String)
    (h_uri_into : uriInto.into uri = ok u) :
    SkillResource.from_bytes uriInto uri bytes ⦃ (entry : SkillResource) =>
      SkillResource.verify entry bytes ⦃ (result : core.result.Result Unit SkillIntegrityError) =>
        result = .Ok () ⦄ ⦄ := by
  obtain ⟨e, he, -, hdg, hsz⟩ :=
    exists_ok_of_spec (SkillResource.from_bytes_spec uriInto uri bytes u h_uri_into)
  rw [he, WP.spec_ok]
  obtain ⟨r, hr, hp⟩ := exists_ok_of_spec (SkillResource.verify_eq_ok_iff e bytes)
  rw [hr, WP.spec_ok]
  exact hp.2 ⟨hsz.symm, hdg.symm⟩

/-- **Verifying other bytes against an entry made from `bytes`** (K05 then K06): `Ok(())`
exactly when `other` has the same length and the same SHA-256 digest (`ExtModel.sha256`, unopened;
the formatting `sha256Digest` is injective on 32-byte digests); `Size` with the two lengths
exactly when the lengths differ; otherwise, when the SHA-256 digests differ, `Digest` with the
two formatted digests. Equal digests of different bytes are not excluded (no collision freedom
is assumed). Premise: caller code. Not covered: (I), (S). -/
theorem SkillResource.verify_from_bytes {UriLike : Type}
    (uriInto : core.convert.Into UriLike String) (uri : UriLike) (bytes other : Slice U8)
    (u : String) (h_uri_into : uriInto.into uri = ok u) :
    SkillResource.from_bytes uriInto uri bytes ⦃ (entry : SkillResource) =>
      SkillResource.verify entry other ⦃ (result : core.result.Result Unit SkillIntegrityError) =>
        match result with
        | .Ok () =>
          other.val.length = bytes.val.length ∧
            ExtModel.sha256 other.val = ExtModel.sha256 bytes.val
        | .Err (.Size uri' expected actual) =>
          other.val.length ≠ bytes.val.length ∧ uri' = u ∧
            expected.val = bytes.val.length ∧ actual.val = other.val.length
        | .Err (.Digest uri' expected actual) =>
          other.val.length = bytes.val.length ∧
            ExtModel.sha256 other.val ≠ ExtModel.sha256 bytes.val ∧ uri' = u ∧
            expected = sha256Digest bytes.val ∧ actual = sha256Digest other.val ⦄ ⦄ := by
  obtain ⟨e, he, hu, hdg, hsz⟩ :=
    exists_ok_of_spec (SkillResource.from_bytes_spec uriInto uri bytes u h_uri_into)
  rw [he, WP.spec_ok]
  obtain ⟨r, hr, hp⟩ := exists_ok_of_spec (SkillResource.verify_spec e other)
  rw [hr, WP.spec_ok]
  rcases r with ⟨⟩ | (⟨uri', expected, actual⟩ | ⟨uri', expected, actual⟩)
  · obtain ⟨h1, h2⟩ := hp
    rw [hdg] at h2
    exact ⟨h1.trans hsz, sha256_eq_of_sha256Digest_eq h2⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hp
    exact ⟨hsz ▸ h1, h2.trans hu, h3 ▸ hsz, h4⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hp
    rw [hdg] at h2 h4
    refine ⟨h1.trans hsz, fun h => h2 ?_, h3.trans hu, h4, h5⟩
    unfold sha256Digest
    rw [h]

/-- **A computed digest is well-formed** (K07 then K15): `is_sha256_digest` returns `true` on the
bytes of the string that `sha256_digest` returns, whatever the bytes hashed. No premise; nothing
is assumed about `ExtModel.sha256` beyond its type (32 bytes). Not covered: (S). -/
theorem is_sha256_digest_sha256_digest (bytes : Slice U8) :
    sha256_digest bytes ⦃ (d : String) =>
      ∀ s : Str, s.val = utf8Bytes d →
        is_sha256_digest s ⦃ (result : Bool) => result = true ⦄ ⦄ := by
  obtain ⟨d, hd, hdv⟩ := exists_ok_of_spec (sha256_digest_spec bytes)
  rw [hd, WP.spec_ok]
  intro s hs
  obtain ⟨b, hb, hbv⟩ := exists_ok_of_spec (is_sha256_digest_spec s)
  rw [hb, WP.spec_ok, hbv, hs, hdv]
  exact isSha256Digest_sha256Digest bytes.val

end rmcp.model.skill
