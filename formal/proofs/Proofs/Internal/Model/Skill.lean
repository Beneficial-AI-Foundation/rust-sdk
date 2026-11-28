/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Defs
public import Proofs.Model.Skill.Basic
public import Proofs.Model.Skill.Verify
public import Proofs.Model.Skill.Model
public import Proofs.Model.Skill.Validate

@[expose] public section

/-!
# Internal spec file for crates/rmcp/src/model/skill.rs (intermediate functions, model laws)

The public API of `skill.rs` that `formal/specs/` states is its **top-level** public functions
only: those that no other verified function calls (`formal/specs/Specs/Model/Skill.lean`). This
file holds the rest of the verified `skill.rs` statements, which the top-level statements are
built on:

* the **intermediate public functions**, `pub` in upstream rmcp but called by a top-level one:
  K04 `SkillResource::new` and K07 `sha256_digest` (called by K05 `from_bytes`; K07 also by K06
  `verify`), K12 `Skill::name`, K14 `skill_name_from_uri` and K15 `is_sha256_digest` (called by
  K13 `validate`), K13 `Skill::validate` (called by K16 `validate_skills`), with the corollary of
  K13;
* the **compositions** that involve an intermediate function;
* the **consequences of the model** (statements about the definitions of `Defs.Skill` only, with
  no Rust call), including the bridge lemma `NfkcFits.of_utf8ByteSize_le` for the premise (N).

The statements, their text, IDs, proofs and sign-off (spec owner, 2026-11-25) are unchanged; only
their place changed (human decision 2026-11-28: `formal/specs/` holds only top-level public
functions). The premise keys ((Z), (V), (N), (U), caller code) and the keys of the exceptions not
covered ((I), (S), (H)) are those defined in `formal/specs/Specs/Model/Skill.lean`, "Premises" and
"Not covered"; the translated configuration, line citations and linkage are as stated there.

| ID | Function | Theorem | Guarantee | Premises (caller must ensure) | Not covered (Rust may panic or behave otherwise; the model does not) |
|---|---|---|---|---|---|
| K04 | `SkillResource::new` | `SkillResource.new` | the entry with the converted URI and digest and the size | caller code | (I) |
| K07 | `sha256_digest` | `sha256_digest` | `sha256:` and the lowercase hex of the SHA-256 digest (`sha256Digest`) | none | (S) |
| K12 | `Skill::name` | `Skill.name` | the bytes of the frontmatter name | (Z) | none |
| K13 | `Skill::validate` | `Skill.validate` | `validateResult self`: the first failing check in the Rust order, with payloads | (V), (N) | (H) |
| K13 cor. | same | `Skill.validate_eq_ok_iff` | `Ok` iff `ValidSkill self` | (V), (N) | (H) |
| K14 | `skill_name_from_uri` | `skill_name_from_uri` | `skillNameOfUri uri` | none | none |
| K15 | `is_sha256_digest` | `is_sha256_digest` | `isSha256Digest digest` | none | none |
| K07+K15 | `sha256_digest`, then `is_sha256_digest` | `is_sha256_digest_sha256_digest` | a computed digest is well-formed | none | (S) |
| K11+K13 | `Skill::with_meta`, then `validate` | `Skill.validate_with_meta` | `validate` ignores `_meta`: the result is `validateResult self` | (V), (N) for `self` | (H) |
| K13+K14 | `skill_name_from_uri`, `validate` | `Skill.skill_name_from_uri_eq_none_iff_validate_eq_err` | `None` iff `validate` returns `UriNotSkillMd(uri)` | (V), (N) | (H) |
| K13+K14 | `skill_name_from_uri`, `validate` | `Skill.exists_skill_name_from_uri_eq_some_of_validate_eq_ok` | if `validate` returns `Ok(())`, `Some(segment)` with a segment that matches the name | (V), (N) | (H) |
| K16+K13 | `validate_skills`, `validate` | `validate_skills_singleton` | on one skill, `validate_skills` returns what `validate` returns | (V), (N), (U) for the skill | (H) |
| model | — | `skillNameOfUri_eq_some_iff` | what `skillNameOfUri` accepts: no `?`/`#`, `dir ++ segment ++ "/SKILL.md"` | none | none |
| model | — | `skillNameOfUri_billing` | example: `billing/SKILL.md` names the skill `billing` | none | none |
| model | — | `isSha256Digest_sha256Digest` | `sha256Digest` of any bytes is well-formed (71 ASCII bytes) | none | none |
| model | — | `nameCharsValid_iff_words` | the name rule as words joined by single `-` | none | none |
| model | — | `validateResult_eq_ok_iff` | `validateResult s = Ok` iff `ValidSkill s` | none | none |
| model | — | `validateResult_eq_err_uriNotSkillMd_iff` | `UriNotSkillMd u` iff the URI names no skill, `u = s.uri` | none | none |
| model | — | `validateResult_eq_err_invalidName_iff` | `InvalidName n` iff the URI names a skill, the name is invalid, `n` is the name | none | none |
| model | — | `validateResult_eq_err_nameMismatch_iff` | `NameMismatch u n` iff the URI names a skill, the name is valid, the segment does not match, with payloads | none | none |
| model | — | `validateResult_eq_err_missingSkillMd_iff` | `MissingSkillMd u` iff checks 1–3 pass, `resources` is a manifest without the skill's URI, `u = s.uri` | none | none |
| model | — | `validateResult_eq_err_iff_firstFileFault_eq_some` | a per-file error `e` iff checks 1–5 pass and `e` is the first file fault (`firstFileFault`) | none | none |
| model | — | `validateResult_ne_err_duplicateSkill` | `validateResult` never gives `DuplicateSkill` | none | none |
| model | — | `validateResult_with_meta` | `validateResult` does not depend on `_meta` | none | none |
| model | — | `firstFileFault_ne_malformedDigest` | files with well-formed digests never give `MalformedDigest` | none | none |
| model | — | `validateSkillsResult_eq_ok_iff` | `validateSkillsResult l = Ok` iff `ValidSkills l` | none | none |
| model | — | `validateSkillsResult_singleton` | `validateSkillsResult [s] = validateResult s` | none | none |
| model | — | `ValidSkills.sublist` | a sublist (e.g. a prefix) of a valid listing is valid | none | none |
| model | — | `validateSkillsResult_append_of_eq_err` | an error of a prefix is the error of the whole listing | none | none |
| model | — | `NfkcFits.of_utf8ByteSize_le` | (N) from the NFKC expansion law and `72 * bytes ≤ isize::MAX` for the name and the URI | the expansion law (a premise about `ExtModel.nfkc`, see (N)) | none |

Each statement is restated as a theorem `Theorems.skill.<name>`, proved by its spec theorem in
`Proofs/Model/Skill/{Basic,Verify,Model,Validate}.lean` (the consequences of the model keep the
names of their proofs, `Defs.Skill.<name>` in `Proofs/Model/Skill/Model.lean`, under
`Theorems.skill.<name>`), and followed by the assumptions its proof depends on, checked by
`#print axioms` under `#guard_msgs`.
-/

open Aeneas Aeneas.Std Result
open Defs (utf8Bytes)
open Defs.Skill
open rmcp.model.skill (SkillsCapability SkillResource SkillFrontmatter Skill SkillResources
  SkillIntegrityError SkillValidationError GetSkillResult)

/-! ## Intermediate public functions (K04, K07, K12–K15) -/

/-- K04 `SkillResource::new`: the entry with URI `u = uri.into()`, digest `d = digest.into()` and
the given size, unchecked (upstream and patched lines 76–82; the conversions in this order).

Premise: caller code. Not covered: (I). -/
theorem Theorems.skill.SkillResource.new {UriLike DigestLike : Type}
    (uriInto : core.convert.Into UriLike String)
    (digestInto : core.convert.Into DigestLike String) (uri : UriLike) (digest : DigestLike)
    (size : U64) (u d : String) (h_uri_into : uriInto.into uri = ok u)
    (h_digest_into : digestInto.into digest = ok d) :
    rmcp.model.skill.SkillResource.new uriInto digestInto uri digest size ⦃
      (result : SkillResource) =>
      result.uri = u ∧
      result.digest = d ∧
      result.size = size ⦄ :=
  rmcp.model.skill.SkillResource.new_spec uriInto digestInto uri digest size u d h_uri_into
    h_digest_into

/--
info: 'Theorems.skill.SkillResource.new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.SkillResource.new

/-- K07 `sha256_digest`: `sha256:` followed by the 64 lowercase hexadecimal digits of the SHA-256
digest of `bytes` (`sha256Digest`, with `ExtModel.sha256` unopened; upstream lines 116–128,
patched lines 116–125 and `lower_hex_digit`, lines 128–130, hunk H1).

No premise. Not covered: (S). -/
theorem Theorems.skill.sha256_digest (bytes : Slice U8) :
    rmcp.model.skill.sha256_digest bytes ⦃ (result : String) =>
      result = sha256Digest bytes.val ⦄ :=
  rmcp.model.skill.sha256_digest_spec bytes

/--
info: 'Theorems.skill.sha256_digest' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.sha256_digest

/-- K12 `Skill::name`: the frontmatter name, as its UTF-8 bytes (`&self.frontmatter.name`,
upstream lines 266–268, patched lines 268–270).

Premise: (Z) on the name. -/
theorem Theorems.skill.Skill.name (self : Skill) (h_name_fits : UsizeFits self.frontmatter.«name») :
    rmcp.model.skill.Skill.name self ⦃ (result : Str) =>
      result.val = utf8Bytes self.frontmatter.«name» ⦄ :=
  rmcp.model.skill.Skill.name_spec self h_name_fits

/--
info: 'Theorems.skill.Skill.name' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.Skill.name

/-- K13 `Skill::validate`: returns `validateResult self` (`Defs.Skill`): the error of the first
failing check, in the Rust order, with its payload, else `Ok(())` (upstream lines 277–319; patched
lines 279–338, hunk H2):

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

Premises: (V) `h_sizes`; (N) `h_nfkc` (patch-induced; see `NfkcFits.of_utf8ByteSize_le`). Not
covered: (H). -/
theorem Theorems.skill.Skill.validate (self : Skill) (h_sizes : SkillFits self)
    (h_nfkc : NfkcFits self) :
    rmcp.model.skill.Skill.validate self ⦃
      (result : core.result.Result Unit SkillValidationError) =>
      result = validateResult self ⦄ :=
  rmcp.model.skill.Skill.validate_spec self h_sizes h_nfkc

/--
info: 'Theorems.skill.Skill.validate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.Skill.validate

/-- K13, corollary: `validate` returns `Ok(())` exactly for a valid skill (`ValidSkill`): the URI
has no query or fragment and ends in `<segment>/SKILL.md`, with the segment non-empty, without
`/`, and at the start of the URI or after a `/` (so `billing/SKILL.md` is accepted); the decoded
segment matches the name in NFKC form; the name is a valid skill name; and, unless `resources`
is `"dynamic"`, the manifest lists the skill's own `SKILL.md`, every file lies within the skill's
directory and has a well-formed digest, and no two files have the same key (`ValidManifest`).

Premises as K13. Not covered: (H). -/
theorem Theorems.skill.Skill.validate_eq_ok_iff (self : Skill) (h_sizes : SkillFits self)
    (h_nfkc : NfkcFits self) :
    rmcp.model.skill.Skill.validate self ⦃
      (result : core.result.Result Unit SkillValidationError) =>
      (result = .Ok () ↔ ValidSkill self) ⦄ :=
  rmcp.model.skill.Skill.validate_eq_ok_iff self h_sizes h_nfkc

/--
info: 'Theorems.skill.Skill.validate_eq_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.Skill.validate_eq_ok_iff

/-- K14 `skill_name_from_uri`: the bytes of the returned slice are `skillNameOfUri uri`: `None`
for a URI with `?` or `#`; otherwise, for a URI ending in `/SKILL.md`, the non-empty segment before
it, still percent-encoded; `None` in every other case (upstream lines 326–333; patched lines
345–352, hunk H3).

Defined on every `Str`; no premise. -/
theorem Theorems.skill.skill_name_from_uri (uri : Str) :
    rmcp.model.skill.skill_name_from_uri uri ⦃ (result : Option Str) =>
      result.map (·.val) = skillNameOfUri uri.val ⦄ :=
  rmcp.model.skill.skill_name_from_uri_spec uri

/--
info: 'Theorems.skill.skill_name_from_uri' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.skill_name_from_uri

/-- K15 `is_sha256_digest`: `true` exactly when `digest` is `sha256:` followed by 64 lowercase
hexadecimal digits (`isSha256Digest`; upstream lines 417–421, patched lines 481–485, hunk H7).

No premise. -/
theorem Theorems.skill.is_sha256_digest (digest : Str) :
    rmcp.model.skill.is_sha256_digest digest ⦃ (result : Bool) =>
      result = isSha256Digest digest.val ⦄ :=
  rmcp.model.skill.is_sha256_digest_spec digest

/--
info: 'Theorems.skill.is_sha256_digest' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.is_sha256_digest

/-! ## Compositions with an intermediate function -/

/-- K07+K15, **a computed digest is well-formed**: `is_sha256_digest` returns `true` on the bytes
of the string that `sha256_digest` returns, whatever the bytes hashed. Nothing is assumed about
`ExtModel.sha256` beyond its type (32 bytes).

No premise. Not covered: (S). -/
theorem Theorems.skill.is_sha256_digest_sha256_digest (bytes : Slice U8) :
    rmcp.model.skill.sha256_digest bytes ⦃ (d : String) =>
      ∀ s : Str, s.val = utf8Bytes d →
        rmcp.model.skill.is_sha256_digest s ⦃ (result : Bool) => result = true ⦄ ⦄ :=
  rmcp.model.skill.is_sha256_digest_sha256_digest bytes

/--
info: 'Theorems.skill.is_sha256_digest_sha256_digest' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.is_sha256_digest_sha256_digest

/-- K11+K13, **`validate` ignores `_meta`**: `validate` of the skill that `with_meta` returns
gives `validateResult self`, what `validate self` gives (K13); `validateResult` reads only the URI,
the frontmatter name and the resources (`validateResult_with_meta`).

Premises: (V), (N) for `self` (`with_meta` keeps the fields they constrain). Not covered: (H). -/
theorem Theorems.skill.Skill.validate_with_meta (self : Skill) (m : rmcp.model.meta.MetaObject)
    (h_sizes : SkillFits self) (h_nfkc : NfkcFits self) :
    rmcp.model.skill.Skill.with_meta self m ⦃ (s : Skill) =>
      rmcp.model.skill.Skill.validate s ⦃
        (result : core.result.Result Unit SkillValidationError) =>
        result = validateResult self ⦄ ⦄ :=
  rmcp.model.skill.Skill.validate_with_meta self m h_sizes h_nfkc

/--
info: 'Theorems.skill.Skill.validate_with_meta' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.Skill.validate_with_meta

/-- K13+K14, **`skill_name_from_uri` returns `None` exactly when `validate` reports
`UriNotSkillMd`**: on the bytes of the skill's URI.

Premises as K13. Not covered: (H). -/
theorem Theorems.skill.Skill.skill_name_from_uri_eq_none_iff_validate_eq_err (self : Skill)
    (uri : Str) (h_uri : uri.val = utf8Bytes self.uri) (h_sizes : SkillFits self)
    (h_nfkc : NfkcFits self) :
    rmcp.model.skill.skill_name_from_uri uri ⦃ (segment : Option Str) =>
      rmcp.model.skill.Skill.validate self ⦃
        (result : core.result.Result Unit SkillValidationError) =>
        (segment = none ↔ result = .Err (.UriNotSkillMd self.uri)) ⦄ ⦄ :=
  rmcp.model.skill.Skill.skill_name_from_uri_eq_none_iff_validate_eq_err self uri h_uri h_sizes
    h_nfkc

/--
info: 'Theorems.skill.Skill.skill_name_from_uri_eq_none_iff_validate_eq_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.Skill.skill_name_from_uri_eq_none_iff_validate_eq_err

/-- K13+K14, **a skill that validates has a name segment that matches its name**: when `validate`
returns `Ok(())`, `skill_name_from_uri` on the bytes of the skill's URI returns `Some(segment)`
with a segment that matches the frontmatter name (`nameMatchesSegment`).

Premises as K13. Not covered: (H). -/
theorem Theorems.skill.Skill.exists_skill_name_from_uri_eq_some_of_validate_eq_ok (self : Skill)
    (uri : Str) (h_uri : uri.val = utf8Bytes self.uri) (h_sizes : SkillFits self)
    (h_nfkc : NfkcFits self) :
    rmcp.model.skill.skill_name_from_uri uri ⦃ (segment : Option Str) =>
      rmcp.model.skill.Skill.validate self ⦃
        (result : core.result.Result Unit SkillValidationError) =>
        (result = .Ok () →
          ∃ seg, segment = some seg ∧ nameMatchesSegment seg.val self.frontmatter.«name» = true) ⦄
      ⦄ :=
  rmcp.model.skill.Skill.exists_skill_name_from_uri_eq_some_of_validate_eq_ok self uri h_uri
    h_sizes h_nfkc

/--
info: 'Theorems.skill.Skill.exists_skill_name_from_uri_eq_some_of_validate_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.Skill.exists_skill_name_from_uri_eq_some_of_validate_eq_ok

/-- K16+K13, **one skill: `validate_skills` is `validate`**: for a listing of exactly one skill
`s`, `validate_skills` returns what `validate s` returns (no duplicate is possible).

Premises: (V), (N), (U) for `s`. They are sufficient, not exact: (U) is used only when `validate`
succeeds, the file premises of (V) only up to the first faulty file, and every value held in
memory meets them. Not covered: (H). -/
theorem Theorems.skill.validate_skills_singleton (skills : Slice Skill) (s : Skill)
    (h_one : skills.val = [s]) (h_sizes : SkillFits s) (h_uri_fits : UriFits s.uri)
    (h_nfkc : NfkcFits s) :
    rmcp.model.skill.validate_skills skills ⦃
      (result : core.result.Result Unit SkillValidationError) =>
      rmcp.model.skill.Skill.validate s ⦃
        (result' : core.result.Result Unit SkillValidationError) =>
        result = result' ⦄ ⦄ :=
  rmcp.model.skill.validate_skills_singleton skills s h_one h_sizes h_uri_fits h_nfkc

/--
info: 'Theorems.skill.validate_skills_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.validate_skills_singleton

/-! ## Consequences of the model (statements about `Defs.Skill` only) -/

/-- Model, **what `skillNameOfUri` accepts**: it returns `some segment` exactly when the URI has
no `?` or `#`, and is `dir ++ segment ++ "/SKILL.md"` for a non-empty `segment` without `/` and a
`dir` that is empty or ends in `/`. So a URI that names a skill ends in `<segment>/SKILL.md`, with
the segment at the start or after a `/`. -/
theorem Theorems.skill.skillNameOfUri_eq_some_iff (uri segment : List U8) :
    skillNameOfUri uri = some segment ↔
      (∀ b ∈ uri, isQueryOrFragmentStart b = false) ∧ segment ≠ [] ∧ asciiByte '/' ∉ segment ∧
        ∃ dir, uri = dir ++ segment ++ utf8Bytes "/SKILL.md" ∧
          (dir = [] ∨ dir.getLast? = some (asciiByte '/')) :=
  Defs.Skill.skillNameOfUri_eq_some_iff uri segment

/--
info: 'Theorems.skill.skillNameOfUri_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.skillNameOfUri_eq_some_iff

/-- Model, **a URI without a scheme or directory names a skill**: `billing/SKILL.md` names the
skill `billing` (the segment is at the start of the URI). -/
theorem Theorems.skill.skillNameOfUri_billing :
    skillNameOfUri (utf8Bytes "billing/SKILL.md") = some (utf8Bytes "billing") :=
  Defs.Skill.skillNameOfUri_billing

/--
info: 'Theorems.skill.skillNameOfUri_billing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.skillNameOfUri_billing

/-- Model, **a computed digest is well-formed**: `sha256Digest` of any bytes passes
`isSha256Digest`. In particular it is 71 ASCII bytes: `sha256:` and 64 lowercase hexadecimal
digits. -/
theorem Theorems.skill.isSha256Digest_sha256Digest (bytes : List U8) :
    isSha256Digest (utf8Bytes (sha256Digest bytes)) = true :=
  Defs.Skill.isSha256Digest_sha256Digest bytes

/--
info: 'Theorems.skill.isSha256Digest_sha256Digest' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.isSha256Digest_sha256Digest

/-- Model, **the skill-name rule as words**: `cs` passes `nameCharsValid alnum` exactly when it has
at most 64 characters and is one or more non-empty words of `alnum` characters joined by single
`-`. -/
theorem Theorems.skill.nameCharsValid_iff_words (alnum : Char → Bool) (cs : List Char) :
    nameCharsValid alnum cs = true ↔
      cs.length ≤ 64 ∧ ∃ words : List (List Char), words ≠ [] ∧
        (∀ w ∈ words, w ≠ [] ∧ ∀ c ∈ w, alnum c = true) ∧ cs = List.intercalate ['-'] words :=
  Defs.Skill.nameCharsValid_iff_words alnum cs

/--
info: 'Theorems.skill.nameCharsValid_iff_words' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.nameCharsValid_iff_words

/-- Model, **`validateResult` is `Ok` exactly for a valid skill** (`ValidSkill`): the order of the
checks matters only for which error is returned. -/
theorem Theorems.skill.validateResult_eq_ok_iff (s : Skill) :
    validateResult s = .Ok () ↔ ValidSkill s :=
  Defs.Skill.validateResult_eq_ok_iff s

/--
info: 'Theorems.skill.validateResult_eq_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.validateResult_eq_ok_iff

/-- Model, **when `validate` reports `UriNotSkillMd`** (check 1): exactly when the URI names no
skill, with the skill's URI as payload. -/
theorem Theorems.skill.validateResult_eq_err_uriNotSkillMd_iff (s : Skill) (u : String) :
    validateResult s = .Err (.UriNotSkillMd u) ↔
      skillNameOfUri (utf8Bytes s.uri) = none ∧ u = s.uri :=
  Defs.Skill.validateResult_eq_err_uriNotSkillMd_iff s u

/--
info: 'Theorems.skill.validateResult_eq_err_uriNotSkillMd_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.validateResult_eq_err_uriNotSkillMd_iff

/-- Model, **when `validate` reports `InvalidName`** (check 2): exactly when the URI names a skill
and the frontmatter name is not a valid skill name, with the name as payload. -/
theorem Theorems.skill.validateResult_eq_err_invalidName_iff (s : Skill) (n : String) :
    validateResult s = .Err (.InvalidName n) ↔
      (skillNameOfUri (utf8Bytes s.uri)).isSome ∧ isSkillName s.frontmatter.«name» = false ∧
        n = s.frontmatter.«name» :=
  Defs.Skill.validateResult_eq_err_invalidName_iff s n

/--
info: 'Theorems.skill.validateResult_eq_err_invalidName_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.validateResult_eq_err_invalidName_iff

/-- Model, **when `validate` reports `NameMismatch`** (check 3): exactly when the URI names a skill
with segment `encoded`, the name is valid, and the segment does not match the name, with the
skill's URI and name as payload. -/
theorem Theorems.skill.validateResult_eq_err_nameMismatch_iff (s : Skill) (u n : String) :
    validateResult s = .Err (.NameMismatch u n) ↔
      ∃ encoded, skillNameOfUri (utf8Bytes s.uri) = some encoded ∧
        isSkillName s.frontmatter.«name» = true ∧
        nameMatchesSegment encoded s.frontmatter.«name» = false ∧
        u = s.uri ∧ n = s.frontmatter.«name» :=
  Defs.Skill.validateResult_eq_err_nameMismatch_iff s u n

/--
info: 'Theorems.skill.validateResult_eq_err_nameMismatch_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.validateResult_eq_err_nameMismatch_iff

/-- Model, **when `validate` reports `MissingSkillMd`** (check 5): exactly when the URI names a
skill with segment `encoded`, the name is valid and matches the segment, `resources` is a manifest
`files` (not `"dynamic"`), and no file of it has exactly the skill's URI, with the skill's URI as
payload (upstream lines 297–299, patched lines 300–311). -/
theorem Theorems.skill.validateResult_eq_err_missingSkillMd_iff (s : Skill) (u : String) :
    validateResult s = .Err (.MissingSkillMd u) ↔
      ∃ encoded files, skillNameOfUri (utf8Bytes s.uri) = some encoded ∧
        isSkillName s.frontmatter.«name» = true ∧
        nameMatchesSegment encoded s.frontmatter.«name» = true ∧
        s.resources = .Files files ∧ (∀ f ∈ files.val, f.uri ≠ s.uri) ∧ u = s.uri :=
  Defs.Skill.validateResult_eq_err_missingSkillMd_iff s u

/--
info: 'Theorems.skill.validateResult_eq_err_missingSkillMd_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.validateResult_eq_err_missingSkillMd_iff

/-- Model, **when `validate` reports a per-file error** (check 6): for an error `e` of the kind
`ResourceOutsideSkill`, `DuplicateResource` or `MalformedDigest`, `validate` reports `e` exactly
when checks 1–5 pass (the URI names a skill with segment `encoded`, the name is valid and matches
the segment, `resources` is a manifest `files` that has a file with exactly the skill's URI) and
`e` is the fault of the first faulty file of the manifest (`firstFileFault`, with its payload;
upstream lines 300–317, patched lines 312–337). -/
theorem Theorems.skill.validateResult_eq_err_iff_firstFileFault_eq_some (s : Skill)
    (e : SkillValidationError)
    (he : (∃ uri skillUri, e = .ResourceOutsideSkill uri skillUri) ∨
      (∃ uri, e = .DuplicateResource uri) ∨ (∃ uri digest, e = .MalformedDigest uri digest)) :
    validateResult s = .Err e ↔
      ∃ encoded files, skillNameOfUri (utf8Bytes s.uri) = some encoded ∧
        isSkillName s.frontmatter.«name» = true ∧
        nameMatchesSegment encoded s.frontmatter.«name» = true ∧
        s.resources = .Files files ∧ (∃ f ∈ files.val, f.uri = s.uri) ∧
        firstFileFault s.uri [] files.val = some e :=
  Defs.Skill.validateResult_eq_err_iff_firstFileFault_eq_some s e he

/--
info: 'Theorems.skill.validateResult_eq_err_iff_firstFileFault_eq_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.validateResult_eq_err_iff_firstFileFault_eq_some

/-- Model, **`validate` never reports `DuplicateSkill`**: that error belongs to `validate_skills`
(upstream line 429, patched line 493). With the five `validateResult_eq_err_…` statements above,
every `Err` case of `validateResult` is characterised. -/
theorem Theorems.skill.validateResult_ne_err_duplicateSkill (s : Skill) (u : String) :
    validateResult s ≠ .Err (.DuplicateSkill u) :=
  Defs.Skill.validateResult_ne_err_duplicateSkill s u

/--
info: 'Theorems.skill.validateResult_ne_err_duplicateSkill' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.validateResult_ne_err_duplicateSkill

/-- Model, **`validateResult` does not depend on `_meta`**. -/
theorem Theorems.skill.validateResult_with_meta (s : Skill)
    (m : Option rmcp.model.meta.MetaObject) :
    validateResult { s with «meta» := m } = validateResult s :=
  Defs.Skill.validateResult_with_meta s m

/--
info: 'Theorems.skill.validateResult_with_meta' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.validateResult_with_meta

/-- Model, **well-formed digests never give `MalformedDigest`**: if every file of `files` has a
well-formed digest (e.g. an entry made by `from_bytes`, `SkillResource.isSha256Digest_from_bytes`),
the first file fault is not a `MalformedDigest`. -/
theorem Theorems.skill.firstFileFault_ne_malformedDigest (skillUri : String)
    (earlier files : List SkillResource)
    (h : ∀ f ∈ files, isSha256Digest (utf8Bytes f.digest) = true) (uri digest : String) :
    firstFileFault skillUri earlier files ≠ some (.MalformedDigest uri digest) :=
  Defs.Skill.firstFileFault_ne_malformedDigest skillUri earlier files h uri digest

/--
info: 'Theorems.skill.firstFileFault_ne_malformedDigest' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Theorems.skill.firstFileFault_ne_malformedDigest

/-- Model, **`validateSkillsResult` is `Ok` exactly for a valid listing** (`ValidSkills`). -/
theorem Theorems.skill.validateSkillsResult_eq_ok_iff (skills : List Skill) :
    validateSkillsResult skills = .Ok () ↔ ValidSkills skills :=
  Defs.Skill.validateSkillsResult_eq_ok_iff skills

/--
info: 'Theorems.skill.validateSkillsResult_eq_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.validateSkillsResult_eq_ok_iff

/-- Model, **one skill**: the expected result of `validate_skills` on `[s]` is that of
`validate s`. -/
theorem Theorems.skill.validateSkillsResult_singleton (s : Skill) :
    validateSkillsResult [s] = validateResult s :=
  Defs.Skill.validateSkillsResult_singleton s

/--
info: 'Theorems.skill.validateSkillsResult_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.validateSkillsResult_singleton

/-- Model, **a sublist of a valid listing is valid**, in particular a prefix `l₁` of `l₁ ++ l₂`:
each skill stays valid and distinct keys stay distinct. The concatenation of two valid listings
need not be valid: they can share a key. -/
theorem Theorems.skill.ValidSkills.sublist {l₁ l₂ : List Skill} (h : l₁.Sublist l₂)
    (hv : ValidSkills l₂) :
    ValidSkills l₁ :=
  Defs.Skill.ValidSkills.sublist h hv

/--
info: 'Theorems.skill.ValidSkills.sublist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.ValidSkills.sublist

/-- Model, **an error of a prefix is the error of the listing**: the walk reaches the faulty skill
of `l₁` before any skill of `l₂`. -/
theorem Theorems.skill.validateSkillsResult_append_of_eq_err {l₁ : List Skill} (l₂ : List Skill)
    {e : SkillValidationError} (h : validateSkillsResult l₁ = .Err e) :
    validateSkillsResult (l₁ ++ l₂) = .Err e :=
  Defs.Skill.validateSkillsResult_append_of_eq_err l₂ h

/--
info: 'Theorems.skill.validateSkillsResult_append_of_eq_err' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.validateSkillsResult_append_of_eq_err

/-- Model, **the NFKC premise (N) from the NFKC expansion bound** (bridge lemma). The premise
`hexp` is a law about the opaque `ExtModel.nfkc`, over every input: the NFKC form of `m` characters
has at most `18 * m` characters. It is true of the real function: NFKC is the full compatibility
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
theorem Theorems.skill.NfkcFits.of_utf8ByteSize_le (s : Skill)
    (hexp : ∀ cs, (ExtModel.nfkc cs).length ≤ 18 * cs.length)
    (hname : 72 * s.frontmatter.«name».utf8ByteSize ≤ ExtModel.maxStringBytes)
    (huri : 72 * s.uri.utf8ByteSize ≤ ExtModel.maxStringBytes) : NfkcFits s :=
  Defs.Skill.NfkcFits.of_utf8ByteSize_le s hexp hname huri

/--
info: 'Theorems.skill.NfkcFits.of_utf8ByteSize_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.NfkcFits.of_utf8ByteSize_le
