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
# Public API of `crates/rmcp/src/model/skill.rs` (K01–K20)

One row per theorem below; the theorem is `Theorems.skill.<Theorem>`. In the ID column, `Kxx cor.`
is a corollary of one spec theorem (K06 cor., K09 cor., K13 cor., K16 cor.); a composition is
labelled by the spec theorems it uses (`K05+K06`; `K05 (K07)` for `from_bytes` described with the
digest of K07; `K05 (model)` for `from_bytes` combined with a consequence of the model); `model` is
a consequence of the model (a statement about the definitions of `Defs.Skill` only, with no Rust
call). The keys of the last two columns are explained in "Premises" and "Not covered" below; they
are local to this file (`Specs/Model/RequestState.lean` uses some of the same letters with other
meanings).

| ID | Function | Theorem | Guarantee | Premises (caller must ensure) | Not covered (Rust may panic or behave otherwise; the model does not) |
|---|---|---|---|---|---|
| K01 | `Resource::is_directory` | `Resource.is_directory` | `true` iff the MIME type is `Some("inode/directory")` | (Z) | none |
| K02 | `SkillsCapability::new` | `SkillsCapability.new` | `directory_read = false` | none | none |
| K03 | `SkillsCapability::with_directory_read` | `SkillsCapability.with_directory_read` | `directory_read = true` (its only field) | none | none |
| K04 | `SkillResource::new` | `SkillResource.new` | the entry with the converted URI and digest and the size | caller code | (I) |
| K05 | `SkillResource::from_bytes` | `SkillResource.from_bytes` | the converted URI, `sha256Digest bytes`, the byte length | caller code | (I), (S) |
| K06 | `SkillResource::verify` | `SkillResource.verify` | `Ok` iff length and digest match; else `Size` (length first), else `Digest`, with payloads | none | (S) |
| K07 | `sha256_digest` | `sha256_digest` | `sha256:` and the lowercase hex of the SHA-256 digest (`sha256Digest`) | none | (S) |
| K08 | `SkillFrontmatter::new` | `SkillFrontmatter.new` | the converted name and description, no extra field | caller code | (I) |
| K09 | `SkillFrontmatter::with_field` | `SkillFrontmatter.with_field` | `extra` with `key ↦ value` set, other keys and fields unchanged; still sorted if it was | caller code | (I), (P) |
| K09 cor. | same | `SkillFrontmatter.with_field_extra_entries_eq_mapInsert` | `extra` is `ExtModel.mapInsert k v self.extra.entries` (the model of `BTreeMap::insert`) | caller code | (I), (P) |
| K10 | `Skill::new` | `Skill.new` | the converted URI, the frontmatter and resources given, no `_meta` | caller code | (I) |
| K11 | `Skill::with_meta` | `Skill.with_meta` | `_meta = Some(meta)`, other fields unchanged | none | none |
| K12 | `Skill::name` | `Skill.name` | the bytes of the frontmatter name | (Z) | none |
| K13 | `Skill::validate` | `Skill.validate` | `validateResult self`: the first failing check in the Rust order, with payloads | (V), (N) | (H) |
| K13 cor. | same | `Skill.validate_eq_ok_iff` | `Ok` iff `ValidSkill self` | (V), (N) | (H) |
| K14 | `skill_name_from_uri` | `skill_name_from_uri` | `skillNameOfUri uri` | none | none |
| K15 | `is_sha256_digest` | `is_sha256_digest` | `isSha256Digest digest` | none | none |
| K16 | `validate_skills` | `validate_skills` | `validateSkillsResult skills`: the first skill error or `DuplicateSkill` | (V), (N), (U) for each skill | (H) |
| K16 cor. | same | `validate_skills_eq_ok_iff` | `Ok` iff every skill is valid and the normalised URIs are distinct (`ValidSkills`) | as K16 | (H) |
| K17 | `GetSkillResult::new` | `GetSkillResult.new` | `result_type = Some(COMPLETE)`, the skill, no TTL, cache scope or `_meta` | none | none |
| K18 | `GetSkillResult::with_ttl_ms` | `GetSkillResult.with_ttl_ms` | `ttl_ms = Some(ttl_ms)`, other fields unchanged | none | none |
| K19 | `GetSkillResult::with_cache_scope` | `GetSkillResult.with_cache_scope` | `cache_scope = Some(cache_scope)`, other fields unchanged | none | none |
| K20 | `GetSkillResult::with_meta` | `GetSkillResult.with_meta` | `_meta = Some(meta)`, other fields unchanged | none | none |
| K05+K06 | `from_bytes`, then `verify` | `SkillResource.verify_from_bytes_self` | an entry made from bytes verifies them (`Ok(())`) | caller code | (I), (S) |
| K05+K06 | `from_bytes`, then `verify` | `SkillResource.verify_from_bytes` | against other bytes: `Ok` iff same length and SHA-256 digest; else `Size` or `Digest`, with payloads | caller code | (I), (S) |
| K05 (K07) | `from_bytes` | `SkillResource.from_bytes_eq` | the computation `uri.into()`, then the entry with digest `sha256Digest bytes` and size `bytes.len()` | none | (S) |
| K05 (model) | `from_bytes` | `SkillResource.isSha256Digest_from_bytes` | the entry's digest is well-formed (`isSha256Digest`; so never `MalformedDigest`) | caller code | (I), (S) |
| K06 cor. | `verify` | `SkillResource.verify_eq_ok_iff` | `Ok` iff the length is `size` and `sha256Digest bytes = digest` | none | (S) |
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

## What this file promises

`skill.rs` describes a skill (a directory of files served as resources): its `SKILL.md`
frontmatter, its manifest of files with their `sha256:` digests and sizes, and the result of
`skills/get`. For each of the twenty public functions, a statement below says that the call, in
the Lean model, terminates without panicking, and what it returns: the value built (K02–K05,
K08–K11, K17–K20), the bytes or digest computed (K07, K12, K14, K15), or, for a `Result`, the
`Ok` case and every `Err` case with its payload in the Rust order of checks (K06, K13, K16).
The `Result`-returning functions are stated by an expected result written in `Defs.Skill`
(`validateResult`, `validateSkillsResult`) or by a `match result with` whose arms are in the Rust
order; each postcondition determines `result` uniquely (K09: when `self.extra` is sorted
(`KeysSorted`), the sorted entries of the result are fixed by their lookups, and K09 cor. gives
them for any entry list; K05: a `U64` is fixed by its value). Each holds under its premises, only
in the translated configuration ("Provenance"); Rust may still panic, or behave otherwise, in the
cases under "Not covered".

**Builders.** The postconditions of the builders fix every field of the value built: K10 and
K11 the four fields of `Skill`, K17–K20 the five fields of `GetSkillResult`, K02 and K03 the one
field of `SkillsCapability`. So two builders that set different fields commute (e.g.
`with_ttl_ms` then `with_cache_scope` gives the same `GetSkillResult` as the other order), and
of two calls of the same builder the last one wins. Two `with_field` calls (K09) on different
keys give the same lookups in either order.

## How to read a statement

`f x ⦃ (result : T) => P result ⦄` says that `f x` terminates without panicking in the Lean model
and that `result` satisfies `P` (plan Section 3). Hypotheses `(h_… : …)` are **premises** the
caller must ensure, and nothing is promised when one fails; the "Not covered" cases are inputs
or environments where Rust panics or behaves otherwise while the statement promises a result.
Rust strings are read as their UTF-8 bytes (`Defs.utf8Bytes`, the `val` of a `Str`). The three
opaque constants `ExtModel.sha256`, `ExtModel.nfkc` and `ExtModel.generalCategory` appear only
unopened, inside `sha256Digest`, `isSkillName`, `nameMatchesSegment`, `NfkcFits` and directly in
`verify_from_bytes`, as the values the Rust code computes. No statement assumes a law about them,
except `NfkcFits.of_utf8ByteSize_le`, which takes the NFKC expansion bound as an explicit
premise in law (implication) form (review rule of `formal/README.md`, "Trusted base").

Translated functions are written in full (`rmcp.model.skill.…`), as a bare name would resolve to
a restated theorem. The model consequences (`model` rows) are about the definitions of
`Defs.Skill` only; they keep the names of their proofs, `Defs.Skill.<name>`, under
`Theorems.skill.<name>`.

## Premises (caller must ensure)

* **caller code** (`h_*_into`): a conversion of the caller (`Into<String>`,
  `Into<serde_json::Value>`; user code) returns the value the hypothesis names. The standard
  `From` impls for `&str` and `String` do.
* **(Z)** `UsizeFits`: the string has at most `usize::MAX` UTF-8 bytes (the bound of the Lean
  model of `String::deref`). Every Rust `String` meets it.
* **(V)** `SkillFits self`: the URI and the name meet (Z); every manifest file's URI meets
  `UriFits` (`24 * (n + 1) ≤ isize::MAX` for `n` bytes) and its digest (Z). Every skill held in
  memory meets it (address space at most `2^57` bytes). Partly patch-induced (the `Vec`s of
  `prim::split_slash`/`split_percent`).
* **(N)** `NfkcFits self`, **patch-induced**, a declared domain restriction (translation patch 04,
  hunks H2 and H4; evidence `formal/trusted/evidence/README.md`): the NFKC forms of the name and
  of the decoded URI segment, where `validate` computes them, have at most `isize::MAX / 4`
  characters. The patched copy collects them into a `Vec<char>` (`prim::nfkc`) and panics above
  that, the original streams them and does not. By the bridge lemma
  `Theorems.skill.NfkcFits.of_utf8ByteSize_le` (last below) it follows from `72 * n ≤ isize::MAX`
  for the `n` UTF-8 bytes of the name and of the URI (so it excludes no name or URI of at most
  `2^56` bytes), given the law that NFKC expands a character sequence of length `m` to at most
  `18 * m` characters (the largest expansion is `U+FDFA`, 18 characters), which the caller
  supplies as a premise.
* **(U)** `UriFits s.uri` for each skill of `validate_skills` (its URI is percent-normalised).

## Not covered (inherited exceptions)

* **(I)** K04, K05, K08–K10, K09 cor. and the compositions with a caller-code premise
  (`SkillResource.verify_from_bytes_self`, `SkillResource.verify_from_bytes`,
  `SkillResource.isSha256Digest_from_bytes`; not `SkillResource.from_bytes_eq`, an equation of two
  computations that both call the caller's conversion): the caller-code premises describe the
  caller's `Into` impls as functions of their argument (the Aeneas translation of the traits); code
  with side effects or that reads global state is not described. A `Drop` impl of a caller value
  that panics is not translated.
* **(S)** SHA-256: the model of `prim::sha256` always succeeds, while the `u64` bit counter of
  `sha2` overflows (a panic under `overflow-checks`) for an input of at least `2^61` bytes
  (`sha2-0.11.2/src/block_api.rs` line 66), outside the size convention of
  `trusted/Rmcp/FunsExternal.lean`. It concerns the statements that hash: K05 and K07 (always),
  K06 (only when the length matches, as the size is checked first), and the compositions built
  on them: `SkillResource.verify_from_bytes_self`, `SkillResource.verify_from_bytes`,
  `SkillResource.from_bytes_eq`, `SkillResource.isSha256Digest_from_bytes`,
  `SkillResource.verify_eq_ok_iff` and `is_sha256_digest_sha256_digest`. No other statement
  hashes.
* **(P)** `serde_json` feature `preserve_order` (K09, K09 cor.): the model is the `BTreeMap`
  that `serde_json::Map` is in the translated configuration (`Cargo.lock`: `serde_json 1.0.154`
  without `indexmap`; `STATUS.md` at 9047c72, "`serde_json::Map`"). Cargo feature unification
  turns `preserve_order` on when any crate of a downstream build enables it; `serde_json::Map` is
  then an `IndexMap` in insertion order (`serde_json-1.0.154/src/map.rs` lines 3–4 and 28–31).
  The lookup clause of K09 still holds then; the order clauses (`KeysSorted` in K09, the
  `ExtModel.mapInsert` entries of K09 cor.) do not. K08 (`extra` empty) holds either way.
* **(H)** `HashSet::with_capacity` (K13, K16 and the compositions that call them): the random
  hash keys and a failing operating-system random source are not modelled
  (`ExtModel.randomState`; model of `HashSet::with_capacity`). The statements depend only on
  membership in the set, never on its order or hash keys.

## Provenance

*Scope.* The public API of `skill.rs` (functions `pub` in upstream rmcp; human decision
2026-11-24): the twenty public functions K01–K20 (human decision of 2026-11-25), with corollaries,
compositions and the consequences of the model `Defs.Skill`.

*Order.* K01–K20 are in Rust source order (= ID order), each corollary after its statement; then
the compositions, then the consequences of the model.

*Proofs.* Each statement is restated as a theorem `Theorems.skill.<Type>.<function>` (free
functions `Theorems.skill.<function>`; corollaries, compositions and model consequences keep the
descriptive name of their proof), proved by its spec theorem in
`Proofs/Model/Skill/{Basic,Verify,Model,Validate}.lean` (with the helpers of `Common` and
`ValidateHelpers`), and followed by the assumptions its proof depends on, checked by
`#print axioms` under `#guard_msgs`. The restated text is that of the signed-off statements
(function names written in full).

*Sign-off.* The 51 statements: signed off by the spec owner (Hoang Le Truong) on 2026-11-25
(the signed-off text was in `specs/Drafts/Skill.lean`, removed at incorporation). Translation
stage (patch 04 and its external models): signed off on 2026-11-25. Incorporation approved by the
human on 2026-11-25.

*Linkage.* K01–K04, K08–K12 and K17–K20 are ORIGINAL: they translate from code of upstream
`7caec76` that translation patch 04 leaves unmodified (checked by
`scripts/check-original-linkage.sh`). K05–K07 and K13–K16 translate from code that patch 04
changes (hunks H1–H9 of `formal/trusted/patches/04-skill-public.patch`; the patch header gives the
reason and why each value is unchanged).

*Translated configuration* (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
`--no-default-features` with the features `request-state`, `server`, `client`, `client-side-sse`,
`transport-streamable-http-server`, `transport-streamable-http-client` and `auth` (plan
Section 15), with `overflow-checks=true` and `debug-assertions=true` (plan Section 1). Aeneas
`nightly-2026.11.24-fb44cb4`. The translation is of upstream origin/main `7caec76` with
translation patches 01–04 applied in order (`scripts/apply-patches.sh`).

*Line citations*: "upstream" is `crates/rmcp/src/model/skill.rs` at `7caec76` (= working tree);
"patched" is `.llbc/work/crates/rmcp/src/model/skill.rs` (patches 01–04), whose line numbers the
`Source:` lines of `Rmcp/Funs.lean` give. They agree up to line 103.

*Not translated (not specified)*: the `Serialize`/`Deserialize` impls (including that of
`SkillResources`, upstream lines 191–216, and its constant `DYNAMIC`, line 189), the `JsonSchema`
impls, the derived `Debug`, `Clone`, `PartialEq` impls, the `Display`/`Error` impls of
`SkillIntegrityError` and `SkillValidationError`, the private `is_false` (upstream line 57) and
the constant `SKILLS_EXTENSION_ID` (line 21).

*Translated, specified only through `Defs.Skill`*: the public constants `DIRECTORY_MIME_TYPE` (line
24; the text `"inode/directory"` of K01) and `SKILL_MD` (upstream line 323, patched 342; `skillMd`),
the derived `Default` of `SkillsCapability` (line 34, called by K02); the private upstream functions
`is_valid_skill_name` (`isSkillName`), `manifest_resource_key` (`manifestKey`) and
`normalize_percent_encoding` (`normalizePercent`); the private helpers that translation patch 04
adds, `lower_hex_digit` (`lowerHexDigit`), `is_unreserved` (`isUnreserved`), `is_ascii_hex` (it
tests a whole `&str`; `isHexDigit` tests one byte, and `normalizePart` applies it to the two bytes
after a `%`), `push_normalized_part` (`normalizePart`), `resolve_segment` and `resolve_segments`
(`removeDotSegments`); the loop bodies and closures that Aeneas extracts from `sha256_digest`,
`is_valid_skill_name`, `is_ascii_hex` (patched lines 467–474), `normalize_percent_encoding`,
`resolve_segments`, `validate`, `is_sha256_digest` and `validate_skills`; and the patch-only module
`skill::prim` (patched lines 581–638), whose twelve functions are not translated but modelled in
`trusted/Rmcp/FunsExternal.lean` (section "Public `skill.rs` API"). Their own statements, if any,
belong to `formal/proofs/Proofs/Internal/` (STYLE_GUIDE, "Spec Files").

*Definitions used*: those of `Defs.Skill` (`formal/specs/Defs/Skill.lean`) and `Defs.utf8Bytes`.

*Native-code assumptions:* none (`native-axioms.lock` empty).
-/

open Aeneas Aeneas.Std Result
open Defs (utf8Bytes)
open Defs.Skill
open rmcp.model.skill (SkillsCapability SkillResource SkillFrontmatter Skill SkillResources
  SkillIntegrityError SkillValidationError GetSkillResult)

/-! ## K01: `Resource::is_directory` -/

/-- K01 `Resource::is_directory`: `true` exactly when the MIME type is `Some("inode/directory")`
(`DIRECTORY_MIME_TYPE`, upstream line 24; `self.mime_type.as_deref() == Some(DIRECTORY_MIME_TYPE)`,
upstream and patched lines 28–30).

Premise: (Z) on the MIME type. -/
theorem Theorems.skill.Resource.is_directory (self : rmcp.model.resource.Resource)
    (h_mime_fits : ∀ t, self.mime_type = some t → UsizeFits t) :
    rmcp.model.skill.Resource.is_directory self ⦃ (result : Bool) =>
      (result = true ↔ self.mime_type = some "inode/directory") ⦄ :=
  rmcp.model.skill.Resource.is_directory_spec self h_mime_fits

/--
info: 'Theorems.skill.Resource.is_directory' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.Resource.is_directory

/-! ## K02, K03: `SkillsCapability` -/

/-- K02 `SkillsCapability::new`: the capability without directory reads (`Self::default()`,
upstream and patched lines 46–48; the derived `Default`, line 34, gives `directory_read: false`). -/
theorem Theorems.skill.SkillsCapability.new :
    rmcp.model.skill.SkillsCapability.new ⦃ (result : SkillsCapability) =>
      result.directory_read = false ⦄ :=
  rmcp.model.skill.SkillsCapability.new_spec

/--
info: 'Theorems.skill.SkillsCapability.new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.SkillsCapability.new

/-- K03 `SkillsCapability::with_directory_read`: sets `directory_read` to `true` (upstream and
patched lines 51–54); it is the only field of `SkillsCapability` (lines 38–42), so calling it twice
gives the same value as once. -/
theorem Theorems.skill.SkillsCapability.with_directory_read (self : SkillsCapability) :
    rmcp.model.skill.SkillsCapability.with_directory_read self ⦃ (result : SkillsCapability) =>
      result.directory_read = true ⦄ :=
  rmcp.model.skill.SkillsCapability.with_directory_read_spec self

/--
info: 'Theorems.skill.SkillsCapability.with_directory_read' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.SkillsCapability.with_directory_read

/-! ## K04–K06: `SkillResource` -/

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

/-- K05 `SkillResource::from_bytes`: the entry for `bytes` at URI `u = uri.into()`; its digest is
`sha256Digest bytes` (K07) and its size the byte length
(`Self::new(uri, sha256_digest(bytes), bytes.len() as u64)`, upstream and patched lines 85–87;
`as u64` is exact, `usize` having at most 64 bits).

Premise: caller code. Not covered: (I), (S). -/
theorem Theorems.skill.SkillResource.from_bytes {UriLike : Type}
    (uriInto : core.convert.Into UriLike String)
    (uri : UriLike) (bytes : Slice U8) (u : String) (h_uri_into : uriInto.into uri = ok u) :
    rmcp.model.skill.SkillResource.from_bytes uriInto uri bytes ⦃ (result : SkillResource) =>
      result.uri = u ∧
      result.digest = sha256Digest bytes.val ∧
      result.size.val = bytes.val.length ⦄ :=
  rmcp.model.skill.SkillResource.from_bytes_spec uriInto uri bytes u h_uri_into

/--
info: 'Theorems.skill.SkillResource.from_bytes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.SkillResource.from_bytes

/-- K06 `SkillResource::verify`: checks the size first, then the digest (upstream lines 94–112;
patched lines 94–112, hunk H9 swaps the branches of the digest test without changing the result):

* `Ok(())` exactly when `bytes` has the promised length and its digest `sha256Digest bytes` is
  the promised one;
* `Err(Size { uri, expected: self.size, actual: bytes.len() })` when the length differs
  (upstream lines 95–102), whatever the digest;
* `Err(Digest { uri, expected: self.digest, actual: sha256Digest bytes })` when the length is
  right and the digest differs (upstream lines 103–110).

No premise. Not covered: (S). -/
theorem Theorems.skill.SkillResource.verify (self : SkillResource) (bytes : Slice U8) :
    rmcp.model.skill.SkillResource.verify self bytes ⦃
      (result : core.result.Result Unit SkillIntegrityError) =>
      match result with
      | .Ok () =>
        bytes.val.length = self.size.val ∧ sha256Digest bytes.val = self.digest
      | .Err (.Size uri expected actual) =>
        bytes.val.length ≠ self.size.val ∧
          uri = self.uri ∧ expected = self.size ∧ actual.val = bytes.val.length
      | .Err (.Digest uri expected actual) =>
        bytes.val.length = self.size.val ∧ sha256Digest bytes.val ≠ self.digest ∧
          uri = self.uri ∧ expected = self.digest ∧ actual = sha256Digest bytes.val ⦄ :=
  rmcp.model.skill.SkillResource.verify_spec self bytes

/--
info: 'Theorems.skill.SkillResource.verify' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.SkillResource.verify

/-! ## K07: `sha256_digest` -/

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

/-! ## K08, K09: `SkillFrontmatter` -/

/-- K08 `SkillFrontmatter::new`: the frontmatter with name `n = name.into()`, description
`d = description.into()` and no other field (`JsonObject::new()`; upstream lines 161–167, patched
lines 163–169). The empty map is sorted (`KeysSorted`), as K09 then keeps it.

Premise: caller code. Not covered: (I). -/
theorem Theorems.skill.SkillFrontmatter.new {NameLike DescriptionLike : Type}
    (nameInto : core.convert.Into NameLike String)
    (descriptionInto : core.convert.Into DescriptionLike String) («name» : NameLike)
    (description : DescriptionLike) (n d : String) (h_name_into : nameInto.into «name» = ok n)
    (h_description_into : descriptionInto.into description = ok d) :
    rmcp.model.skill.SkillFrontmatter.new nameInto descriptionInto «name» description ⦃
      (result : SkillFrontmatter) =>
      result.«name» = n ∧
      result.description = d ∧
      result.extra.entries = [] ⦄ :=
  rmcp.model.skill.SkillFrontmatter.new_spec nameInto descriptionInto «name» description n d
    h_name_into h_description_into

/--
info: 'Theorems.skill.SkillFrontmatter.new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.SkillFrontmatter.new

/-- K09 `SkillFrontmatter::with_field`: in the Lean model a `serde_json::Map` is its list of
entries; every map Rust builds is sorted (`KeysSorted`; in the translated configuration, see (P)).
`with_field` sets the extra field `k = key.into()` to `v = value.into()`, replacing an earlier
value of `k`; every other key keeps its value, and the name and description are unchanged
(`self.extra.insert(key.into(), value.into())`, upstream lines 170–177, patched lines 172–179;
`serde_json::Map` is a `BTreeMap` in the translated configuration). The lookups hold for any entry
list of `self.extra` (the insertion is described at K09 cor.). If `self.extra` is sorted (as every
map built by K08 and K09 is), so is the result, and then the lookups determine it.

Premise: caller code. Not covered: (I), (P). -/
theorem Theorems.skill.SkillFrontmatter.with_field {KeyLike ValueLike : Type}
    (keyInto : core.convert.Into KeyLike String)
    (valueInto : core.convert.Into ValueLike serde_json.value.Value) (self : SkillFrontmatter)
    (key : KeyLike) (value : ValueLike) (k : String) (v : serde_json.value.Value)
    (h_key_into : keyInto.into key = ok k) (h_value_into : valueInto.into value = ok v) :
    rmcp.model.skill.SkillFrontmatter.with_field keyInto valueInto self key value ⦃
      (result : SkillFrontmatter) =>
      result.«name» = self.«name» ∧
      result.description = self.description ∧
      (KeysSorted self.extra → KeysSorted result.extra) ∧
      ∀ k', mapLookup result.extra k' = if k' = k then some v else mapLookup self.extra k' ⦄ :=
  rmcp.model.skill.SkillFrontmatter.with_field_spec keyInto valueInto self key value k v
    h_key_into h_value_into

/--
info: 'Theorems.skill.SkillFrontmatter.with_field' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.SkillFrontmatter.with_field

/-- K09, corollary: the entries of `extra` are `ExtModel.mapInsert k v self.extra.entries`, the
trusted model of `BTreeMap::insert`, for any entry list. `ExtModel.mapInsert k v` walks the
entries while their key differs from `k` and is not greater than it (in the byte order of
`KeysSorted`); at the entry where it stops it replaces the value if that key is `k`, and otherwise
inserts `(k, v)` before that entry (at the end if it reaches the end). So `(k, v)` precedes every
other entry with key `k`, and every other key keeps its first entry. On a sorted list this is the
`BTreeMap` insertion.

Premise: caller code. Not covered: (I), (P). -/
theorem Theorems.skill.SkillFrontmatter.with_field_extra_entries_eq_mapInsert
    {KeyLike ValueLike : Type}
    (keyInto : core.convert.Into KeyLike String)
    (valueInto : core.convert.Into ValueLike serde_json.value.Value) (self : SkillFrontmatter)
    (key : KeyLike) (value : ValueLike) (k : String) (v : serde_json.value.Value)
    (h_key_into : keyInto.into key = ok k) (h_value_into : valueInto.into value = ok v) :
    rmcp.model.skill.SkillFrontmatter.with_field keyInto valueInto self key value ⦃
      (result : SkillFrontmatter) =>
      result.«name» = self.«name» ∧
      result.description = self.description ∧
      result.extra.entries = (ExtModel.mapInsert k v self.extra.entries).2 ⦄ :=
  rmcp.model.skill.SkillFrontmatter.with_field_extra_entries_eq_mapInsert keyInto valueInto self
    key value k v h_key_into h_value_into

/--
info: 'Theorems.skill.SkillFrontmatter.with_field_extra_entries_eq_mapInsert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.SkillFrontmatter.with_field_extra_entries_eq_mapInsert

/-! ## K10–K13: `Skill` -/

/-- K10 `Skill::new`: the skill with URI `u = uri.into()`, the given frontmatter and resources,
and no `_meta`, unchecked (upstream lines 247–258, patched lines 249–260). It fixes all four fields
of `Skill`.

Premise: caller code. Not covered: (I). -/
theorem Theorems.skill.Skill.new {UriLike : Type} (uriInto : core.convert.Into UriLike String)
    (uri : UriLike) (frontmatter : SkillFrontmatter) (resources : SkillResources) (u : String)
    (h_uri_into : uriInto.into uri = ok u) :
    rmcp.model.skill.Skill.new uriInto uri frontmatter resources ⦃ (result : Skill) =>
      result.uri = u ∧
      result.frontmatter = frontmatter ∧
      result.resources = resources ∧
      result.«meta» = none ⦄ :=
  rmcp.model.skill.Skill.new_spec uriInto uri frontmatter resources u h_uri_into

/--
info: 'Theorems.skill.Skill.new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.Skill.new

/-- K11 `Skill::with_meta`: sets `_meta` to `Some(meta)`; the other fields are unchanged
(upstream lines 260–263, patched lines 262–265). So of two calls the last one wins, and `validate`
does not see the change (`Skill.validate_with_meta`). -/
theorem Theorems.skill.Skill.with_meta (self : Skill) (m : rmcp.model.meta.MetaObject) :
    rmcp.model.skill.Skill.with_meta self m ⦃ (result : Skill) =>
      result.uri = self.uri ∧
      result.frontmatter = self.frontmatter ∧
      result.resources = self.resources ∧
      result.«meta» = some m ⦄ :=
  rmcp.model.skill.Skill.with_meta_spec self m

/--
info: 'Theorems.skill.Skill.with_meta' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.Skill.with_meta

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

/-! ## K14–K16: free functions -/

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

/-- K16 `validate_skills`: returns `validateSkillsResult skills` (`Defs.Skill`): walking the
skills in order, the `validate` error (K13) of the first skill that does not validate, or
`DuplicateSkill(uri)` for the first skill whose percent-normalised URI (`skillKey`) an earlier
skill has, whichever comes first; `Ok(())` if neither occurs (upstream lines 424–433; patched
lines 488–497, hunk H8). For a skill that both fails `validate` and repeats an earlier skill's
key, the `validate` error is returned: `skill.validate()?` comes before the duplicate check
(upstream line 427 before 428, patched line 491 before 492).

Premises, for every skill: (V), (N), (U). These premises are sufficient, not exact: Rust only
reaches the skills up to the first fault (and their files up to the first faulty file), and every
value held in memory meets them. Not covered: (H), for each skill validated. -/
theorem Theorems.skill.validate_skills (skills : Slice Skill)
    (h_sizes : ∀ s ∈ skills.val, SkillFits s ∧ UriFits s.uri)
    (h_nfkc : ∀ s ∈ skills.val, NfkcFits s) :
    rmcp.model.skill.validate_skills skills ⦃
      (result : core.result.Result Unit SkillValidationError) =>
      result = validateSkillsResult skills.val ⦄ :=
  rmcp.model.skill.validate_skills_spec skills h_sizes h_nfkc

/--
info: 'Theorems.skill.validate_skills' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.validate_skills

/-- K16, corollary: `validate_skills` returns `Ok(())` exactly when every skill is valid
(`ValidSkill`, as K13's corollary) and the percent-normalised URIs are pairwise distinct
(`ValidSkills`).

Premises as K16. Not covered: (H), for each skill validated. -/
theorem Theorems.skill.validate_skills_eq_ok_iff (skills : Slice Skill)
    (h_sizes : ∀ s ∈ skills.val, SkillFits s ∧ UriFits s.uri)
    (h_nfkc : ∀ s ∈ skills.val, NfkcFits s) :
    rmcp.model.skill.validate_skills skills ⦃
      (result : core.result.Result Unit SkillValidationError) =>
      (result = .Ok () ↔ ValidSkills skills.val) ⦄ :=
  rmcp.model.skill.validate_skills_eq_ok_iff skills h_sizes h_nfkc

/--
info: 'Theorems.skill.validate_skills_eq_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.validate_skills_eq_ok_iff

/-! ## K17–K20: `GetSkillResult` -/

/-- K17 `GetSkillResult::new`: the result for `skill`, marked complete
(`result_type: Some(ResultType::COMPLETE)`, the borrowed string `"complete"`, `model.rs` line 1033
upstream, 1035 patched), with no TTL, no cache scope and no `_meta` (upstream lines 488–496,
patched lines 552–560). It fixes all five fields; K18–K20 each set one of them and keep the
others, so they commute with each other, and of two calls of the same one the last wins. -/
theorem Theorems.skill.GetSkillResult.new (skill : Skill) :
    rmcp.model.skill.GetSkillResult.new skill ⦃ (result : GetSkillResult) =>
      result.result_type = some rmcp.model.ResultType.COMPLETE ∧
      result.ttl_ms = none ∧
      result.cache_scope = none ∧
      result.skill = skill ∧
      result.«meta» = none ⦄ :=
  rmcp.model.skill.GetSkillResult.new_spec skill

/--
info: 'Theorems.skill.GetSkillResult.new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.GetSkillResult.new

/-- K18 `GetSkillResult::with_ttl_ms`: sets `ttl_ms` to `Some(ttl_ms)`; the other fields are
unchanged (upstream lines 498–501, patched lines 562–565). It commutes with K19 and K20; of two
calls the last wins. -/
theorem Theorems.skill.GetSkillResult.with_ttl_ms (self : GetSkillResult) (ttl_ms : U64) :
    rmcp.model.skill.GetSkillResult.with_ttl_ms self ttl_ms ⦃ (result : GetSkillResult) =>
      result.result_type = self.result_type ∧
      result.ttl_ms = some ttl_ms ∧
      result.cache_scope = self.cache_scope ∧
      result.skill = self.skill ∧
      result.«meta» = self.«meta» ⦄ :=
  rmcp.model.skill.GetSkillResult.with_ttl_ms_spec self ttl_ms

/--
info: 'Theorems.skill.GetSkillResult.with_ttl_ms' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.GetSkillResult.with_ttl_ms

/-- K19 `GetSkillResult::with_cache_scope`: sets `cache_scope` to `Some(cache_scope)`; the other
fields are unchanged (upstream lines 503–506, patched lines 567–570). It commutes with K18 and
K20; of two calls the last wins. -/
theorem Theorems.skill.GetSkillResult.with_cache_scope (self : GetSkillResult)
    (cache_scope : rmcp.model.CacheScope) :
    rmcp.model.skill.GetSkillResult.with_cache_scope self cache_scope ⦃
      (result : GetSkillResult) =>
      result.result_type = self.result_type ∧
      result.ttl_ms = self.ttl_ms ∧
      result.cache_scope = some cache_scope ∧
      result.skill = self.skill ∧
      result.«meta» = self.«meta» ⦄ :=
  rmcp.model.skill.GetSkillResult.with_cache_scope_spec self cache_scope

/--
info: 'Theorems.skill.GetSkillResult.with_cache_scope' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.GetSkillResult.with_cache_scope

/-- K20 `GetSkillResult::with_meta`: sets `_meta` to `Some(meta)`; the other fields are unchanged
(upstream lines 508–511, patched lines 572–575). It commutes with K18 and K19; of two calls the
last wins. -/
theorem Theorems.skill.GetSkillResult.with_meta (self : GetSkillResult)
    (m : rmcp.model.meta.MetaObject) :
    rmcp.model.skill.GetSkillResult.with_meta self m ⦃ (result : GetSkillResult) =>
      result.result_type = self.result_type ∧
      result.ttl_ms = self.ttl_ms ∧
      result.cache_scope = self.cache_scope ∧
      result.skill = self.skill ∧
      result.«meta» = some m ⦄ :=
  rmcp.model.skill.GetSkillResult.with_meta_spec self m

/--
info: 'Theorems.skill.GetSkillResult.with_meta' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.GetSkillResult.with_meta

/-! ## Compositions -/

/-- K05+K06, **an entry made from bytes verifies them**: `from_bytes` succeeds and `verify` of the
entry on the same bytes returns `Ok(())`.

Premise: caller code (the URI conversion). Not covered: (I), (S). -/
theorem Theorems.skill.SkillResource.verify_from_bytes_self {UriLike : Type}
    (uriInto : core.convert.Into UriLike String) (uri : UriLike) (bytes : Slice U8) (u : String)
    (h_uri_into : uriInto.into uri = ok u) :
    rmcp.model.skill.SkillResource.from_bytes uriInto uri bytes ⦃ (entry : SkillResource) =>
      rmcp.model.skill.SkillResource.verify entry bytes ⦃
        (result : core.result.Result Unit SkillIntegrityError) =>
        result = .Ok () ⦄ ⦄ :=
  rmcp.model.skill.SkillResource.verify_from_bytes_self uriInto uri bytes u h_uri_into

/--
info: 'Theorems.skill.SkillResource.verify_from_bytes_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.SkillResource.verify_from_bytes_self

/-- K05+K06, **verifying other bytes against an entry made from `bytes`**: `Ok(())` exactly when
`other` has the same length and the same SHA-256 digest (`ExtModel.sha256`, unopened; the
formatting `sha256Digest` is injective on 32-byte digests); `Size` with the two lengths exactly
when the lengths differ; otherwise, when the SHA-256 digests differ, `Digest` with the two
formatted digests. Equal digests of different bytes are not excluded (no collision freedom is
assumed).

Premise: caller code. Not covered: (I), (S). -/
theorem Theorems.skill.SkillResource.verify_from_bytes {UriLike : Type}
    (uriInto : core.convert.Into UriLike String) (uri : UriLike) (bytes other : Slice U8)
    (u : String) (h_uri_into : uriInto.into uri = ok u) :
    rmcp.model.skill.SkillResource.from_bytes uriInto uri bytes ⦃ (entry : SkillResource) =>
      rmcp.model.skill.SkillResource.verify entry other ⦃
        (result : core.result.Result Unit SkillIntegrityError) =>
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
            expected = sha256Digest bytes.val ∧ actual = sha256Digest other.val ⦄ ⦄ :=
  rmcp.model.skill.SkillResource.verify_from_bytes uriInto uri bytes other u h_uri_into

/--
info: 'Theorems.skill.SkillResource.verify_from_bytes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.SkillResource.verify_from_bytes

/-- K05 (K07), **`from_bytes` is `new` with the computed digest and length**: for any `U64`
`size` of value `bytes.len()`, `from_bytes uri bytes` is the computation that converts `uri`
(`uri.into()`) and returns the entry with that URI, the digest `sha256Digest bytes` and size
`size`; this is `SkillResource::new(uri, sha256_digest(bytes), bytes.len() as u64)` (upstream
and patched lines 85–87; the construction of K04) with the digest conversion `String → String`
the identity. An equality of computations: it holds whatever the caller's conversion does (both
sides call it once, on `uri`), so it has no caller-code premise.

Not covered: (S). -/
theorem Theorems.skill.SkillResource.from_bytes_eq {UriLike : Type}
    (uriInto : core.convert.Into UriLike String) (uri : UriLike) (bytes : Slice U8)
    (size : U64) (h_size : size.val = bytes.val.length) :
    rmcp.model.skill.SkillResource.from_bytes uriInto uri bytes =
      (do
        let u ← uriInto.into uri
        ok ({ uri := u, digest := sha256Digest bytes.val, size := size } : SkillResource)) :=
  rmcp.model.skill.SkillResource.from_bytes_eq uriInto uri bytes size h_size

/--
info: 'Theorems.skill.SkillResource.from_bytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.SkillResource.from_bytes_eq

/-- K05 (model), **an entry made from bytes has a well-formed digest**: the digest of the entry
that `from_bytes` returns passes `isSha256Digest`, so `validate` never reports `MalformedDigest`
for it (`firstFileFault_ne_malformedDigest`).

Premise: caller code. Not covered: (I), (S). -/
theorem Theorems.skill.SkillResource.isSha256Digest_from_bytes {UriLike : Type}
    (uriInto : core.convert.Into UriLike String) (uri : UriLike) (bytes : Slice U8) (u : String)
    (h_uri_into : uriInto.into uri = ok u) :
    rmcp.model.skill.SkillResource.from_bytes uriInto uri bytes ⦃ (entry : SkillResource) =>
      isSha256Digest (utf8Bytes entry.digest) = true ⦄ :=
  rmcp.model.skill.SkillResource.isSha256Digest_from_bytes uriInto uri bytes u h_uri_into

/--
info: 'Theorems.skill.SkillResource.isSha256Digest_from_bytes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.SkillResource.isSha256Digest_from_bytes

/-- K06 cor., **when `verify` succeeds**: `Ok(())` exactly when `bytes` has the promised length
and its digest `sha256Digest bytes` is the promised one.

No premise. Not covered: (S). -/
theorem Theorems.skill.SkillResource.verify_eq_ok_iff (self : SkillResource) (bytes : Slice U8) :
    rmcp.model.skill.SkillResource.verify self bytes ⦃
      (result : core.result.Result Unit SkillIntegrityError) =>
      (result = .Ok () ↔
        bytes.val.length = self.size.val ∧ sha256Digest bytes.val = self.digest) ⦄ :=
  rmcp.model.skill.SkillResource.verify_eq_ok_iff self bytes

/--
info: 'Theorems.skill.SkillResource.verify_eq_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.skill.SkillResource.verify_eq_ok_iff

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
