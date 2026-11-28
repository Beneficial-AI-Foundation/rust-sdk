/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Defs
public import Rmcp.Funs
import Proofs.Model.Skill.Basic
import Proofs.Model.Skill.Verify
import Proofs.Model.Skill.Model
import Proofs.Model.Skill.Validate

@[expose] public section

/-!
# Public API of `crates/rmcp/src/model/skill.rs`: top-level functions

This file states only the **top-level** public functions of `skill.rs`: those that no other
verified function calls (human decision 2026-11-28). The six public functions that a top-level
one calls are verified too: K04 `SkillResource::new` and K07 `sha256_digest` (called by K05
`from_bytes`; K07 also by K06 `verify`), K13 `Skill::validate` (called by K16 `validate_skills`)
and K12 `Skill::name`, K14 `skill_name_from_uri`, K15 `is_sha256_digest` (called by K13). Their
statements, the compositions that involve them, and the consequences of the model `Defs.Skill`
(statements with no Rust call, including the bridge lemma for (N)) are in
`formal/proofs/Proofs/Internal/Model/Skill.lean`. The theorem docstrings below are unchanged
signed-off text: where one names K04, K07, K12–K15, K13's corollary, `Skill.validate_with_meta` or
`firstFileFault_ne_malformedDigest`, that statement is in the internal file.

One row per theorem below; the theorem is `Theorems.skill.<Theorem>`. In the ID column, `Kxx cor.`
is a corollary of one spec theorem (K06 cor., K09 cor., K16 cor.); a composition is labelled by
the spec theorems it uses (`K05+K06`; `K05 (K07)` for `from_bytes` described with the digest of
K07; `K05 (model)` for `from_bytes` combined with a consequence of the model). The keys of the
last two columns are explained in "Premises" and "Not covered" below; they are local to this file
and its internal companion (`Specs/Model/RequestState.lean` uses some of the same letters with
other meanings).

| ID | Function | Theorem | Guarantee | Premises (caller must ensure) | Not covered (Rust may panic or behave otherwise; the model does not) |
|---|---|---|---|---|---|
| K01 | `Resource::is_directory` | `Resource.is_directory` | `true` iff the MIME type is `Some("inode/directory")` | (Z) | none |
| K02 | `SkillsCapability::new` | `SkillsCapability.new` | `directory_read = false` | none | none |
| K03 | `SkillsCapability::with_directory_read` | `SkillsCapability.with_directory_read` | `directory_read = true` (its only field) | none | none |
| K05 | `SkillResource::from_bytes` | `SkillResource.from_bytes` | the converted URI, `sha256Digest bytes`, the byte length | caller code | (I), (S) |
| K06 | `SkillResource::verify` | `SkillResource.verify` | `Ok` iff length and digest match; else `Size` (length first), else `Digest`, with payloads | none | (S) |
| K08 | `SkillFrontmatter::new` | `SkillFrontmatter.new` | the converted name and description, no extra field | caller code | (I) |
| K09 | `SkillFrontmatter::with_field` | `SkillFrontmatter.with_field` | `extra` with `key ↦ value` set, other keys and fields unchanged; still sorted if it was | caller code | (I), (P) |
| K09 cor. | same | `SkillFrontmatter.with_field_extra_entries_eq_mapInsert` | `extra` is `ExtModel.mapInsert k v self.extra.entries` (the model of `BTreeMap::insert`) | caller code | (I), (P) |
| K10 | `Skill::new` | `Skill.new` | the converted URI, the frontmatter and resources given, no `_meta` | caller code | (I) |
| K11 | `Skill::with_meta` | `Skill.with_meta` | `_meta = Some(meta)`, other fields unchanged | none | none |
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

## What this file promises

`skill.rs` describes a skill (a directory of files served as resources): its `SKILL.md`
frontmatter, its manifest of files with their `sha256:` digests and sizes, and the result of
`skills/get`. For each of the fourteen top-level public functions, a statement below says that
the call, in the Lean model, terminates without panicking, and what it returns: the value built
(K02, K03, K05, K08–K11, K17–K20), the truth value computed (K01), or, for a `Result`, the `Ok`
case and every `Err` case with its payload in the Rust order of checks (K06, K16).
The `Result`-returning functions are stated by an expected result written in `Defs.Skill`
(`validateSkillsResult`) or by a `match result with` whose arms are in the Rust
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
except `NfkcFits.of_utf8ByteSize_le` (in the internal file), which takes the NFKC expansion bound as
an explicit premise in law (implication) form (review rule of `formal/README.md`, "Trusted base").

Translated functions are written in full (`rmcp.model.skill.…`), as a bare name would resolve to
a restated theorem. The keys of "Premises" and "Not covered" below also serve the statements in
`formal/proofs/Proofs/Internal/Model/Skill.lean` (K04, K07, K12–K15 and their compositions).

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
  hunks H2 and H4; evidence `formal/trusted/evidence/README.md`): the NFKC forms of the name and of
  the decoded URI segment, where `validate` computes them, have at most `isize::MAX / 4` characters.
  The patched copy collects them into a `Vec<char>` (`prim::nfkc`) and panics above that, the
  original streams them and does not. By the bridge lemma
  `Theorems.skill.NfkcFits.of_utf8ByteSize_le` (`formal/proofs/Proofs/Internal/Model/Skill.lean`) it
  follows from `72 * n ≤ isize::MAX` for the `n` UTF-8 bytes of the name and of the URI (so it
  excludes no name or URI of at most `2^56` bytes), given the law that NFKC expands a character
  sequence of length `m` to at most `18 * m` characters (the largest expansion is `U+FDFA`, 18
  characters), which the caller supplies as a premise.
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
2026-11-24): of the twenty public functions K01–K20 (human decision of 2026-11-25), the fourteen
top-level ones (K01–K03, K05, K06, K08–K11, K16–K20; human decision 2026-11-28), with their
corollaries and the compositions of top-level functions. The intermediate K04, K07, K12–K15,
their corollary and compositions, and the consequences of the model `Defs.Skill` are in
`formal/proofs/Proofs/Internal/Model/Skill.lean`.

*Order.* The top-level functions are in Rust source order (= ID order), each corollary after its
statement; then the compositions.

*Proofs.* Each statement is restated as a theorem `Theorems.skill.<Type>.<function>` (free functions
`Theorems.skill.<function>`; corollaries and compositions keep the descriptive name of their proof),
proved by its spec theorem in `Proofs/Model/Skill/{Basic,Verify,Model,Validate}.lean` (with the
helpers of `Common` and `ValidateHelpers`), and followed by the assumptions its proof depends on,
checked by `#print axioms` under `#guard_msgs`. The restated text is that of the signed-off
statements (function names written in full).

*Sign-off.* The 51 statements (21 here, 30 in the internal file): signed off by the spec owner
(Hoang Le Truong) on 2026-11-25 (the signed-off statements are the ones in this file and in
`formal/proofs/Proofs/Internal/Model/Skill.lean`). Translation stage (patch 04 and its external
models): signed off on 2026-11-25. Incorporation approved by the human on 2026-11-25.

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

/-! ## K05, K06: `SkillResource` -/

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

/-! ## K10, K11: `Skill` -/

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

/-! ## K16: `validate_skills` -/

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
