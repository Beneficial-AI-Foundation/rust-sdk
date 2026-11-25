# MCP SDK Verification — Status

Plan: [`docs/MCP_SDK_Verification_Master_Plan_EN.md`][plan].
Task state: [`board.yaml`](board.yaml) (authoritative). Per-function records:
[`functions/`](functions/). Step evidence: [`evidence/`](evidence/); this report's evidence:
the S19 evidence (git history at 223ff12).

Phase 2 results: see "Phase 2" → "Phase 2 results (S37, 2026-11-24)".

**Translation patch 03 v2 (2026-11-24, reviewed and signed off 2026-11-24; specs pending):** R09–R15 of the public
`request_state.rs` API translate on the upgraded toolchain; see "Public
request_state.rs API" and "Trusted base". **R09–R15 specifications (2026-11-25):** 12 statements
signed off by the spec owner after 4 review rounds; Lean statements, proofs and
records incorporated; proofs checked 2026-11-25 (build, guards, independent incorporation review);
committed `0cbd67f`; accepted by the human owner 2026-11-25 (board SPEC-R09-R15).

**Aeneas upgrade (2026-11-24), reviewed and re-signed by the spec owner 2026-11-24:** see "Aeneas upgrade
(2026-11-24)" below. The results sections below record the state before it (Aeneas
`nightly-2026.08.20-5d08da4`, 35 native-code axioms); "Trusted base" is updated to the current state.

Last updated 2026-11-23: S19 final status report, written at local commit `aacfbf7` (branch
`docs/verification-guides`, not pushed). S19 was accepted by the human owner on 2026-11-23 (`board.yaml`).
Updated 2026-11-23 for the D2 fallback (human decision 2026-11-23): the SDK `*.rs` files are
byte-identical to upstream `origin/main` (`7caec76`); the `request_state_wire` refactor and all
added tests are translation patch `formal/trusted/patches/01-request-state-wire.patch`, applied
only to the translated copy; every Phase 1 target's (W/E) linkage is `patch-01` (proved on upstream
`7caec76` plus translation patch 01). The translation and all 25 proofs are unchanged.

Board at this report: S05–S16 and S18 `ACCEPTED` (human approval 2026-11-23); S02 and S04
`ACCEPTED` (human approval 2026-11-24); S01, S03 and S04a `IN_PROGRESS`, accepted by the owner on
2026-11-24 and waiting only for H5 (S01) or the first CI runs (S03, S04a); S17 `NOT_STARTED` (needs a push to
GitHub); S19 is this report.

Updated 2026-11-23 for **Phase 2** (plan Part II, Sections 13–25): S20 started; human decisions
H1–H4 accepted, H5 (owner and budget) open; 25 Phase 2 records added; board tasks S20–S37 added.
See "Phase 2" below. Nothing about the Phase 1 results changes.

## Aeneas upgrade (2026-11-24)

**State: reviewed and re-signed by the spec owner 2026-11-24.** Human decision 2026-11-24 ("option 1: full
migration"); base `d61356a`, branch `upgrade/aeneas-fb44cb4`, committed as `deb8d84`. Decisions:
lead N1–N15, human A1, A2 and the axiom-list, restatement, guard-exemption and module decisions
below. Nothing here changes a signed-off statement except the forced restatements listed.

**Toolchain.**

| Component | Before (until 2026-11-24) | After |
|---|---|---|
| Aeneas | `nightly-2026.08.20-5d08da4` | `nightly-2026.11.24-fb44cb4` (commit `fb44cb40`) |
| Charon | `0.1.235` | `0.1.324` |
| Lean / Mathlib | `v4.31.0` / `v4.31.0` | `v4.36.0` / `v4.36.0` (`fc4f59e5`) |
| Rust | `nightly-2026-06-01` | `nightly-2026-09-17` (`1.100.0-nightly`, commit date 2026-09-16) |

**Trust-base changes.**
- **0 native-code axioms** (was 35: 5 Phase 1, 30 Phase 2): the new `toStr` proves the length
  side condition of a literal in the kernel; `formal/trusted/native-axioms.lock` is emptied (lead
  decision N5, a shrink). Open problem 8 ("Bugs found") is resolved.
- **`core.fmt.Formatter` is no longer an axiom** of the Aeneas library (it is an `opaque` type).
  No target used it; re-adding the excluded items it blocked (B19, derived `Debug`) is a separate
  step after the migration (N15).
- **Four models moved into the Aeneas library** and were removed from
  `formal/trusted/Rmcp/FunsExternal.lean`: `Borrow::borrow` (blanket; now
  `Aeneas.Std.core.borrow.Borrow`), `Option::ok_or`, `Result::map_err`, `Vec::is_empty` (lead
  decision N8; the records and "Trusted base" are updated).
- **`RangeInclusive::contains` model changed** to the `nightly-2026-09-17` behaviour (human
  decisions A2, 2026-11-24): an exhausted range has end bound `Excluded(start)`, so it contains
  nothing (until then: `item < end` for an exhausted range). The laws `contains_u8_spec` and
  `contains_eq_match_le` (and their `Theorems.External.*` restatements) were false under the new
  model (counterexample: `1..=5` exhausted, item 2) and were restated exactly (exhausted branch
  `item < start`); `new_contains_u8_spec` is unchanged. A02 applies `contains_u8_spec` to a
  freshly built range (not exhausted), so its statement is unaffected. **Review done** (one fresh reviewer, model and laws, 2026-11-24): the
  model is exact; one blocking finding (the `Theorems.External…new_contains_u8_spec` restatement
  had been dropped in a merge) was fixed by restoring it, and one docstring citation was fixed.
  `formal/trusted/evidence/README.md` marks the old spot check as run on `nightly-2026-06-01`
  only and records two vectors that separate the old and new model, verified on
  `nightly-2026-09-17`.
  Re-sign-off of the two laws in the batch below.
- **All 39 model citations** are to be re-checked against the `nightly-2026-09-17` `rust-src`
  (lead decision N9, model review; `FunsExternal.lean` already cites the new line numbers).
- **Two exact guard exemptions** (human decision 2026-11-24, pinned in `scripts/lean_guard.py` with
  self-tests): the Aeneas phrase "this code is generated from a macro invocation at:" in generated
  docstrings (the macro-site path is checked against the allowed sources, N13), and exactly one
  `set_option linter.dupNamespace false in` on `zeroize.Zeroize.Blanket.zeroize` in
  `trusted/Rmcp/FunsExternal.lean`.
- **Charon settings check (N1)**: Charon `0.1.324` no longer records its options in the LLBC
  (`translated.options`); `scripts/aeneas-translate.sh` checks the preset and overflow checks in
  the LLBC and that `exclude`, `opaque` and `start_from` were applied on the translated items
  (`translation.json`). Both cargo build-script output layouts are accepted (N2).
- **Lean modules (N12)**: the project Lean files are converted to the module system (header and
  visibility only, no statement change); the Defs rename is mechanical (N14). One accepted
  construct of the module system: `import all Aeneas.Std.Scalar.SaturatingOps` in
  `Proofs/Transport/ClientSideSse.lean` (the saturating-add lemmas it needs are private in the
  library module); the axiom audit and the kernel replay run at the private level, so it changes
  nothing in the trust base. The axiom audit's
  kernel replay uses `Lean.Kernel.Environment.replay` (N11).

**`#print axioms` lists** (re-sign table, generated mechanically against `d61356a`; one-time
exception, human decision 2026-11-24: lists may gain only `propext`, `Classical.choice`,
`Quot.sound`, re-signed as one batch; shrink-only again afterwards): 194 blocks before and after,
**110 unchanged, 84 changed, 0 added, 0 removed**. Of the 84: 66 only gain standard axioms, 18
only lose `_native` axioms; **no exception** (no other axiom added, no non-native axiom removed).
Every list is now within `[propext, Classical.choice, Quot.sound]` (75 of the changed lists are
exactly these three, 9 are `[propext, Quot.sound]`). By file: `Proofs/Internal/External.lean` 46,
`Specs/Model.lean` 13, `Proofs/Internal/Model/RequestState.lean` 10,
`Specs/Model/RequestState.lean` 8, `Proofs/Internal/Transport/AsyncRw.lean` 3,
`…/StreamableHttpServer/Tower.lean` 2, `…/Common/ClientSideSse.lean` 1, `Specs/Model/Task.lean` 1.
Function records: 28 of 58 `axioms` fields changed (`formal/docs/functions/*.yaml`, each with a
note).

**Statement changes** (theorem/lemma signatures, proofs ignored; 520 unchanged, 14 changed, none
added or removed): N7 forced restatements, name-only batch re-sign (human decision 2026-11-24):
`alloc.vec.Vec.is_empty_spec` (no allocator argument), `String…CoreHashHash.hash_eq` (`Slice.from`
instead of the anonymous constructor), `HashMap.get_eq`, `HashMap.get_string_spec` and the helper
`Proofs.External.HashMap.find_string` (`Aeneas.Std.core.borrow.Borrow`), with their
`Theorems.External.*` restatements; the RangeInclusive laws `contains_u8_spec`,
`contains_eq_match_le` and restatements (above). Also named explicitly: the helper lemma `Proofs.ClientSideSse.from_residual_eq` (proof file, no
record, no `#print axioms`) names a translated instance renamed by the new Charon/Aeneas
(`CoreOpsTryTraitFromResidualResultInfallible` → `CoreOpsTry_traitFromResidualResult`; the
upgrade reviewer confirmed the same Rust impl with the same body). **Definition change** (`Defs`,
112 declarations unchanged, 1 changed): `Defs.CodecState.KeyTable`, allocator argument `Global` →
`alloc.alloc.Global` (the Aeneas library's name; name-only, N7/N14).
A `Theorems.External…new_contains_u8_spec` restatement dropped in a merge was restored by the lead
(statement unchanged).

**Build and guards** (working tree, 2026-11-24): `lake build --wfail` exit 0 (3767 jobs, no warning);
`lean-guard.sh axioms` exit 0 (3908 constants in 76 project modules; 0 trusted, 0 native-code
axioms; kernel replay of 3883 constants accepted, 25 unsafe/partial skipped); `aeneas-archive`
and `build-log` pass; `sources` fails only on the four stale entries of
`formal/trusted/translation-pins.txt` (lines 29 and 157 of `Funs.lean`, 134 of
`FunsExternal_Template.lean`, 199 of `Types.lean`), which the human edits by hand (A1).

**Reviews and sign-off.** Round 1: two independent reviewers (trust base and tooling; statements,
axiom lists, proofs and records); every finding fixed, including the blocking one (stale
`rust-src` citations in `trusted/Rmcp/`; the N9 citation re-check is now a full mechanical sweep,
no model behaviour changed except `RangeInclusive::contains`). Round 2: a fresh reviewer
re-checked every round-1 finding (all fixed, no regression). The RangeInclusive model and laws
had their own review (above). **Human batch re-sign-off, spec owner Hoang Le Truong,
2026-11-24:** the 84 changed `#print axioms` lists, the 9 forced restatements, the 4
RangeInclusive laws, the `Defs.CodecState.KeyTable` rename, the `from_residual_eq` helper rename
and the `RangeInclusive::contains` model (re-sign table, recorded in the run log).

**Pending:** the `translation-pins.txt` edit (human; until then `lean-guard.sh sources` fails on
its 4 stale entries); a clean `aeneas-archive` run (stale `*.trace.nobuild` files written by an
editor Lean server still on v4.31); the commit (human approval); patch 03 (R09–R12), parked in
`stash@{0}`, resumed after the commit; re-adding excluded items as separate steps (N15); CI on
GitHub. (Update 2026-11-24, after the upgrade commit `deb8d84`: patch 03 was redone on the new
toolchain as patch 03 v2, targets R09–R15, human decision; the parked `stash@{0}` version is
superseded and kept until the new one is committed. See "Public request_state.rs API".)

## Results

Plan Section 11 template, filled with the actual results. Three deviations from the template's
wording, each forced by a recorded fact: the verified code is upstream `origin/main` plus a
translation patch, not the unmodified upstream files (D2 fallback, human decision 2026-11-23); the
external contracts are models (definitions, structures and `opaque` constants), not axioms (human
decision 2026-11-23); five native-code axioms are added to the trusted base (Phase 1; Phase 2 adds
30 more, see "Trusted base"). No target is open, so
the last sentence names the excluded functions and non-targets instead.

> At upstream SDK commit `7caec762799bece6fba38e4298b8ca7db8bac12c` (`origin/main`) **with the
> translation patch `formal/trusted/patches/01-request-state-wire.patch` applied** (D2 fallback,
> human decision 2026-11-23: the `request_state_wire` refactor exists only in the patched copy
> `.llbc/work/`; the SDK `*.rs` files in the repository are byte-identical to `7caec76`), translated
> for `x86_64-unknown-linux-gnu` with `--no-default-features --features request-state` [Phase 1
> record; the committed translation now uses the widened Phase 2 feature list, under which the
> Phase 1 output is byte-identical (S21, S23)] (and the
> Charon settings in `crates/rmcp/Cargo.toml`), the following request-state wire functions (public
> in the patched copy) and existing codec functions are checked against the Aeneas translation of
> the patched copy (`nightly-2026.08.20-5d08da4`): W01 `b64_len`, W02 `key_length_ok`, W03
> `check_kid_len`, W04 `bytes_eq`, W05 `next_dot`, W06 `component_count`, W07 `version_of`, W08
> `parse_rs1`, W09 `parse_rs2`, W10 `transcript_v1`, W11 `transcript_v2`, W12 `decode_expiry`, W13
> `is_expired`, W14 `open_frame`, W15 `frame` (module `request_state_wire`); E01
> `open_authenticated_body`, E02 `b64_len`, E03 `validate_key_length`, E04 `validate_config_kid`,
> E07 `seal_rs1`, E08 `seal_rs2`, E09 `open_rs1_at`, E09a `rs1_fallbacks_verify`, E10 `open_rs2_at`,
> E11 `open_at` (`RequestStateCodec`); and the composition theorems `frame_roundtrip`,
> `rs1_roundtrip`, `rs2_roundtrip`, `open_at_roundtrip_rs1`, `open_at_roundtrip_rs2`. The code
> verified is `7caec76` plus patch 01, not the unmodified upstream files. The link to upstream
> behaviour is the patch's byte-identity regression tests (`mod byte_identity` and the codec tests,
> run on the patched copy by `patched-tests.yml`) and the differential check of S04a (about 2.9M
> `open` calls, unrefactored vs refactored codec, no difference); that link is argued and tested,
> not proved. These results rest on the trusted base listed in `formal/README.md` and `STATUS.md`:
> Charon, Aeneas and Lean; the translated configuration; translation patch 01; the HMAC-SHA256,
> Base64url and standard-library models in `formal/trusted/` (definitions, structures and four
> `opaque` constants; no trusted axiom); the five Aeneas `toStr` native-code axioms (Phase 1; 35 with
> Phase 2) locked in
> `formal/trusted/native-axioms.lock`; the codec-state hypothesis; the statements in
> `formal/specs/`; and the exclusions. They do not establish cryptographic security, constant-time
> execution, or correctness of the public codec wrappers. No target is open; the functions not
> listed are excluded (Section 2.3, "Excluded functions" below) or are translatable non-targets
> (`open`, `open_with`, `new`, `try_new`).

**D10 count (plan Section 8, "Gates").** Of the 25 targets: **verified on original code 0**,
**proved with translation patch 01: 25**, **open 0**. "Proved with translation patch 01" means spec
`REVIEWED` (signed off by the spec owner), proof `CHECKED` and linkage `patch-01` in every record of
`functions/`, with the restated theorem in a spec file; each theorem holds under its stated premises
(no-overflow and size domains, codec-state clauses) and is about the patched copy. (Before the D2
fallback, this count read "verified 25" with linkage `ORIGINAL` relative to local commit `f8fb6a7`;
the proofs did not change.) If the refactor lands in the SDK source, patch 01 is deleted and the
targets can become `ORIGINAL`. Plus 5 composition theorems. Excluded (not counted, not verified):
the items under "Excluded functions" below. Not targets: 4 translatable wrappers (since 2026-11-24
specified and proved as R01–R08, with the `SealOptions` builder and `new_unchecked`; see "Public
request_state.rs API").

Restated theorems (`theorem Theorems.…`, each proved by the spec theorem it restates and guarded
by `#guard_msgs in` + `#print axioms`), counted at `aacfbf7` (historical paths: since 2026-11-24 the
W/E files and the model laws are in `formal/proofs/Proofs/Internal/`, and
`formal/specs/Specs/Model/RequestState.lean` holds R01–R08):

| Spec file | Theorems | Content |
|---|---|---|
| `formal/specs/Specs/Model/RequestStateWire.lean` | 16 | W01–W15, `frame_roundtrip` |
| `formal/specs/Specs/Model/RequestState.lean` | 14 | E01–E04, E07–E11, E09a, 4 round trips |
| `formal/specs/Specs/External.lean` | 72 | laws of the external models (S08–S09) |
| Total | 102 | |

## Source baseline

| Item | Value |
|---|---|
| Repository | https://github.com/truonghoangle/rust-sdk (fork of the Rust MCP SDK) |
| Base commit | `0e2396f73a88617141b31f645de6f1171ed5f993` |
| SHA-256 of `request_state.rs` at base | `41e69cad…b416` (full value: plan Section 1) |
| Pinned commit | upstream `origin/main` `7caec762799bece6fba38e4298b8ca7db8bac12c`; every SDK `*.rs` file is byte-identical to it (D2 fallback, 2026-11-23) |
| Translation patch | `formal/trusted/patches/01-request-state-wire.patch`: the refactor of local commit `f8fb6a7` plus the S16 tests of `afab9d2`, applied only to `.llbc/work/` by `scripts/apply-patches.sh` |
| Verified Rust source | the patched copy (`7caec76` + patch 01, plus the test-only patch 02 since 2026-11-24, which adds `#[cfg(test)]` code only); its non-test lines equal those of `f8fb6a7`, so line numbers are unchanged |
| Translation | committed at `9bd8144` (from `f8fb6a7` + Charon settings); reproduced byte for byte through the patch path (2026-11-23) |
| Aeneas | release tag `nightly-2026.11.24-fb44cb4` since the Aeneas upgrade of 2026-11-24 (reviewed and re-signed by the spec owner 2026-11-24); until then `nightly-2026.08.20-5d08da4` (the S03 evidence (git history at 223ff12)) |

`request_state.rs` at `7caec76` has the base SHA-256 above (unchanged since `0e2396f`).
History: SHA-256 of the target files at `f8fb6a7`: `request_state.rs` `a09f02e3…f076`,
`request_state_wire.rs` `96f433d7…c357`. Since then the files changed only by the S16 test
insertions inside `mod tests` (`afab9d2`; `git diff -U0 f8fb6a7 aacfbf7` shows two insertion-only
hunks, after line 735 resp. 280), and `crates/rmcp/Cargo.toml` only in comments and the
derived-`Debug` `exclude` entries (`9bd8144`, `af41799`). The committed translation was reproduced
byte for byte on a fresh clone at `a32553d` (the S18 evidence (git history at 223ff12)). Since
the D2 fallback these changes are in patch 01, and the files in the repository are upstream.

Target files, in the patched copy (both compile only with the `request-state` feature):
- `crates/rmcp/src/model/request_state_wire.rs` (new, public; created by patch 01, absent from
  the repository's sources)
- `crates/rmcp/src/model/request_state.rs` (upstream file, refactored onto it by patch 01)

## Translated configuration

Single target, fixed in `scripts/aeneas-translate.sh` (S03; feature list widened at S21 for Phase 2,
human decision H1; the Phase 1 output is byte-identical under it):

```
--target x86_64-unknown-linux-gnu --no-default-features
--features request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth --lib
--config profile.dev.overflow-checks=true --config profile.dev.debug-assertions=true
```

Charon settings: `[package.metadata.charon]` in `crates/rmcp/Cargo.toml` (`start_from`, `exclude`,
`opaque`), committed (they name `request_state_wire` and `rmcp::model::skill::prim`, which exist
only in the patched copy).
Dependency pins (`PINNED_DEPS`): `hmac 0.13.0`, `sha2 0.11.1`, `base64 0.23.1`, `digest 0.11.3`,
`zeroize 1.9.2`, `chrono 0.4.45`, `serde_json 1.0.154`, since translation patch 03 (2026-11-24,
signed off) `serde_core 1.0.229`, and since translation patch 04 (2026-11-25, signed off 2026-11-25)
`percent-encoding 2.3.2`, `unicode-normalization 0.1.26` and `unicode-general-category 1.1.0`,
checked since S21 on rmcp's own edges in the
translated configuration (human decision 2026-11-23; other versions used only by other crates,
e.g. `oauth2`'s `sha2 0.10.9`, are allowed). **Patches** (`formal/trusted/patches/`, applied in
file-name order to the copy in `.llbc/work/` only): translation patch
`01-request-state-wire.patch` (D2 fallback, 2026-11-23), the test-only patch
`02-phase2-tests.patch`, translation patch `03-request-state-public.patch` (signed off
2026-11-24) and translation patch `04-skill-public.patch` (2026-11-25, signed off by the spec owner
2026-11-25); see "Trusted base". **No hand edit**
of the generated files (`formal/translation/` is reproduced byte for byte by the translate script,
S18). The proofs hold only for this configuration.

## Scope decision (plan Section 1)

Aeneas handles pure, sequential, safe Rust well, and the request-state codec is mostly that:
framing, parsing, length checks and byte transcripts. The parts that are not (HMAC and Base64
crate internals, the system clock, `serde` JSON wrappers, formatting impls) are either behind
four opaque primitives with hand-written models (plan Section 4) or excluded (plan Section 2.3).

**Objective.** Implementation-linked correctness of the request-state codec — framing,
configuration checks, version dispatch, token parsing, MAC transcripts, expiry, and seal/open
round trip — under explicitly named models of HMAC-SHA256, Base64url and the standard-library
operations the code uses.

**Not claimed:**
- HMAC unforgeability or any other cryptographic security property;
- constant-time behaviour of the compiled code;
- correctness of the `hmac`, `sha2`, `base64` or `zeroize` crates;
- any excluded function (see "Excluded functions" below);
- the translatable public wrappers `open`, `open_with`, `new` and `try_new`, which are not
  targets;
- negative round trips (a tampered token or one sealed under another key is rejected; deferred
  at S15, see "Open items");
- any configuration other than the one above;
- full MCP protocol verification.

Claims apply to the commit, patch and configuration above only, not to upstream releases or to
the unpatched upstream files.

## Owners and budget

| Role | Name |
|---|---|
| Project owner | TBD — to be named by a human (blocks S01 acceptance and the D2 gate) |
| Spec owner(s) | Hoang Le Truong (named 2026-11-23; signed off all 25 statements, the 5 |
| | composition theorems, the codec-state predicate and the external models) |
| Budget (people, time, compute) | TBD — to be named by a human |

Only the named human spec owner may set `spec: REVIEWED`, and only a human may move a task to
`ACCEPTED` (plan Section 6).

## Per-function status

Mirrors `formal/docs/functions/*.yaml` (the records are authoritative), checked at `aacfbf7`:
every record has `translation: LEAN_OK`, `spec: REVIEWED`, `spec_owner: "Hoang Le Truong"`,
`linkage: patch-01` (patch 01, since 2026-11-23), `proof: CHECKED`.

| ID | Rust symbol | translation | spec | linkage | proof |
|---|---|---|---|---|---|
| W01 | `request_state_wire::b64_len` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| W02 | `request_state_wire::key_length_ok` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| W03 | `request_state_wire::check_kid_len` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| W04 | `request_state_wire::bytes_eq` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| W05 | `request_state_wire::next_dot` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| W06 | `request_state_wire::component_count` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| W07 | `request_state_wire::version_of` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| W08 | `request_state_wire::parse_rs1` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| W09 | `request_state_wire::parse_rs2` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| W10 | `request_state_wire::transcript_v1` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| W11 | `request_state_wire::transcript_v2` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| W12 | `request_state_wire::decode_expiry` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| W13 | `request_state_wire::is_expired` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| W14 | `request_state_wire::open_frame` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| W15 | `request_state_wire::frame` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| E01 | `RequestStateCodec::open_authenticated_body` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| E02 | `RequestStateCodec::b64_len` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| E03 | `RequestStateCodec::validate_key_length` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| E04 | `RequestStateCodec::validate_config_kid` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| E07 | `RequestStateCodec::seal_rs1` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| E08 | `RequestStateCodec::seal_rs2` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| E09 | `RequestStateCodec::open_rs1_at` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| E09a | `RequestStateCodec::rs1_fallbacks_verify` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| E10 | `RequestStateCodec::open_rs2_at` | LEAN_OK | REVIEWED | patch-01 | CHECKED |
| E11 | `RequestStateCodec::open_at` | LEAN_OK | REVIEWED | patch-01 | CHECKED |

Total: 25 records (W01–W15, E01–E04, E07–E11, E09a), all proved and restated in the spec
files, plus the composition theorems `frame_roundtrip` (S06) and `rs1_roundtrip`,
`rs2_roundtrip`, `open_at_roundtrip_rs1`, `open_at_roundtrip_rs2` (S15). Proofs:
`formal/proofs/Proofs/Model/`. Evidence: S06, S07, S10 (W and E01–E04), S13 (E07–E11, E09a,
codec state), S15 (round trips).

**E05 and E06 are unassigned.** They belonged to `mac_v1`/`mac_v2`, which the S04a refactor
deletes (plan Sections 2.2 and 2.3). The IDs are not renumbered and have no function record.

## Excluded functions (plan Section 2.3)

Excluded, not deferred: no function record, no specification, no proof. Each item except
`mac_v1`/`mac_v2` (deleted by the refactor) and `any_key_verifies` (never added) is in the
committed Charon `exclude` list of `crates/rmcp/Cargo.toml`, with its blocker in a comment. That
no target calls an excluded item was checked at S19: none of them is declared in the generated
`Funs.lean`/`Types.lean` or in `FunsExternal.lean` (text search; the only hit is a comment), and
every target has a generated body that the proofs use.

- `mac_v1`, `mac_v2` (were E05, E06): B1, HMAC types in the return type; deleted by the refactor,
  replaced by W10/W11 and `prim`.
- `any_key_verifies` (proposed wire function): B11, nested borrows in `&[&[u8]]`; never added.
- `seal_at`: B13, Aeneas "Unreachable" error on the TTL computation; `exclude`.
- `seal_with`, `seal`: call `seal_at`; `exclude`.
- `new_with_keyring`: B13, Aeneas internal error; `exclude`.
- `with_rs1_signing`, `with_rs1_fallback`: B4, "no bottoms in the value"; `exclude`.
- `Debug`/`Display` for `RequestStateError`, `Debug` for `RequestStateCodec`: B13, Aeneas type
  assertion and internal error; `exclude`.
- derived `Debug` for `KidError`, `Version`, `FrameError`, `Rs1Parts`, `Rs2Parts`, `SealMode`,
  `SealOptions`: not a blocker; they depended on `Aeneas.Std.core.fmt.Formatter` and native-code
  string axioms (until the Aeneas upgrade of 2026-11-24; since then `Formatter` is an `opaque`
  type of the Aeneas library and no native-code axiom is declared), and no target uses them
  (human decision 2026-11-22); `exclude`.
- `seal_json`, `seal_json_with`, `open_json`, `open_json_with`, `Error` for `RequestStateError`:
  B9, `serde` signatures, `Error::source` not modelled; `exclude`.
- crates `serde`, `serde_core` (crate level): B9; only the excluded JSON wrappers use them.

**Amendment (translation patch 03 v2, 2026-11-24, signed off by the spec owner).** On Aeneas
`nightly-2026.11.24-fb44cb4` the `exclude` entries of `seal_at`, `seal`, `seal_with`,
`new_with_keyring`, `with_rs1_signing`, `with_rs1_fallback`, `open_json` and `open_json_with`
are removed and these eight functions translate: `with_rs1_signing`, `with_rs1_fallback` and
`new_with_keyring` with no source change (B4 and the B13 internal error are gone on this
toolchain), `seal_at` (hence `seal`, `seal_with`) and `open_json*` with translation patch 03; the
crate `serde_core` moved from `exclude` to `opaque` (crate `serde` stays excluded). Still excluded:
`seal_json`, `seal_json_with` (B9 narrowed to these two: Aeneas does not support the mutually
recursive `serde_core::ser` traits; blocked upstream; once that is fixed they would additionally
need the variant-constructor workaround of patch 03 hunk 2, since
`.map_err(RequestStateError::Serialization)` hits "Arrow types are not supported yet" at
`request_state.rs` 133:4-133:46 / 461:4-468:5 of the patched copy), `Error` for `RequestStateError`, the
`Debug`/`Display` impls and the derived `Debug` impls above. The list above is the state before
2026-11-24.

Consequences (plan Section 2.3): the round-trip theorems compose E07/E08 with E09–E11
directly, with no seal wrapper verified; the codec-state invariant is permanently a hypothesis;
`open`, `open_with`, `new` and `try_new` translate but are not targets. (Since 2026-11-24 they and the `SealOptions` builder, `new_unchecked`, are being specified as
R01–R08, the public `request_state.rs` API; see "Public request_state.rs API".)

## Trusted base

Current state after the Aeneas upgrade of 2026-11-24 (reviewed and re-signed by the spec owner 2026-11-24; see
"Aeneas upgrade (2026-11-24)"): `scripts/lean-guard.sh axioms` exit 0 with 0 native-code axioms
on the working tree of branch `upgrade/aeneas-fb44cb4`. Before the upgrade: checked at `3ded001`
by `scripts/lean-guard.sh axioms` (exit 0; 4047 constants in 74 project
modules; kernel replay of 4038 constants accepted, 9 unsafe/partial skipped; S23 review
2026-11-24; first recorded at `aacfbf7` with 2110 constants in 46 modules):

- **Trusted axioms: 0.** `formal/trusted/axioms.lock` has no entry; the `RmcpExternal` roots
  declare no axiom (human decision 2026-11-23). Allowed builtins: `propext`, `Classical.choice`,
  `Quot.sound`.
- **Native-code axioms: 0** since the Aeneas upgrade of 2026-11-24 (lead decision N5):
  `formal/trusted/native-axioms.lock` is empty, because the `toStr` of
  `nightly-2026.11.24-fb44cb4` proves the length side condition of a literal in the kernel; the
  lock's rules stay in force for any native-code axiom that appears again. **Until then: 35**,
  all reached, used and locked in `formal/trusted/native-axioms.lock`
  (separate trust class, human decision 2026-11-22). Phase 1 (5): the Aeneas `toStr` side
  conditions of the string literals `VERSION_V1` ("rs1"), `VERSION_V2` ("rs2"), `KID_EMPTY_MSG`,
  `KID_TOO_LONG_MSG` and the `expect` message of `rs1_fallbacks_verify`. Phase 2 (30, human
  decision H2, locked 2026-11-24 at S29): the 18 request and 10 notification method-name literals
  of `async_rw.rs` (`is_standard_method` lines 399–416, `is_standard_notification` lines 423–432)
  and `"http"`/`"https"` of `tower.rs` `default_port` (lines 1148–1149), used by T05–T08 and C05. Each side condition
  also had a kernel proof; the Aeneas `toStr` of the upgrade uses it, which removed them.
- **External models** (accepted at S08/S09, human approval 2026-11-23; in use by the proofs): the
  41 placeholder externals of S04a part 2 are replaced by definitions (functions) and structures
  (types) with the generated names; what cannot be computed is one of exactly four `opaque`
  constants: `ExtModel.hmacSha256`, `ExtModel.sipHash13`, `ExtModel.nowMs`,
  `ExtModel.SerdeJsonErrorImpl` (Phase 1; S26/S27 add a fifth, see below; translation patch 03
  adds three more and turns `SerdeJsonErrorImpl` into a `def`, see "Translation patch 03 models"
  below). They add no axiom and do not appear in `#print axioms` or the
  locks: a change to a model is caught only by review of `formal/trusted/`. Their 72 laws are
  proved (`Proofs/External/`) and restated in `Specs/External.lean` (since 2026-11-24:
  `formal/proofs/Proofs/Internal/External.lean`).
- **Translation pin** (S21, human decision 2026-11-23): `formal/trusted/translation-pins.txt` records
  the sha256 of `formal/translation/Rmcp/Funs.lean` and the one line on which `lean-guard.sh sources`
  excuses a metaprogramming word (line 1971 before the Aeneas upgrade, the word `initialize`, the
  T06 literal; the entries are stale after the re-translation of 2026-11-24 and are being updated
  by the human by hand, decision A1). It is a trusted
  file: the guard cannot see lexical context, so a pin whose hash is updated together with an edited
  `Funs.lean` excuses whatever stands at the pinned line; only the byte-for-byte regeneration of
  `aeneas-translation.yml` and review (each pinned line read in context) catch that. A legitimate
  re-translation must update it in a reviewed PR.
- **Phase 2 external models** (S26/S27, 2026-11-23; reviewed, signed off by the spec owner,
  laws proved): the 26 S21 placeholders are definitions transcribed from `core`/`alloc` of
  nightly-2026-06-01 (the citations are re-checked against nightly-2026-09-17 in the model review
  of the Aeneas upgrade, lead decision N9; `RangeInclusive::contains` changed, see "Aeneas
  upgrade (2026-11-24)") (strings and `Arc`; `Option`, `Result`, slices, ranges; `i64::from_str`;
  `Ipv4Addr`/`Ipv6Addr` predicates), and 5 of the 6 placeholder types are structures or
  inductives (`Ipv4Addr` over 4 octets, `Ipv6Addr` over 8 segments where Rust stores 16 octets,
  `ParseIntError` with all six `IntErrorKind` variants, `Arc` holding its value, `MaybeUninit`);
  the sixth, `serde_json::Value`, is defined as the abstract `opaque` type
  `ExtModel.SerdeJsonValue` (Phase 2 targets only move values). Helpers: `ExtModel.IntErrorKind`,
  `decDigit?`, `i64DigitLoop`, `i64FromAscii`, `sliceEq`, `sliceEqSameLength`, `beNat`, `ipv4Nats`,
  `ipv6Nats`. Stated exceptions are in each docstring (e.g. `Arc` equality has no pointer fast
  path). 43 laws (AI-drafted; review round 1: two agents, no blocking finding; signed off by the spec
  owner 2026-11-23; proved and restated in `Specs/External.lean` (now `Proofs/Internal/External.lean`), axioms at most `propext`,
  `Classical.choice`, `Quot.sound`). Sources and evidence: `formal/trusted/evidence/README.md`; the
  differential tests of plan Section 18 were not built (stage 3 dropped by human decision,
  2026-11-23; plan Section 18 amendment), so fidelity rests on the cited source, review and the
  proved laws (stage 6).
- **Translation patch 03 models** (2026-11-24, human decisions: targets R09–R15, variant A;
  **reviewed in two rounds and signed off by the spec owner 2026-11-24**): the functions newly reached by `seal`/`seal_with`
  (through `seal_at`), `with_rs1_signing`, `with_rs1_fallback`, `open_json`/`open_json_with` and
  `new_with_keyring` need **14 function models** (`Duration::as_millis`, `str::to_owned`,
  `HashMap::{contains_key, is_empty, new, entry}`, `VacantEntry::insert`, `Hash for str`,
  `Borrow<str> for String`, `PartialEq<str> for String`, `slice::Iter::any`, `Iterator::any`
  (default), `serde_json::from_slice`, `Error::source` (default)) and **2 type models**
  (`OccupiedEntry`, `VacantEntry`), all definitions or structures, with the helpers
  `ExtModel.HashMap.lookupEntry` and `ExtModel.sliceIterAny`, and **three `opaque` constants**
  (no axiom):
  - `ExtModel.randomState : RandomState`, the hash keys `HashMap::new` stores (random per map in
    Rust). Review rule: no statement has a premise or conclusion about its value or about the
    `hash_builder` of a map built by `HashMap::new`, and none states or relies on the equality
    (or inequality) of maps or codecs built by distinct `HashMap::new` calls.
  - `ExtModel.serdeJsonFromSlice`, the outcome (`Ok` value or `Err`) of
    `serde_json::from_slice::<T>` for the caller's `Deserialize` instance. **Modelling decision**
    (human, 2026-11-24): `from_slice` is `ok` of this opaque outcome, because it depends on the
    caller's `Deserialize` impl and the `serde_json` parser, neither translated; stated
    exceptions: a `Deserialize` impl that panics, aborts or does not terminate, or that is
    non-deterministic or has side effects (global or thread-local state, a random number
    generator), is not modelled. Review rule: a statement may only say that the result of
    `open_json`/`open_json_with` is this outcome for the opened payload, mapped as the Rust code
    maps it, and no statement relates two calls of `open_json`/`open_json_with` (or of
    `from_slice`).
  - `ExtModel.SerdeJsonErrorImplCarrier : NonemptyType`; `ExtModel.SerdeJsonErrorImpl` is now
    `def … := Carrier.type` (abstract, no longer itself `opaque`), with `Nonempty` instances for
    it and for `serde_json::Error`, so that the opaque outcome can be an `Err` (human decision
    2026-11-24). Still never inspected.
  With patch 03 the total was 7 `opaque` constants (`hmacSha256`, `sipHash13`, `nowMs`,
  `SerdeJsonValue`, `randomState`, `serdeJsonFromSlice`, `SerdeJsonErrorImplCarrier`); sources
  and tests per model: `formal/trusted/evidence/README.md`, "Public `request_state.rs` API
  externals".
- **Translation patch 04 models** (2026-11-25, human decisions: targets K01–K20 of `skill.rs`,
  patch 04 with hunks H1–H9; reviewed in 3 rounds and **signed off by the spec owner 2026-11-25**): in
  `formal/trusted/Rmcp/FunsExternal.lean` and `TypesExternal.lean`, sections "Public `skill.rs`
  API", all definitions or structures, no axiom:
  - **12 `prim` models**, one per one-line wrapper of the private module `skill::prim` that the
    patch adds (opaque in the translation): `sha256`, `find_query_or_fragment`, `strip_suffix`,
    `strip_prefix`, `last_slash_segment`, `split_slash`, `join_slash`, `split_once_percent`,
    `split_percent`, `percent_encode_controls`, `percent_decode_utf8`, `nfkc`;
  - **28 `core`/`alloc`/`std`/crate models**: `get_general_category`
    (`unicode-general-category 1.1.0`), array `IntoIterator::into_iter` and `IntoIter::next`,
    `bool::then_some`, `char: From<u8>`, `char` `PartialEq::eq`, `Iterator::all` (default),
    `<ParseIntError as Debug>::fmt`, `u8::{is_ascii_alphanumeric, is_ascii_hexdigit,
    from_str_radix}`, `Option::as_deref`, `Option` `Try::branch` and
    `FromResidual::from_residual`, `Bytes::all`, `str::{is_empty, split_at_checked, split_at,
    bytes}`, `HashSet::{with_capacity, insert}`, `Cow::into_owned`, `Cow` `Deref::deref`,
    `str::to_ascii_uppercase`, `String::as_str`, `Vec::pop`, `serde_json::Map::{new, insert}`;
  - **4 structures**: `array::IntoIter` (array and alive range), `str::Bytes` (the inner slice
    iterator), `HashSet` (element list), `serde_json::Map` (the `BTreeMap` entries ascending by
    key in Rust's `String` order, lead decision 2026-11-25);
  - helpers in `ExtModel` (listed in the evidence README) and **three `opaque` constants** (no
    axiom): `ExtModel.sha256` (SHA-256 of `sha2 0.11.1`), `ExtModel.nfkc` (NFKC of
    `unicode-normalization 0.1.26`), `ExtModel.generalCategory` (the General_Category tables of
    `unicode-general-category 1.1.0`). Their laws are not stated in `trusted/`; a statement that
    needs one takes it as a premise (human decision 2026-11-25), under the review rule below.
    Their placeholder values (32 zero bytes, the identity, `Unassigned`) are what compiled
    evaluation returns, so evaluating or differentially testing anything that reaches them is
    meaningless (lead decision 2026-11-25: no compiled replacement).
  Stated exceptions: `<ParseIntError as Debug>::fmt` is a **total, not exact,** model (lead
  decision 2026-11-25): `Ok(())` and the formatter unchanged, because `core::fmt::Formatter` is
  opaque in the Aeneas library, and its only caller is the `expect` of `push_normalized_part`,
  whose panic path two checked hexadecimal digits never take; the default `Iterator::all` is the
  `next` loop (an iterator that overrides `try_fold` is not modelled; no generated definition
  calls it); `HashSet::with_capacity` stores `ExtModel.randomState` (its review rule applies)
  and does not model hashbrown's capacity-overflow panic (unreachable within the size
  convention); the patch-induced premises for K13 and K16 (below). Proved spec theorems:
  `formal/proofs/Proofs/External/Skill.lean`. Sources and tests per model:
  `formal/trusted/evidence/README.md`, "Skills externals".
  The total is now **10 `opaque` constants** (`hmacSha256`, `sipHash13`, `nowMs`,
  `SerdeJsonValue`, `randomState`, `serdeJsonFromSlice`, `SerdeJsonErrorImplCarrier`, `sha256`,
  `nfkc`, `generalCategory`).
- **Codec-state hypothesis** (accepted at S12): `Defs/CodecState.lean` defines `CodecValid`
  (keyring clauses; single-key codecs unconstrained; pairwise distinct key ids),
  `CodecFallbacksKnown` (every rs1 fallback id is a key id) and `FallbacksKnown`. It is a
  hypothesis of the statements, not an axiom: E09, E11 and the rs1 round trips assume
  `CodecFallbacksKnown`, E09a `FallbacksKnown`, E10 and rs2 nothing. `CodecValid` implies
  `CodecFallbacksKnown`. The excluded constructors are what establish it in Rust; they are not
  verified.
- **Tools:** Charon `0.1.324` and Aeneas (`nightly-2026.11.24-fb44cb4`), Lean `v4.36.0` kernel
  (Mathlib `v4.36.0`), Rust `nightly-2026-09-17`, since the Aeneas upgrade of 2026-11-24 (until
  then Charon `0.1.235`, Aeneas `nightly-2026.08.20-5d08da4`, Lean `v4.31.0`, Rust
  `nightly-2026-06-01`); prebuilt Aeneas Lean library (archive sha256 checked) and Mathlib oleans
  (not digest-checked). The Aeneas library builds without warnings, so the gate is
  `lake build --wfail` and the build-log allowlist is empty (N10).
- **Configuration:** the translated configuration above. **Patches:** one,
  `formal/trusted/patches/01-request-state-wire.patch` (the refactor and its tests; D2 fallback,
  2026-11-23; reviewed by two independent agents and signed off by the human on 2026-11-23, VERIFICATION.md §4),
  and the test-only `02-phase2-tests.patch` (34 `#[cfg(test)]` boundary tests, S34, H3, 2026-11-24;
  it changes no translated item, the re-translation is byte-identical; see "Documents"), and
  (since 2026-11-24, **reviewed and signed off 2026-11-24; specs pending**) translation patch
  `formal/trusted/patches/03-request-state-public.patch` (variant A, human decision 2026-11-24;
  +6/−2 non-test Rust lines in `request_state.rs`, no test added or changed): hunk 1 in `seal_at`,
  `let ttl = options.ttl;` before the `match` (without it Aeneas stops with "Unreachable" on the
  `Some(ttl)` arm, matching on a field read through a shared reference; `Option<Duration>` is
  `Copy`, so the match computes the same expression), hunk 2 in `open_json_with`, an explicit
  `match` in place of `.map_err(RequestStateError::Deserialization)` (without it Aeneas fails on
  the `FnOnce` impl of the variant constructor, "Arrow types are not supported yet";
  `Result::map_err` is that `match`). Existing tests cover both hunks (the TTL, known-answer and
  round-trip tests for hunk 1; `seal_open_roundtrips_json` and
  `serde_is_reached_only_after_integrity_verification` for hunk 2; 835 library tests pass before
  and after, measured). With it, `seal`, `seal_with`, `seal_at`, `with_rs1_signing`,
  `with_rs1_fallback`, `open_json`, `open_json_with` and `new_with_keyring` translate with real
  bodies; every earlier generated block is unchanged up to its `Source` line numbers. **Hand
  edits of the translation:** none.
  **Charon and script changes with patch 03** (lead decisions 2026-11-24 on the human decision
  of targets R09–R15; signed off 2026-11-24): in `crates/rmcp/Cargo.toml` the eight `exclude` entries
  above and their comments are removed and `serde_core` moved from `exclude` to `opaque` (so the
  trait `DeserializeOwned` of the `open_json*` signatures is translated; only signatures and
  trait declarations); `scripts/check-original-linkage.sh` requires the non-`request_state`
  `exclude` list to be exactly `["serde"]` (was `["serde", "serde_core"]`);
  `scripts/aeneas-translate.sh` adds `serde_core 1.0.229` to `PINNED_DEPS`;
  `formal/trusted/translation-pins.txt` is updated to the new `Funs.lean` hash and line of the
  pinned `initialize` word.
  **Exclusions:** the list above (plan Section 2.3).
- **Statements:** `formal/specs/Defs/` and `formal/specs/Specs/` (public API; index
  `formal/specs/README.md`), and `formal/proofs/Proofs/Internal/` with `formal/proofs/Proofs/Defs/`
  (private, crate-internal and patch-only functions and the model laws; human decision 2026-11-24).

External models (plan Section 4), in `formal/trusted/Rmcp/FunsExternal.lean` and
`TypesExternal.lean`; sources and tests per model in `formal/trusted/evidence/README.md`:
  And (since 2026-11-25, human decisions: targets K01–K20, hunks H1–H9; **reviewed in 3 rounds
  and signed off by the spec owner 2026-11-25**) translation patch
  [`formal/trusted/patches/04-skill-public.patch`](../trusted/patches/04-skill-public.patch) on
  `crates/rmcp/src/model/skill.rs` (no test added or changed): the private module `prim` of
  twelve one-line wrappers (each the original expression) and hunks H1 `sha256_digest`, H2
  `Skill::validate`, H3 `skill_name_from_uri`, H4 `is_valid_skill_name`, H5
  `manifest_resource_key`, H6 `normalize_percent_encoding`, H7 `is_sha256_digest`, H8
  `validate_skills`, H9 `SkillResource::verify` (the header gives the error each hunk avoids and
  why the values are unchanged; H4 and H9 are not needed for the translation and are kept by
  human decision). **Linkage:** 13 targets are ORIGINAL (K01–K04, K08–K12, K17–K20 translate
  unmodified) and 7 need patch 04 (K05–K07, K13–K16); `scripts/check-original-linkage.sh`
  checks that the patch-04 targets are absent from the unpatched translation (it drops the seven
  patch-04 skills start points and the opaque entry `rmcp::model::skill::prim` from the copy's
  Charon settings, and in its run `scripts/aeneas-translate.sh` fails if one of the ten
  `PATCH04_TARGETS` is translated from the unmodified source). Recorded runs (2026-11-25, scratch
  clone of `b363a8a` with this change committed as scratch commit `b3e26c4`): exit 0, all 38
  ORIGINAL targets defined, blocks identical up to `Source:` (`Funs.lean` 60/60, `Types.lean`
  40/40, the two External templates 34/34 and 10/10); negative test (scratch commit `a847d99`,
  `model.skill.Skill.name` added to `PATCH04_TARGETS`): exit 1, "patch-04 target
  model.skill.Skill.name is translated from the unmodified source" (evidence README, "Linkage of
  the skills targets"; plan Section 19, amendment 2026-11-25). **Patch-induced premises** (the
  original would not need them; evidence README): (1) H2 and H4 collect the NFKC form into a
  `Vec<char>` where the original streams it, adding a capacity-overflow panic for a form above
  `isize::MAX` bytes (a name above of the order of `isize::MAX / 24` bytes; unreachable in practice), so a
  K13 statement may take the NFKC length bound of `nfkc_spec` as a premise; (2) `prim::split_slash`
  and `prim::split_percent` (H5, H6) collect the parts into a `Vec<String>` (24 bytes per
  element) where the original streams the split (H6) or collects `&str`s (16 bytes, H5), adding a
  capacity-overflow panic at `24 * parts > isize::MAX`, so K13 and K16 statements may take the
  premise `hlen : 24 * (splitBytes sep s.val).length ≤ maxStringBytes` of `split_slash_spec` and
  `split_percent_spec`; unreachable on x86_64, where a `&str` has fewer than 2^57 bytes (57-bit
  virtual addresses) and 24 · 2^57 < 2^63 − 1 = `isize::MAX`.
  **Charon and script changes with patch 04** (human decisions 2026-11-25): fifteen `start_from` entries for K01–K20
  and `rmcp::model::skill::prim` in `opaque` (`crates/rmcp/Cargo.toml`); `PINNED_DEPS` adds
  `percent-encoding 2.3.2`, `unicode-normalization 0.1.26`, `unicode-general-category 1.1.0`;
  the two `_` globs `rmcp::model::skill::_::new` (K02, K04, K08, K10, K17) and
  `rmcp::model::skill::_::with_meta` (K11, K20) are a stated exception to "a `_` glob matches
  exactly one Rust item": each must match exactly its listed `rust_name`s (`MULTI` in
  `scripts/aeneas-translate.sh`; plan Section 15, rule 3); `formal/trusted/translation-pins.txt`
  is updated to the new `Funs.lean`.

| Contract | Model (no axiom) | Status |
|---|---|---|
| HMAC (`prim.hmac_sha256`, `_verify`) | `ok (hmacSha256 k m)`, `ok (t = …)` | accepted (S08) |
| Base64url, no padding (`prim.b64_*`) | `ExtModel.b64`, `ExtModel.b64Decode` | accepted (S08) |
| Standard library | definitions and structures (list below) | accepted (S09) |
| `zeroize` | `Zeroizing::new`, `Clone`, `Deref`; `Zeroize` impls | accepted (S09) |
| Clock (`now_ms`, opaque) | `ok nowMs`, `opaque ExtModel.nowMs` | accepted (S09) |
| `serde_json::Error` (type) | structure, `opaque ExtModel.SerdeJsonErrorImpl` | accepted (S09); since translation patch 03 `SerdeJsonErrorImpl` is a `def` over `opaque ExtModel.SerdeJsonErrorImplCarrier : NonemptyType` (reviewed and signed off by the spec owner 2026-11-24) |
| Codec state | `Defs.CodecState` hypotheses (above) | accepted (S12) |
| Phase 2: strings, `Arc`, `Option`, `Result`, slices, ranges | definitions (S26) | signed off 2026-11-23; 22 laws proved; `RangeInclusive::contains` model changed 2026-11-24 (Aeneas upgrade, human decision A2; one fresh model review, no defect; two laws restated exactly, re-signed 2026-11-24) |
| Phase 2: `i64::from_str`, `Ipv4Addr`/`Ipv6Addr` | definitions, structures (S27) | signed off 2026-11-23; 21 laws proved |
| `serde_json::Value` (type) | `opaque ExtModel.SerdeJsonValue` (S27) | signed off 2026-11-23 (no law: only moved) |
| Translation patch 03: `Duration::as_millis`, `str::to_owned`, `HashMap::{contains_key, is_empty, new, entry}`, `VacantEntry::insert`, `Hash for str`, `Borrow<str>`/`PartialEq<str>` for `String`, `slice::Iter::any`, `Iterator::any`, `serde_json::from_slice`, `Error::source`; types `OccupiedEntry`, `VacantEntry` | 14 definitions, 2 structures; `opaque ExtModel.randomState`, `opaque ExtModel.serdeJsonFromSlice` | reviewed, signed off by the spec owner (2026-11-24) |

Details:
- HMAC: both functions always succeed. Stated exception: the SHA-256 bit-length `u64` counter
  (`sha2-0.11.1/src/block_api.rs` line 66) overflows for a message of at least `2^61 − 64` bytes
  or a key of at least `2^61` bytes; not modelled (the `x86_64` address space is at most `2^57`
  bytes).
- Base64url: strict decoding; round trip, canonicity, URL-safe alphabet (no `.`) and length laws
| Translation patch 04: the 12 `skill::prim` wrappers; 28 `core`/`alloc`/`std`/`serde_json`/`unicode-general-category` functions; types `array::IntoIter`, `str::Bytes`, `HashSet`, `serde_json::Map` | 40 definitions, 4 structures; `opaque ExtModel.sha256`, `opaque ExtModel.nfkc`, `opaque ExtModel.generalCategory`; `<ParseIntError as Debug>::fmt` total (lead decision) | reviewed (3 rounds), signed off by the spec owner (2026-11-25) |
  proved (`Proofs/External/Base64.lean`); differential check against `base64 0.23.1`: 25,682,976
  comparisons, 0 mismatches (S18 re-run with the differential toolchain pinned to Rust 1.96).
- Standard library: `Option` `Default`,
  `Result::is_err`, `&[T]` `Default`, `str::len`, `str::as_bytes`,
  `String::{with_capacity, push_str, push, as_bytes, from_utf8}`, `String` `PartialEq::eq`,
  `Eq::assert_fields_are_eq`, `Clone`, `Hash::hash`, `RandomState` `Clone` and
  `build_hasher`, `DefaultHasher` `write` and `finish`, `HashMap::get` (first entry with an equal
  key, no hashing), `HashMap` `Clone`; structures `Duration`, `FromUtf8Error`, `HashMap`
  (association list), `RandomState`, `DefaultHasher` (with `opaque ExtModel.sipHash13`). Until the
  Aeneas upgrade of 2026-11-24 also `Borrow::borrow` (blanket), `Option::ok_or`,
  `Result::map_err` and `Vec::is_empty`; these four are now defined in the Aeneas library (lead
  decision N8), part of the Aeneas trust item, and their laws are unchanged up to the forced
  renames.
- Clock: environmental assumption, not modelled: `Utc::now` panics if the clock is before 1970
  or outside chrono's range.
- Allocation failure is not modelled: `ok` from a `String`/`Vec` model means "returns, or aborts
  or panics for memory reasons".

Review rules that stay in force:
- **Clock.** `nowMs` is one constant, so every reader of the clock is pure in the model. No spec
  statement mentions the functions `rmcp.model.request_state.RequestStateCodec.now_ms`,
  `…RequestStateCodec.open`, `…RequestStateCodec.open_with`, `…RequestStateCodec.open_json`,
  `…RequestStateCodec.open_json_with`, `…RequestStateCodec.seal` or
  `…RequestStateCodec.seal_with` (a variable named `now_ms`, such as the time parameter of E01,
  is not covered); opening is specified through `open_at` and sealing through `seal_at` (or its
  `Defs` model `sealAt`), with an explicit time. Exceptions (human decisions 2026-11-24, extended
  by the spec owner 2026-11-25): only the spec theorems of `open`, `open_with`, `open_json`,
  `open_json_with`, `seal` and `seal_with`, their `Theorems.*` restatements and the corollaries
  `open_with_spec_of_length_le`, `seal_with_spec_of_length_le` and `seal_spec_of_length_le` (and
  their restatements) may name these functions and `ExtModel.nowMs`, and only with these
  postconditions: `open`/`open_with`, `resultBytes result = openAt … ExtModel.nowMs.val`;
  `open_json`/`open_json_with`, the error of `openAt … ExtModel.nowMs.val` unchanged, otherwise
  the `ExtModel.serdeJsonFromSlice` outcome for the opened payload with `Err` mapped to
  `Deserialization`; `seal`/`seal_with`, `sealAt … ExtModel.nowMs.val = some (ExtModel.utf8
  result)`, `sealAt` (`Defs.CodecState`) being the model of the private `seal_at` (human decision
  2026-11-25; it replaces the earlier wording "the result of the translated `seal_at` at
  `ExtModel.nowMs`"). Their docstrings state the one-reading caveat and the inherited exceptions.
  No other statement names `ExtModel.nowMs`, no statement has a premise or conclusion about its
  value, and no statement relates two clock readings; `now_ms` itself stays unmentioned. The
  internal statements of `seal_at` (R10a) and of its round trip with `open_at` (R10b) use
  explicit times.
- **`HashMap::get`.** Faithful for `Hash`/`Eq` instances that agree and do not fail (only
  `K = Q = String` occurs). Since translation patch 03 the same holds for `contains_key`
  (`K = String`, `Q = str` or `String`) and `entry` (`K = String`).
- **`ExtModel.randomState`** (translation patch 03, signed off 2026-11-24): no statement has a premise or
  conclusion about its value or about the `hash_builder` of a map built by `HashMap::new`, and no
  statement states or relies on the equality (or inequality) of maps, or of codecs containing
  them, built by distinct `HashMap::new` calls (for example two results of `new_with_keyring`):
  in Rust their `RandomState` keys differ on the same thread and are independent random keys otherwise (`std/src/hash/random.rs` lines 71–75); the
  `hash_builder` is unobservable through the modelled API.
- **`ExtModel.serdeJsonFromSlice`** (translation patch 03, signed off 2026-11-24): a statement may only
  say that the result of `open_json`/`open_json_with` is this outcome for the opened payload,
  mapped as the Rust code maps it; as for two clock readings, no statement relates two calls of
  `open_json`/`open_json_with` (or of `serde_json::from_slice`). Stated exceptions: a
  `Deserialize` impl that panics, aborts or does not terminate, and one that is
  non-deterministic or has side effects (global or thread-local state, a random number
  generator).

Opaque items (Charon `opaque` setting in `crates/rmcp/Cargo.toml`, committed):
`rmcp::model::request_state_wire::prim` (wraps the HMAC and base64 `Engine` types, B1, B3),
`rmcp::model::request_state::_::now_ms` (system clock; since translation patch 03 called by the
targets `seal_with` and hence `seal`, under the extended clock rule, and by non-target wrappers), and
the external crates `zeroize`, `base64`, `hmac`, `sha2`, `thiserror`, `chrono`, `serde_json`
(signatures only), since translation patch 03 also `serde_core` (moved from `exclude`; signatures
- **`ExtModel.sha256`, `ExtModel.nfkc`, `ExtModel.generalCategory`** (translation patch 04,
  human decision 2026-11-25 that their laws are premises; rule signed off by the spec owner
  2026-11-25): no axiom and no
  `trusted/` definition states a law about them. A statement may mention them in its
  conclusion only unopened, as the value the Rust code computes (`ExtModel.sha256 bytes`,
  `ExtModel.nfkc t.toList`, `ExtModel.generalCategory c`). A fact about them may enter a
  statement only as an explicit premise, and only if it is true of the real function on every
  input it quantifies over, with the source cited in the statement's docstring; a premise that
  is false of the real function (which would make the statement vacuous) is a review defect.
  In particular:
  - `sha256`: no premise about its values except equalities or inequalities of digests of the
    specific inputs of the statement, as conditions on those inputs (e.g. "the digest of these
    bytes is the recorded one"); no universal law, and never injectivity or collision freedom
    (false: the function maps every byte list to 32 bytes).
  - `nfkc`: the NFKC-length domain: a premise `4 * (ExtModel.nfkc cs).length ≤ maxStringBytes`
    (the `Vec` bound of `prim::nfkc`, the patch-induced premise of K13) for the specific `cs`
    of the statement; facts of UAX #15 for the specific input, such as "an ASCII-only `cs` is
    its own NFKC form" or idempotence `nfkc (nfkc cs) = nfkc cs`, each as a premise with the
    clause of UAX #15 cited. No premise that equates the NFKC forms of two inputs unless that
    is the condition the Rust code tests.
  - `generalCategory`: facts about specific characters or about the ASCII range, each as a
    premise matching `UnicodeData.txt` of the Unicode version of `unicode-general-category
    1.1.0` (e.g. `'a'`–`'z'` are `LowercaseLetter`, `'0'`–`'9'` `DecimalNumber`, `'-'`
    `DashPunctuation`); a universal premise over non-ASCII characters only if it is a stability
    guarantee of the Unicode standard (cited).
  Review checks for each such premise that it is satisfiable by the real function on the
  inputs the statement is meant for. Form of the premises (lead decision 2026-11-25, finding
  U3): each premise about an opaque constant is either
  - a **law**, stated in implication form over the inputs it covers (e.g. "for an ASCII-only
    `cs`, `ExtModel.nfkc cs = cs`", i.e. `(∀ c ∈ cs, c.toNat < 128) → ExtModel.nfkc cs = cs`;
    "`'a' ≤ c ≤ 'z'` → `ExtModel.generalCategory c = LowercaseLetter`"), which is true of the
    real function for every input satisfying its hypothesis and does not narrow the statement;
    or
  - a **domain restriction**: an unconditional fact about the statement's own input (e.g.
    `4 * (ExtModel.nfkc t.toList).length ≤ maxStringBytes`, or "the digest of these bytes is the
    recorded one"), which narrows the inputs the statement covers; it must be declared as a
    domain restriction in the statement's docstring and in the "Assumptions" column of the
    summary table of `formal/specs/README.md`, with the inputs it excludes.
  A premise taken from UAX #15, FIPS 180-4 or `UnicodeData.txt` must also cite evidence that the
  pinned crate conforms on those inputs: for `nfkc`, the conformance of `unicode-normalization
  0.1.26` (Unicode 18.0.0, `src/tables.rs` line 18) to the Unicode `NormalizationTest.txt` on
  those inputs (the upstream `tests/normalization_tests.rs`, generated by the crate's
  `scripts/unicode.py` and not shipped in the crates.io package, run at the 0.1.26 release) or a
  Rust vector run against the pinned crate; for `sha256`, a Rust vector of `sha2 0.11.1` (e.g. the spec
  example of `sha256_digest::matches_the_digest_in_the_spec_example`); for `generalCategory`,
  a Rust vector of `unicode-general-category 1.1.0` on the characters concerned. A premise
  without that evidence, or in neither form, is a review defect.
- **`HashSet` element order** (translation patch 04, lead decision 2026-11-25): Rust's
  `HashSet` iteration order is unspecified, so no statement may depend on the order of the
  `elements` list of the model; statements speak of membership, of the `bool` of `insert` and
  of order-independent quantities only.
- **`serde_json::Map`** (translation patch 04, lead decision 2026-11-25): modelled exactly as
  the `BTreeMap` it is (no `preserve_order`): entries ascending by key in Rust's `String` order,
  so each Rust map has one model value; statements may rely on that order.
and trait declarations, for `DeserializeOwned` in the `open_json*` signatures); since S21 (Phase 2, plan Section 15) also the crates of the widened features
(`http`, `tokio`, `tokio_util`, `tracing`, `tracing_core`, `futures`, `futures_util`, `futures_core`,
`bytes`, `sse_stream`, `hyper`, `tower_service`, `uuid`, `schemars`, `pin_project_lite`,
`rmcp::model::skill::prim` (translation patch 04: the `str` pattern APIs, SHA-256, NFKC and
percent-encoding, B1, B2),
`tokio_stream`, `http_body`, `http_body_util`, `rand`, `async_trait`, `pastey`, `oauth2`, `reqwest`,
`url`; signatures only) and the type `rmcp::transport::auth::AuthorizationManager` (H4; it appears
in no generated file). Marking an item opaque only keeps its signature; its contract is the model
above.

## Bugs found

**Rust code: no bug found in the 25 verified functions** within the stated scope (the
translated configuration, the external models and their stated exceptions, the codec-state
hypothesis). No proof needed a change of production code beyond the refactor (now patch 01,
which was made for translatability, not for a proof), and no differential or
test run found a disagreement (S13: 125,664 + 12,160 + 216 differential cases, 0
disagreements on inputs satisfying the hypotheses; S04a: about 2.9M `open` calls base vs
refactor, no difference; S16: 95 request-state tests pass, 8 hand-made mutants each caught).
Behaviours recorded as facts, not bugs: a single-key codec built with `new_unchecked` or the
deprecated `new` accepts a key of any length (only `try_new` checks it); and
`rs1_fallbacks_verify` panics (`expect`) if an rs1 fallback id is not a key, which the excluded
keyring constructors prevent (not verified).

**Phase 2 (S24, human decision H7, 2026-11-24): `async_rw` method lists miss six core MCP
names.** `is_standard_method` / `is_standard_notification` (`async_rw.rs` 396–433, upstream
`7caec76`) do not list `tasks/get`, `tasks/result`, `tasks/cancel`, `tasks/list`,
`notifications/tasks/status` and `notifications/elicitation/complete`, which are in the core
MCP schemas (`2025-11-25`; plan H6 union). Effect: only when a line fails to deserialize
(`try_parse_with_compatibility`, `Err` arm, lines 468–485; `should_ignore_notification`, lines
437–457) and, after any leading BOM is removed (line 464), the line is valid UTF-8 and parses as a
JSON value with a string `method` (otherwise the result is `Err`), a line with one of these
method names is silently dropped (`Ok(None)`) instead of
returned as a `Serde` error: always for the two notifications, and for the four `tasks/*`
requests when the message has no `id` key (a standard, listed name gives
`Err(JsonRpcMessageCodecError::Serde)` in these cases). The T05/T06 statements describe the code
("in the core list and not in `Defs.Methods.codeOmits`"). Not yet reported upstream (see "Open
items").

**Phase 2 (S25, human decision H8, 2026-11-24): `is_disallowed_metadata_ipv4` does not block
`240.0.0.0/4`.** `AuthorizationManager::is_disallowed_metadata_ipv4` (`auth.rs` 1343–1354,
upstream `7caec76`) accepts addresses in the reserved block `240.0.0.0/4` (RFC 1112 §4; IANA
special-purpose registry, "Reserved"), except the broadcast address `255.255.255.255`, which it
blocks. A metadata URL with such an address passes the SSRF check (A02 and, through embedded
forms, A03), and a resolved address in it is classed `Public` by the DNS-resolver filter
(`AddressClass::of`, `auth/metadata_resolver.rs` 42–74, which calls
`is_disallowed_metadata_ipv4` at line 52), although the module doc (lines 8–9) says reserved
addresses are never allowed. The A02 statement describes the code (the plan's list of eleven
ranges). Not yet reported upstream (see "Open items").

Defects found in the plan, documents and tooling, with their state:

1. Plan §4 said the constructors enforce "every key is at least 32 bytes"; false for
   `new_unchecked` and the deprecated `new` (single-key codecs). Found at S05 (drafter note 3),
   settled at S12/S13. **Fixed**: plan §4 reworded, `CodecValid` leaves single-key codecs
   unconstrained.
2. Plan §2.2 listed W01 as a dependency of E07/E08; `seal_rs1`/`seal_rs2` call the codec's own
   `Self::b64_len` (E02). Found at S01. **Fixed**: plan §2.2 lists E02, matching the records.
3. Plan §3 required an `h_count` premise for E11; it is derivable there (E11 calls W08/W09 only on
   tokens starting with `rs1`/`rs2`). Found in the S13 spec rounds, decision (j). **Fixed** (plan
   §3).
4. The differential check's `rdiff/Cargo.lock` was git-ignored, but `run.sh` builds `--locked`, so
   a fresh clone could not run it. **Fixed** in `d8435ed` (lock tracked).
5. The differential check was built with whatever Rust toolchain rustup selected. Found at S18
   (F4). **Fixed**: `rdiff/rust-toolchain.toml` pins Rust 1.96 (`aacfbf7`).
6. `formal/README.md` status line was stale ("S03: toolchain only"). Found at S18 (F1).
   **Fixed** in `aacfbf7`.
7. The macOS Aeneas release bundle links `/nix/store` libraries, so its binaries do not start on
   a plain Mac. Found at S03. **Worked around** (`DYLD_FALLBACK_LIBRARY_PATH=/usr/lib`); not
   reported upstream.
8. Aeneas `toStr` discharges its side condition with `decide +native` although a kernel proof
   exists, adding the five native-code axioms. Found at S03/S04a. **Resolved** by the Aeneas
   upgrade of 2026-11-24: the `toStr` of `nightly-2026.11.24-fb44cb4` checks it in the kernel, no
   native-code axiom remains (reviewed and re-signed by the spec owner 2026-11-24 of the upgrade).
9. Lean's `#print axioms` can omit axioms reached through inductive/constructor cycles. Found at
   S03. **Worked around**: the project's audit (`scripts/lean-axiom-audit.lean`) walks all
   constants and computes a superset.
10. The plan header ("Current state", "Not yet done") is stale: it says every proof is `OPEN`.
    Found at S19. **Fixed** at S19 acceptance (spec-owner decision 2026-11-23): the header now
    gives the current status and the human items.
11. The status headers of several evidence files are stale: S08 and S09 say "awaiting the human
    spec owner's sign-off", S06, S07 and S10 say "staged, awaiting human review" and "nothing is
    incorporated yet" (S07/S10 also record their agent proof review as not run / pending), S05
    names the spec owner as TBD, and S16 says "not reviewed", although the board marks these
    steps `ACCEPTED`, the commits record the incorporation, and the S16 commit records an agent
    review. Found at S19. **Fixed** at S19 acceptance: each of these files now starts with a dated
    "Outcome" line (accepted, commit); the original status text is kept as history.
12. The plan (S04a, Section 5), the guides and `docs/VERIFICATION.md` name three CI workflows;
    only `.github/workflows/lean-build.yml` existed. Found at S19. **Fixed** (2026-11-23):
    `aeneas-translation.yml` and `patched-tests.yml` written, reviewed and checked locally
    (the CI-workflows evidence (git history at 223ff12)); they have not run on GitHub yet (S17).

Items 1–3 are in the plan text the specifications were checked against, not in the Rust code.

## Phase 2

Plan Part II (Sections 13–25). Twenty-five existing upstream functions in six files of
`crates/rmcp/src/` at `7caec76`, unmodified, to be verified with linkage `ORIGINAL`, plus the
composition theorems C01–C05. Selected by a measured pilot (plan Section 14, 2026-11-23); the
pilot is not the project's translation, which is S21.

### Phase 2 results (S37, 2026-11-24)

Written by the lead, checked by an independent review, accepted by the human owner on 2026-11-24.

Plan Section 25 template, filled with the actual results (no wording changed except the bracketed
lists):

> At upstream SDK commit `7caec762799bece6fba38e4298b8ca7db8bac12c`, unmodified (the translation of
> these functions does not depend on any translation patch and `crates/rmcp/src` is the pinned
> upstream tree; checked by `scripts/check-original-linkage.sh`), translated for
> `x86_64-unknown-linux-gnu` with `--no-default-features --features
> request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth`
> (and the Charon settings in `crates/rmcp/Cargo.toml`), the following existing SDK functions are
> verified against the Aeneas translation (`nightly-2026.08.20-5d08da4`): M01–M05
> `JsonRpcMessage::{into_request, into_response, into_notification, into_error, into_result}`,
> M06–M07 `NumberOrString::{numeric_string_value, matches_response_id}`, M08
> `TaskStatus::is_terminal`, M09–M12 `SamplingContent::{into_vec, is_empty, len, first}`, M13–M14
> `Reference::{as_prompt_name, as_resource_uri}`, T01–T03
> `SseEventSizeLimiter::{check_limit, finish_line, observe}`, T04–T06
> `async_rw::{without_carriage_return, is_standard_notification, is_standard_method}`, T07–T08
> `tower::{default_port, AllowedPort::matches}`, A01–A03
> `AuthorizationManager::{embedded_ipv4, is_disallowed_metadata_ipv4,
> is_disallowed_metadata_ipv6}`, together with the composition theorems C01 (SSE chunk append),
> C02 (SSE bound at chunk boundaries), C03 (`into_result` from `into_response`/`into_error`),
> C04 (no SSRF bypass through embedded IPv4, with a corollary in `Defs.Net` terms), C05 (every
> standard notification is a standard method) and the plan Section 16.1 joint lemmas. These
> results rest on the trusted base listed in `formal/README.md` and `STATUS.md`: Charon, Aeneas
> and Lean; the translated configuration; the standard-library, `core::net` and integer-parsing
> models in `formal/trusted/` (definitions, structures and `opaque` constants; no trusted axiom);
> the `toStr` native-code axioms in `formal/trusted/native-axioms.lock`; the statements in
> `formal/specs/`; and the functions not taken (Section 16.5). They do not establish the
> correctness of the functions that call these targets, of URL or HTTP parsing, of `async` code,
> or of DNS resolution. Functions not listed are open for the reasons given below.

None of the 25 is open; the functions measured and not taken are listed, with their blockers, in
plan Section 16.5.

Two qualifications the template does not carry: (1) the statements in `formal/specs/` are now the
public API only; the statements about the private targets (M06, M07, T01–T08, A01–A03) and the
model laws are in `formal/proofs/Proofs/Internal/` and part of the same trust (human decision
2026-11-24, plan Sections 4 and 20); (2) "checked by `scripts/check-original-linkage.sh`" holds
locally (on `3ded001` twice in the S23 review, and again in the S34 run; exit 0, blocks 41/27/30/9)
and has not yet run in CI; the records say "pending S22 CI" until the first push.

**D10 count for Phase 2:** verified on original code **25**, proved with a translation patch **0**,
open **0** (all 25 records: `translation: LEAN_OK`, `spec: REVIEWED`, `linkage: ORIGINAL`,
`proof: CHECKED`). In total 50 targets are proved: 25 verified on original code (Phase 2) and 25
proved with translation patch 01 (Phase 1), plus C01–C05, the Phase 1 round trips and the joint
lemmas (185 restated theorems: 19 public, 166 internal, of which 116 are model laws).

**Trusted-base delta since Phase 1:**
- External models: added the `core::net` (`Ipv4Addr`, `Ipv6Addr`), integer-parsing (`str::parse`,
  `i64::from_str`, `ParseIntError`), `str`/`String`/`Arc` equality and dereference, `Option`,
  `Result`, slice, range and `MaybeUninit` models (S26/S27), with 44 new proved laws (116 in all,
  restated in `Proofs/Internal/External.lean`); one more `opaque` constant (`SerdeJsonValue`, five
  in all). Trusted axioms: still **0**.
- Native-code axioms: **5 → 35** (the 30 Aeneas `toStr` side conditions of the method-name and
  `http`/`https` literals, human decision H2), all locked and kernel-provable.
- Charon settings: 25 more `start_from` entries; 24 more `opaque` external crates of the widened
  features (signatures only; see "Trusted base"); the `opaque` `AuthorizationManager` type (H4,
  reason corrected at S23); no new `exclude` entry. The feature list (H1) is part of the translated
  configuration; the Phase 1 output is byte-identical under it.
- Translation pin: `formal/trusted/translation-pins.txt` (S21; sha256 of `Funs.lean` plus the one
  excused line 1971).
- Patches: the test-only patch 02 (S34, H3; changes no translated item).
- Phase C (no trusted-base change): the listed proofs use the signed-off laws instead of unfolding
  model bodies; two `#guard_msgs` lists shrank, builtins only (`Slice.first_spec` and T01).

**Bugs found (Phase 2; see "Bugs found"):** H7 — `async_rw`'s method lists miss six core MCP names,
so a line that fails to deserialize but parses as JSON with one of these method names is dropped
(`Ok(None)`) instead of returned as a `Serde` error (for the four `tasks/*` requests only without
an `id`); H8 — `240.0.0.0/4` (except `255.255.255.255`, which is blocked) is not blocked by
`is_disallowed_metadata_ipv4`, and so passes the SSRF check and the DNS-resolver filter. Both are
recorded, with the statements describing the code; neither is reported upstream yet.

**Evidence beyond the proofs:** every plan Section 22 boundary case is exercised by a Rust test (37
upstream, 104 through the test-only patch 02); 835 library tests pass locally with both patches
(847 since the 12 R09–R15 boundary tests of 2026-11-25, see "Documents");
one seeded mutation (`64..=127` → `64..=126` in `is_disallowed_metadata_ipv4`) is caught by
`s34_a02_range_boundaries` (S34; the S34 reviewers caught five more mutants in scratch, not
recorded as evidence).

**Phase 2 open items (full list: "Open items"):** H5 (project owner and budget; it also blocks the
acceptance of S01 and S20 and gate G1); the first push, which runs the three CI workflows and makes
S03, S04a, S21 and S22 (and through them S23 and S34) `ACCEPTED`; S17 and S35 (each CI check shown
to fail once on a throwaway branch; `NOT_STARTED`); S36 (fresh-clone reproduction, after S35); the
upstream reports for H7 and H8 (need the owner's go-ahead); the upstream Aeneas `toStr` fix that
would remove the 35 native-code axioms; the Aeneas bump (plan Section 25); the S31 candidate lemma
(`observe = historyOutcome` for every cap ≥ 1).

**Cost:** Phase 2 ran on 2026-11-23 and 2026-11-24 (plan estimate: D1–D10), by AI agents in the
`mcp-cycle` process, with the spec owner (Hoang Le Truong) signing off each specification and
human decision; gate G1 is not yet met. Token cost is not recorded; the only measured compute
figures are the pilot's (plan Section 14: about 7 s per warm translation, about 17 GB of build
output). The budget (H5) has not been named, so no comparison with a budget is possible.

**Phase 3 scope (plan Section 23):** what Phase 2 now provides as lemmas, and what still blocks:

| Phase 3 candidate | Phase 2 lemmas it would use | Still blocked by |
|---|---|---|
| `AddressClass::of`, `MetadataAddressResolver::{is_allowed, allows_url}` (SSRF guard) | A01–A03, C04 | B16, B7 (an Aeneas bump fixes B7) |
| `is_allowed_metadata_url` | A02, A03 | `url::Url`/`Host` model, B16, B2 |
| `origin_is_allowed`, `parse_allowed_origin` | T07, T08 | B2 (`trim_matches`, `strip_suffix`); `http::Uri` parsing |
| `host_is_allowed` | none (the S26 string-equality model) | B2 (`trim_matches`) |
| `should_ignore_notification`, `try_parse_with_compatibility` | T04–T06 (and C05, added here) | a `serde_json::Value` model |
| `bounded_sse_stream` | T01–T03, C01, C02 | `async`/`Pin` (outside Aeneas; C01/C02 are the contract) |
| client response routing (`service/client.rs`) | M01–M07, C03 | `async`, channels |
| task manager terminal-state transitions | M08 | `tokio` |
| `CreateMessageRequestParams::validate` | M09–M12 | B21 |

Phase 3 entry criterion (plan Section 23): a measured pilot on the then-current Aeneas release,
re-run against this table, before any target is committed to. Deferred (Section 25): the Aeneas
bump; upstreaming the Phase 2 models; specifications for the translatable Phase 1 non-targets
(`open`, `open_with`, `new`, `try_new`). Phase C proof refinement is done (2026-11-24).

**Human decisions (H1–H5 2026-11-23, run log of S20; H6–H7 2026-11-24, S24):**

| ID | Decision | State |
|---|---|---|
| H1 | One translated configuration with the widened feature list `request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth` | Accepted |
| H2 | 30 more Aeneas `toStr` native-code axioms for T05–T08, locked in `native-axioms.lock` at S29 | Accepted |
| H3 | Boundary tests from upstream tests and differential programs (the latter dropped 2026-11-23, plan Section 18 amendment); a test-only patch 02 only for an uncovered case, recorded (if created) as a further deviation from `docs/VERIFICATION.md` §4 under "Documents" | Accepted |
| H4 | `opaque` entry for the type `rmcp::transport::auth::AuthorizationManager` | Accepted |
| H5 | Project owner and budget | **Open**: TBD (human, 2026-11-23); spec owner named: Hoang Le Truong |
| H6 | Source of the T05/T06 method lists: union of the method names in the official MCP `schema.ts` of the five `KNOWN_VERSIONS` (22 requests, 12 notifications), since `2026-07-28` alone lacks `initialize`/`ping`. Core protocol only: extension methods (rmcp's `tasks/update`, `notifications/tasks`) are out of scope by design, not a bug; schema versions pinned (commit + sha256), list contents pinned by Lean regression checks, derivation reproduced by the command in `Defs.Methods`; a Tasks-extension list, if needed, is generated separately with capability-dependent handling checked; coverage claims say "core protocol", never "full MCP" | Decided (human, 2026-11-24, S24) |
| H7 | T05/T06 code form: "in the core list and not in `codeOmits`" (six names); the gap is a bug ("Bugs found"). `notifications/elicitation/response` is out of scope like the extension names | Decided (human, 2026-11-24, S24) |
| H8 | A01–A03: blocking all of `64:ff9b:1::/48` is intended; `240.0.0.0/4` (reserved, not blocked) is a bug ("Bugs found"); other special-purpose ranges outside the plan's lists, incl. `::ffff:0:0:0/96` (RFC 2765, obsoleted by RFC 6145), are a scope note | Decided (human, 2026-11-24, S25) |

**Owners:** spec owner Hoang Le Truong (named for Phase 2 on 2026-11-23); project owner and budget
TBD (H5, open by human decision 2026-11-23).

**Per-function status** (mirrors `functions/{M,T,A}*.yaml`; the records are authoritative). Every
record: `translation: LEAN_OK` (S21), `spec: REVIEWED` (S24/S25), `linkage: ORIGINAL` (pending the
S22 CI run; passes locally), `proof: CHECKED` (S28–S32).

| ID | Rust symbol | Line at `7caec76` |
|---|---|---|
| M01–M05 | `JsonRpcMessage::{into_request, into_response, into_notification, into_error, into_result}` | `model.rs:819, 825, 831, 837, 843` |
| M06, M07 | `NumberOrString::{numeric_string_value, matches_response_id}` | `model.rs:322, 330` |
| M08 | `TaskStatus::is_terminal` | `model/task.rs:38` |
| M09–M12 | `SamplingContent::{into_vec, is_empty, len, first}` | `model.rs:2926, 2934, 2942, 2958` |
| M13, M14 | `Reference::{as_prompt_name, as_resource_uri}` | `model.rs:3741, 3749` |
| T01–T03 | `SseEventSizeLimiter::{check_limit, finish_line, observe}` | `transport/common/client_side_sse.rs:90, 75, 48` |
| T04–T06 | `async_rw::{without_carriage_return, is_standard_notification, is_standard_method}` | `transport/async_rw.rs:385, 420, 396` |
| T07, T08 | `tower::default_port`, `tower::AllowedPort::matches` | `transport/streamable_http_server/tower.rs:1146, 1164` |
| A01–A03 | `AuthorizationManager::{embedded_ipv4, is_disallowed_metadata_ipv4, is_disallowed_metadata_ipv6}` | `transport/auth.rs:1359, 1343, 1370` |

**Incorporation of S24/S25 (2026-11-24; human request "move the approved specifications into the
project and remove the drafts", decided as "prove, then incorporate"):** the seven Phase 2 `Defs`
modules joined the `Defs` root; the deferred `Defs` items, approved by the spec owner at S24/S25 sign-off, were applied by an
`mcp-spec` agent, not by a prover (a `Defs.Net` check of the
6to4, IPv4-mapped and IPv4-compatible prefix edges; citations in `Defs/Sse.lean` and
`Defs/IntParse.lean`; the derivation-command wording in `Defs/Methods.lean`), and `Defs.Bytes` no
longer imports the trusted models (`Proofs.External.Utf8.utf8Bytes_eq_utf8`,
`Proofs.RequestState.strIs_iff_val_eq_utf8Bytes`). All 47 signed-off statements (M01–M14, T01–T08,
A01–A03, C01–C05 with their second forms and corollaries, the Section 16.1 joint lemmas and the S27
law `from_str_eq_parseI64`) were proved by four `mcp-lean` agents that drafted none of them (S28–S32),
with every statement copied verbatim from its draft (checked by script), and restated in
`Specs/Model.lean`, `Specs/Model/Task.lean`, `Specs/Transport/{AsyncRw, Auth}.lean`,
`Specs/Transport/Common/ClientSideSse.lean`, `Specs/Transport/StreamableHttpServer/Tower.lean` and
`Specs/External.lean` with `#guard_msgs` axiom checks; restated statements write the translated
functions with their full names (inside `theorem Theorems.<…>.f` a bare `f` names the restated
theorem). Axioms: `propext`, `Classical.choice`, `Quot.sound` only, plus for T05–T08 and C05 the 30
Aeneas `toStr` native-code axioms of the method-name and `http`/`https` literals (human decision
H2), added to `trusted/native-axioms.lock` after checking each literal. `formal/specs/Drafts/` was
removed. Full `lake build` (1771 jobs) and the four `lean-guard.sh` checks pass (native-code
axioms: 35 reached, 35 used and locked). Heartbeats raised only for A02 (1,600,000) and A01
(400,000). One independent `mcp-review` agent per batch reviewed the proofs, restatements, records
and the lock (each re-checked the statements against the drafts with its own script, and the lock
reviewer recomputed all 35 hashes); no blocking finding; the local findings were fixed, and the
proof-style ones (flexible tactics, iterator-helper duplication, proofs that unfold trusted model
bodies instead of using the S26 laws, splitting A02 to cut its ~65 s build) are deferred to phase C.

**Public request_state.rs API (started 2026-11-24, human request):** verify the 17 public functions
of `crates/rmcp/src/model/request_state.rs`. R01–R08 (`SealOptions::{new, associated_data, ttl}`,
`RequestStateCodec::{new, new_unchecked, try_new, open, open_with}`) are translated (linkage
`patch-01`); their statements (and an `open_with` corollary) passed two review rounds with no counterexample
and were signed off by the spec owner on 2026-11-24; all nine are proved
(`formal/proofs/Proofs/Model/RequestState/Public.lean`) and restated in the new public spec file
`formal/specs/Specs/Model/RequestState.lean` (full `lake build` and the four guards pass; one
independent proof review, no blocking finding). `open`/`open_with` are specified at the
clock reading (human decision 2026-11-24; review rule in `formal/README.md`, "Trusted base"). The
other nine (`new_with_keyring`, `with_rs1_signing`, `with_rs1_fallback`, `seal`, `seal_with`, and
the four JSON wrappers; R09–R17 once translated) are excluded today (B13, B4, B9); a translation
measurement on the pinned and the newest Aeneas is running. `Defs.Wire` and `Defs.CodecState` moved
back to `formal/specs/Defs/` for these public statements.
**Update (translation patch 03 v2, 2026-11-24; reviewed and signed off 2026-11-24; specs pending):** on Aeneas
`nightly-2026.11.24-fb44cb4` (base `deb8d84`) the human chose targets R09–R15 and variant A
("minimal Rust change"). With `formal/trusted/patches/03-request-state-public.patch` (+6/−2 Rust
lines) and the Charon-settings change ("Trusted base"), **R09–R15 translate** with real bodies:
`seal`, `seal_with`, `with_rs1_signing`, `with_rs1_fallback`, `open_json`, `open_json_with`,
`new_with_keyring` (and the private `seal_at`); 14 function and 2 type models and 3 `opaque`
constants were added, reviewed and signed off by the spec owner 2026-11-24. **Their specifications are not written yet** (no
statement, no sign-off, no proof; the clock rule now covers `seal`/`seal_with`, human decision
2026-11-24). **R16–R17 (`seal_json`, `seal_json_with`) stay excluded**, blocked upstream: Aeneas
does not support the mutually recursive trait declarations of `serde_core::ser` (minimal
reproducer kept outside the repository). The earlier patch 03 (R09–R12, on the old toolchain,
`stash@{0}`) is superseded.
**Update (R09–R15 specifications, 2026-11-25; incorporated, proofs checked):** the
statements of R09–R15 passed a spec cycle of 4 review rounds (2, 2, 2 and 1 independent
`mcp-review` reviewers; every finding fixed; a separate prover proved every round's statements
verbatim in scratch, `#print axioms` `[propext, Classical.choice, Quot.sound]`) and were signed off
by the spec owner (Hoang Le Truong) on 2026-11-25, together with the new definitions and the 12
patch-02 boundary tests. 12 statements: R09 `seal` and its corollary `seal_spec_of_length_le`;
R10 `seal_with` and its corollary `seal_with_spec_of_length_le`; R11 `with_rs1_signing`; R12
`with_rs1_fallback`; R13 `open_json`; R14 `open_json_with`; R15 `new_with_keyring` (with a proved
non-vacuity example); and three internal statements, R10a (the private `seal_at` at an explicit
time), R10b (`seal_at_roundtrip`: `seal_at` at `now` then `open_at` at `now'` returns the payload
under `CodecValid`, an rs1 seal-mode id that is an rs1 fallback, `SealFits` and an unexpired
token) and the `Defs` model round trip `openAt_eq_ok_of_sealAt_eq_some`. Public statements are
restated as `Theorems.request_state.RequestStateCodec.<fn>` in
`formal/specs/Specs/Model/RequestState.lean`; R10a, R10b and the model round trip in
`formal/proofs/Proofs/Internal/Model/RequestState.lean`. Decisions (spec owner 2026-11-25):
`seal`/`seal_with` are stated through the `Defs` model `sealAt` at `ExtModel.nowMs` (no statement
equates `seal_with` with the translated `seal_at`); the clock rule covers `open_json`/
`open_json_with` (review rule in `formal/README.md`, "Trusted base"); `Defs.RequestState` moves
unchanged to `formal/specs/Defs/`, and the new definitions (`sealAt`, `sealExpiry`, `tokenV1`/
`tokenV2`, `durationMillis`, `SealFits`, `CodecSealKeyKnown`, `KeyringFits`, `IterYields`,
`keyringScan`, `keyringCheck`, `KeyringFailure`, seven message texts) go into `Defs.CodecState`;
`CodecValid` is unchanged (the round trips keep the rs1 premise separate); no `_fail` companions.
R15 proves that every codec `new_with_keyring` returns satisfies `CodecValid`. Records
`formal/docs/functions/R09.yaml`–`R15.yaml` (spec `REVIEWED`; proof pending the build and the
lead's checks). With these, R16–R17 are the only public `request_state.rs` functions not covered.

**Readability rewrite of R01–R15 (2026-11-25; signed off by the spec owner and accepted by the
human owner 2026-11-25):** the
public spec file `formal/specs/Specs/Model/RequestState.lean` (18 theorems: R01–R15 and the
corollaries of R08, R09, R10) was rewritten for human readers without changing any statement's
meaning. Text changes: the module docstring (summary table first, with "Premises" and "Not
covered" columns; one glossary of premise keys and inherited exceptions, including the new key
(I), caller code with side effects outside its state, for R04–R06, R11, R12, R15; the clock rule;
provenance last); plain-English docstrings; readable binder names in place of generated ones;
and ten abbreviations appended to `Defs.CodecState` (`strBytes`, `FallbacksKnownForToken`,
`TranscriptV1Fits`, `TranscriptV2Fits`, `appendIfAbsent`, `IsInvalidKeyring`, `IsKeyTooShort`,
`entryBytes`, `ItemsConvert`, `mapErrDeserialization`), each with the replaced text as its body;
no existing definition changed. `formal/specs/README.md` gained key (I). Spec cycle: 5 rounds,
2 fresh independent `mcp-review` reviewers per round (round 1: 1 blocking docstring finding,
fixed; rounds 3–5 no blocking; round 5 both reviewers "ready for sign-off"). Spec-owner
decisions 2026-11-25: ID order and restated text differing from the spec theorems, both recorded
as exceptions in `docs/STYLE_GUIDE.md` "Spec Files"; optional round-5 wording polish deferred
(the (F) phrase "for Rust not to panic", the native-code history phrase, R15's caller-code
premise in the table and README, glossary lines for `rs1`/`rs2`, seal mode, `openAt`, `sealAt`,
`keyringCheck`, two wraps). Evidence that the meaning is unchanged: a scratch Lean file that
imports `Specs.Model.RequestState`, contains the 18 theorems of
`git show 8debe97:formal/specs/Specs/Model/RequestState.lean` with `Theorems.` renamed to
`SignedOff.` (same `open` lines), and checks for each pair
`example : type_of% @SignedOff.X = type_of% @Theorems.X := rfl` plus a command comparing the
binder kinds of the two types binder by binder; `cd formal && lake env lean <file>` exits 0 (18
`rfl`, 18 binder checks). Negative controls (e.g. `versionV1`→`versionV2` in R07, `≤` for `=` in
R06, append-always in R12, an implicit binder made explicit) fail, each at the mutated theorem;
every reviewer re-ran the check and built its own controls. Final validation (round 5): `lake
build --wfail` (3775 jobs), `lean-guard.sh` sources, build-log and axioms exit 0; all 18
`#print axioms` lists `[propext, Classical.choice, Quot.sound]`, unchanged. AI-drafted (mcp-spec)
and AI-reviewed (mcp-review), Claude Code, claude-opus-5-5. R16–R17 (`seal_json`,
`seal_json_with`) stay untranslated; issue record
`formal/trusted/issues/aeneas-serde-ser-mutual-traits.md`.

**Public and internal specifications (2026-11-24, human decision):** `formal/specs/` now holds only
the public rmcp API (functions `pub` in upstream rmcp): `Specs/Model.lean` (M01–M05, M09–M14, the
`_fail` companions, the Section 16.1 joint lemmas, C03) and `Specs/Model/Task.lean` (M08), with the
definitions they use (`Defs/{Bytes,IntParse,JsonRpc}.lean`) and `formal/specs/README.md`, a
one-page index of every guarantee in plain English. The statements about private, crate-internal
(M06, M07) and patch-only (W01–W15) functions and the model laws moved, unchanged, to
`formal/proofs/Proofs/Internal/<Rust path>.lean`, and the definitions only they use to
`formal/proofs/Proofs/Defs/` (Lean names unchanged). A script confirmed that all 185 restated
theorems, with their docstrings and `#print axioms` checks, are byte-identical (185 in all: 19
public, 166 internal); `scripts/lean_guard.py` allows `#guard_msgs` in `proofs/Proofs/Internal/`; records
(`spec_file`), board, plan Section 20 (amendment), `formal/README.md` and the guides updated.

**Phase C proof refinement (2026-11-24, both phases; plan Section 8 "Phase C"):** with every spec
statement frozen, the hand-written proofs were refined in two waves (`Proofs/External/*` first, then
four parallel groups) and one fix round: about 300 flexible tactic uses (`simp`, `simp_all`,
`simpa` without `only`, `norm_num`, `at *`) replaced, none kept; no `maxHeartbeats` left (A01 and
A02 no longer need them; `Proofs.Transport.Auth` builds in about 4.6 s instead of about 70 s); no
rewrite with generated equation lemmas; proofs that unfolded trusted model bodies now use the
signed-off laws (M06, M07, M10, M12, M13, M14, T04–T08, A01 and several Phase 1 proofs); duplicates
factored into shared lemmas (`Proofs/External/{Byte,WP}.lean` new; iterator `next` equations,
`Arc.data_val_inj`, `ok_or_eq`, `is_err_eq`, `Str…eq_eq`, `eq_i64_some_spec`, one shared E01 lemma
used by E09/E10). Human decision 2026-11-24: in phase C an axiom list may only shrink. Two did:
`Theorems.External.core.slice.Slice.first_spec` `[propext, Quot.sound]` → `[propext]`, and T01
`check_limit` `[propext, Classical.choice, Quot.sound]` → `[propext, Quot.sound]` (record updated).
`formal/trusted/` and `formal/translation/` unchanged; full `lake build` (1773 jobs) and the four
`lean-guard.sh` checks pass. Two independent `mcp-review` agents reviewed the refinement (no
blocking finding) and a third the fix round (no blocking finding).

**Human acceptance (2026-11-24):** the owner accepted the 18 steps that were waiting. S02, S04 and
S24–S33 are `ACCEPTED` (their acceptance criteria are met). S01 and S20 become `ACCEPTED` when H5
(project owner and budget) is named; S03, S04a, S21 and S22 when their CI runs pass (first push);
likewise S23 (after S21 and S22) and S34 (after S21), accepted earlier the same day. S24 and S25
depend on S20, whose only open item is H5; the owner accepted them regardless.

**S23 review (2026-11-24, at `3ded001`; two independent `mcp-review` agents, no blocking finding):**
the Charon settings, the `opaque` `AuthorizationManager` entry (H4), the widened configuration (H1)
and the Phase 2 external models (the S21 placeholders) were reviewed. Both reviewers ran
`scripts/check-original-linkage.sh` locally (exit 0: `Funs` 41/41, `Types` 27/27, templates 30/30
and 9/9 blocks identical; source tree and digests re-derived at `7caec76` and HEAD) and a full
re-translation in scratch, byte-identical to `formal/translation/`. The feature list, target and
overflow settings agree everywhere; no Phase 2 target depends on a feature outside the list (only
M06 `any(client, server)` and M07 `client`); the Phase 1 blocks are byte-identical to the pre-S21
translation (148/148). No Phase 2 target reaches an opaque crate or `AuthorizationManager`, and
`exclude` reaches nothing in Phase 2, so no statement is weakened. No placeholder remains (only the
five documented `opaque` constants; each external has a model with a cited source). Corrections
made: H4's reason (Charon/hax fails on the `Arc<dyn CredentialStore/StateStore>` fields, not Aeneas
on oauth2 aliases; plan Section 15 and H4; the `Cargo.toml` comment was corrected at S37: comments do not
reach the S22 pins, which hash the parsed manifest without the Charon table); the linkage script's description of its opaque check; stale STATUS, plan
Section 24 and record text. Conditional: S21 and S22 are not yet accepted (no CI run), so S23 can
be signed off only subject to their CI runs. **Signed off by the spec owner Hoang Le Truong on 2026-11-24**, subject to the
S21/S22 CI runs; S23 becomes `ACCEPTED` when both pass.

**Stated exceptions of the external models (complete list, S23):** inputs of `2^61` bytes or more
(size convention; includes HMAC's bit-length counter and a `Vec` above `isize::MAX`); allocation
failure; `Arc` `PartialEq` checks pointer equality first (`Rmcp/FunsExternal.lean`); `Ipv6Addr` is
stored as eight segments instead of sixteen octets (`TypesExternal.lean`); `MaybeUninit` partial
initialisation is not modelled; `Str` may hold non-UTF-8 bytes in the model and `push_str` of such
bytes is `fail undef`; `HashMap::get` assumes `Hash` and `Eq` agree; the clock `Utc::now` is opaque
(`nowMs`). None changes a result of the translated targets (the only `Arc` instance is `str`; the
other items are representation choices or unused by the targets).

**S25 spec cycle (2026-11-24):** drafts `formal/specs/Drafts/ClientSideSse.lean` (T01–T03, C01 with
its plan form, C02 with its prefix form) and `formal/specs/Drafts/Auth.lean` (A01–A03, C04 with a
corollary in `Defs.Net` terms), with `Defs/Sse.lean` (limiter model plus an independent description
from the WHATWG line rules, agreement checked on finite cases) and `Defs/Net.lean` (RFC prefixes);
both join the `Defs` root at incorporation. Four review rounds with two fresh `mcp-review` agents
each, three fix rounds; round 4 had no blocking or judgment finding. The reviewers proved every
statement in scratch against the translation (axioms `propext`, `Classical.choice`, `Quot.sound`),
compared the translated functions with the Defs on millions of inputs (0 differences) and ran
mutation tests on both Defs. Human decision H8; a bug recorded under "Bugs found" (`240.0.0.0/4`).
Signed off by the spec owner Hoang Le Truong on 2026-11-24. Deferred to incorporation: one more
`Defs.Net` check pinning the outer edges of `2002::/16`, `::ffff:0:0/96` and `::/96`; the citation
"lines 120–121" in `Defs/Sse.lean`. Candidate lemmas for S31/S32 are in plan Section 21.

**Mathlib naming batch (2026-11-24, human decision):** a read-only audit of the hand-written Lean
under `formal/` listed the names that break Mathlib conventions; the clear violations were renamed,
name only, with every statement, definition body and proof unchanged (checked by re-applying the
rename map to `99a2590` and diffing: only three re-wraps and one docstring rewording differ; full
`lake build` and the four `lean-guard.sh` checks pass; `#print axioms` output unchanged; one
independent `mcp-review` confirmed). Signed-off names renamed and **re-signed by the spec owner
Hoang Le Truong on 2026-11-24**: `NoRs1Fallback` → `noRs1Fallback`; C05
`notification_is_standard_method` → `is_standard_method_of_is_standard_notification`; C03
`into_result_consistent` → `into_result_eq`; `first_eq_head_into_vec` → `first_eq_head?_into_vec`;
`b64_alphabet` → `isSome_b64Val_of_mem_b64`; `b64Val_isSome_iff` → `isSome_b64Val_iff`;
`utf8_inj` → `utf8_injective`; `b64_ascii` → `val_lt_128_of_mem_b64`; `map_err_Ok`/`map_err_Err` →
`map_err_ok`/`map_err_err`; `RangeInclusive.contains_eq` → `contains_eq_match_le`;
`hmac_sha256_verify_wrong_length` → `hmac_sha256_verify_eq_ok_false_of_length_ne`;
`dot_not_mem_b64` → `dot_notMem_b64`. Helpers renamed: `isSome_b64Val_b64Sym`,
`ne_dot_of_mem_{versionV1,versionV2,b64}`, `and_65280_eq`, `isDigit`, `isDigit_of_mem_digitBytes`,
`takeWhile_isDigit_eq_self`, `val_cast_u64`. Kept as project conventions: `_spec`/`_fail`,
`_roundtrip`; acronyms are written as words (`docs/STYLE_GUIDE.md`, "Formatting").

**S24 spec cycle (2026-11-24):** drafts `formal/specs/Drafts/Model.lean` (M01–M14, the plan
Section 16.1 joint lemmas, C03, the S27 deferred law) and `formal/specs/Drafts/Transport.lean`
(T04–T08, C05), with `Defs/{Bytes,IntParse,JsonRpc,Methods,Tower}.lean` (not yet imported from
the `Defs` root; they join it at incorporation). Four review rounds with two fresh `mcp-review`
agents each and three fix rounds by fresh `mcp-spec` agents; round 4 had no blocking or judgment
finding. Checks done by the reviewers (scratch, not committed): every statement proved at least
once against the translation, with axioms `propext`, `Classical.choice`, `Quot.sound` and the H2
`toStr` side conditions only; `Defs.parseI64` against the trusted `i64FromAscii` (0 differences on
about 37,000 inputs) and against Rust `str::parse::<i64>` (30 boundary strings plus 11,111
strings, identical); T04–T08 on exhaustive small inputs; 13 mutations of the `Defs.Methods`
regression checks (all content changes fail the build). Human decisions H6 (amended) and H7;
a bug recorded under "Bugs found". Signed off by the spec owner Hoang Le Truong on 2026-11-24.
Deferred to incorporation: the `StrIs` ↔ `Defs.utf8Bytes` lemma; optionally moving the
`utf8Bytes = ExtModel.utf8` check from `Defs/Bytes.lean` to `Proofs/External/String.lean`; two
docstring nits (the derivation-command wording in `Defs/Methods.lean`, the citation
`mod.rs` 1592–1606 at `Defs/IntParse.lean` line 85).

**S22 linkage-check evidence (2026-11-24, local, macOS, on the S22 working tree; script as
reviewed in round 2):** `scripts/check-original-linkage.sh <scratch>` on the real tree: exit 0 —
part (a) passes (src tree `4efe696a…`, crates and manifest digests pinned), `Funs.lean` 41/41,
`Types.lean` 27/27, `FunsExternal_Template.lean` 30/30, `TypesExternal_Template.lean` 9/9 blocks
identical. In scratch clones of that tree with the change committed: (1a) `default_port` 443 → 444
in `tower.rs`: exit 1 at part (a) ("crates/rmcp/src at HEAD is tree 6ab32ce…, not the pinned
upstream tree"); (1b) `[lib] path = "src/lib.rs"` added to `crates/rmcp/Cargo.toml`: exit 1 at
part (a) (manifest digest differs); (2) translation patch `02-seeded-default-port.patch` (443 →
444) with `scripts/aeneas-translate.sh` regenerating the translation (exit 0, `444#u16` in
`Funs.lean`) and committed: exit 1 at part (b), "DIFFERS in committed Funs.lean:
transport.streamable_http_server.tower.default_port" (40/41). No log is committed; this paragraph
is the record. After review round 3 the script gained further guards (pinned SDK-side opaque/exclude
list, shadowing guard, stricter header rule). On the final script: the real tree passes (exit 0;
same block counts); a committed-only declaration `transport.async_rw.Str.Insts.CoreCmpPartialEqStr.eq`
injected into the committed `Funs.lean` fails (shadowing, exit 1); an extra opaque SDK entry
(`NumberOrString`'s `PartialEq` impl) fails at the rewrite (exit 1).

**S21 translation run (2026-11-23, local, macOS with `DYLD_FALLBACK_LIBRARY_PATH=/usr/lib`):**
`scripts/aeneas-translate.sh`, exit 0; Aeneas `nightly-2026.08.20-5d08da4`, Charon 0.1.235, Rust
`nightly-2026-06-01`; translated source: upstream `7caec76` plus patch 01 (`.llbc/work/`). All 50
targets defined; the 21 `_` globs each match one Rust item; no `sorry`; all 148 Phase 1 blocks of
`formal/translation/` (20 in `Types.lean`, 128 in `Funs.lean`) unchanged (the diff only adds
lines). Re-run after the review fixes: output byte-identical. `lake build` (1745 jobs) and
`lean-guard.sh` `sources`, `build-log`, `axioms`, `aeneas-archive` pass; the widened test build
(`$FEATURES,macros`) passes 801 library tests. The three workflows have not run on GitHub.

Board (2026-11-24, after the human acceptance above): S24–S33 `ACCEPTED`; S20, S21, S22, S23 and S34
`IN_PROGRESS`, accepted by the owner and waiting only for H5 (S20) or the first CI runs (S21, S22,
then S23 and S34); S35 and S36 `NOT_STARTED`; S37 `ACCEPTED` (results written and accepted 2026-11-24).

## Open items

Human decisions and actions:
- **Phase 2 owner and budget (H5)**: not named; blocks S20 acceptance and gate G1 (plan Section 21).
- **S31 candidate lemma (open, not a signed-off statement):** prove
  `∀ cap ≥ 1, Defs.Sse.observe cap (init m) h = historyOutcome cap m h` (checked only on finite
  cases in `Defs/Sse.lean`); a later "the stream rejects an oversize event" lemma needs it (plan
  Section 21, notes for S31/S32).
- **Report the H8 gap upstream** (S25, 2026-11-24): `240.0.0.0/4` not blocked by
  `is_disallowed_metadata_ipv4` ("Bugs found", Phase 2). Needs the owner's go-ahead.
- **Report the H7 gap upstream** (S24, 2026-11-24): the `async_rw` method lists miss six core MCP
  names ("Bugs found", Phase 2). Not reported yet; reporting is outward-facing and needs the
  owner's go-ahead.
- **`external_code` in `scripts/lean_guard.py`** (pre-existing, found in the S21 review): it does not
  treat guillemet identifiers `«…»` as one unit, so a `«"»` can shift its view of literals in
  `trusted/` for the rule against `rmcp`-namespace identifiers. The S21 exception for generated files
  does not lex at all (a sha256 + exact-line pin, `formal/trusted/translation-pins.txt`); fixing
  `external_code` is a follow-up.
- **Clippy with the widened features** fails on unused upstream helpers (`dead_code`); the guides
  keep clippy on `--features request-state` (S21 review).
- **Owners and budget**: project owner and budget TBD (blocks S01 acceptance and the D2 gate).
- **D2 fallback in use (human decision 2026-11-23)**: the refactor did not land in the SDK
  source; it is translation patch `formal/trusted/patches/01-request-state-wire.patch` on
  upstream `7caec76`, and every Phase 1 target's (W/E) linkage is `patch-01` (proved on upstream
  `7caec76` plus translation patch 01). The patch had the review of `docs/VERIFICATION.md` §4: two independent
  agent reviews (no blocking; a side-by-side run of upstream and the patched copy gave identical
  results on 2,463,458 cases) and the human sign-off on 2026-11-23. Landing the refactor upstream
  would let the patch be deleted and the targets become `ORIGINAL`. (Before 2026-11-23 this item
  read: not landed in the fork; results about local commit `f8fb6a7` / `aacfbf7`.)
- **S01–S04a acceptance**: `IN_PROGRESS` on the board; S02 lacks `CLAUDE.md` and its own review.
- **CI has never run on GitHub**: the three workflows (`lean-build.yml`,
  `aeneas-translation.yml`, `patched-tests.yml`) need a push; the last two were checked only
  locally on macOS (the CI-workflows evidence (git history at 223ff12)). S17 (each CI check shown to fail once on a
  throwaway branch) is `NOT_STARTED`.
- **`docs/VERIFICATION.md` Section 9 vs the CI workflows** (the guide is kept verbatim; human
  decision pending): it gives generic trigger paths including `Cargo.lock` (not committed here),
  runs the patched tests "with `register_tool`" (no Charon `rustc_args` here; patch 01 adds no
  tool attribute), and describes `lean-build` as `lake build --wfail` (deviation (1) above). Its Section 5 also says patches are applied "with `git apply`" in numeric order;
  `scripts/apply-patches.sh` uses `patch -p1 -F 0` in file-name (lexical) order.
- **Pilot artifacts and per-step evidence**: removed from the working tree on 2026-11-23 (human
  decision), together with the W-batch procedure; they remain in git history (last at commit
  `223ff12`: `formal/docs/evidence/`, `formal/docs/review/`). The pilot record (`formal/docs/pilot/`,
  `formal/docs/pilot.md`, whose logs contained local paths) was removed from git history on
  2026-11-23 (human decision).
- **No shared verification lockfile**: `Cargo.lock` is not committed (plan Section 4), so
  `aeneas-translation.yml` and `patched-tests.yml` each resolve and check their own (same code:
  `scripts/aeneas-translate.sh`, the test job through `--check-deps`, then `cargo test --locked`).
  Pinned crates (`PINNED_DEPS`) and sources (crates.io only) are identical by check; unpinned
  transitive crates could differ between the jobs. Committing a verification lockfile shared by
  both jobs is a human decision.
- **Mathlib oleans** fetched by `lake exe cache get` are not digest-checked (scope decision).
- **Upstream Aeneas `toStr` issue** (`Aeneas/Std/String.lean`): resolved upstream; the Aeneas
  upgrade of 2026-11-24 emptied `native-axioms.lock` (reviewed and re-signed by the spec owner 2026-11-24).

Accepted limits, still open (`formal/README.md`, "What CI checks"; the S03 evidence (git history at 223ff12)):
- S03 X4: `Specs` imports `Proofs`, so a global instance or notation in `proofs/` could change a
  spec statement's meaning; no structural fix decided. At `aacfbf7` a text search finds no
  `instance`, `notation` or infix declaration in `proofs/` or `trusted/` (the two `Decidable`
  instances are in `specs/Defs/`).
- S03 R5a-1: the word bans and allowlists of `lean-guard.sh sources` can be bypassed by gluing a
  banned token to a preceding literal or `)`.
- S03 R5a-2: `axioms.lock` locks referenced constants by name only (moot while it is empty).
- S08–S09 (R3a-1, R3a-2): nothing enforces that `RmcpExternal` imports only Aeneas and
  `Rmcp.Types` (at `aacfbf7` it does: `import Aeneas`, `import Rmcp.Types`), and global
  `notation`/`instance` in `trusted/` is not banned; a root-level name in `trusted/` could make a
  generated name ambiguous. Reviewers check these by hand.
- External models are not covered by any lock: a hash lock over the declarations of
  `RmcpExternal` was offered at the S08/S09 sign-off and not adopted (deferred).

Documents:
- **Test-only patch 02 (H3, human decision 2026-11-24, S34):** `formal/trusted/patches/02-phase2-tests.patch`
  adds 34 `#[cfg(test)]` tests for the plan Section 22 boundary cases no upstream test covers. It is
  a further deviation from `docs/VERIFICATION.md` §4, which defines translation patches as
  behaviour-preserving edits that make an item translate: patch 02 changes no translated item (the
  re-translation with it is byte-identical) and exists only as test evidence, run by
  `patched-tests.yml`. The repository's SDK `*.rs` files stay unchanged. S34 (all 141 Section 22
  boundary cases covered: 37 by upstream tests, 96 uncovered and 8 partial by patch 02; 835 tests
  pass; reviewed by two agents, a third pass after the fix round) was accepted by the human owner
  on 2026-11-24, effective when S21 passes CI. **Extended 2026-11-25** (human decision in the
  R09–R15 spec cycle; findings sR2-a-2, sR2-b-4, sR3-a-3; signed off by the spec owner
  2026-11-25 with the R09–R15 statements): 12 more `#[cfg(test)]` tests in a new
  `mod public_api_boundaries` of `request_state.rs`'s test module (expiry edges of `seal_at`,
  its rs1-keyring round trip, the exact `InvalidKeyring`/`KeyTooShort` errors and fault order of
  `new_with_keyring`, the messages and fallback lists of `with_rs1_signing`/`with_rs1_fallback`;
  list in `formal/trusted/evidence/README.md`). Patch 02 now adds 46 tests (34 + 12); 847 library
  tests pass on the copy with patches 01–03 and with 01–02; the re-translation stays
  byte-identical; one review (25 of 28 mutants caught, the 3 survivors killed by the fix round).
- `docs/VERIFICATION.md` (kept verbatim) also differs, from 2026-11-24, in what an auditor reads:
  its §7 says `formal/specs/` and not `formal/proofs/`; the statements about private,
  crate-internal and patch-only functions and the model laws are now in
  `formal/proofs/Proofs/Internal/` with their definitions in `formal/proofs/Proofs/Defs/`, which an
  auditor reads too (plan Sections 4 and 20 amendment; human decision 2026-11-24).
- `docs/VERIFICATION.md` differs from the project's design in nine documented places (build
  gate, `#guard_msgs` form, generated root module, reading `proofs/`, `globs`, native-code
  axioms, externals as definitions (amended), `theorem Theorems.…` instead of `recall`, and,
  from Phase 2, one proof file per Rust type or module instead of per item (plan Section 20,
  `docs/STYLE_GUIDE.md`)).
- Docs-sync round 3 (2026-11-22) left ten wording items open; at `aacfbf7` items (7) base64
  `0.23.x` and (8) `b64_decode` no longer appear in the guides; the others were not re-checked.
- The guides do not describe the `sources` attribute and `#`-command allowlists or the
  `lean-guard.sh fresh` step (text search at `aacfbf7`).

Deferred proof and record polish (phase C, plan Section 12; no statement change):
- Phase B proofs use flexible tactics (`simp`, `simp_all`, `step*`, `scalar_tac`, `nlinarith`,
  `omega`); duplicated proof text (S13); reuse `(hmacSha256 k m).property` for
  `length_hmacSha256` and one-line docstrings on three helpers (S15).
- `Proofs/External/Iter.lean` is outside the plan's S13 file list (record it or move it into
  `Std.lean`); four proof-file docstrings shorter than the signed-off ones (S13).
- `Rmcp` and `RmcpExternal` are not default targets (they are audited through the imports of
  `Proofs`); making them default targets is a `lakefile.toml` change by the lead.

Deferred scope:
- Negative round trips (tampered token or other key → `IntegrityCheckFailed`): provable only
  under a no-collision premise on the opaque HMAC model (S15, decided 2026-11-23: deferred).
- Specifications for `open`, `open_with`, `new`, `try_new`; the remaining plan Section 12 items.
  Next-sprint scope: the S19 evidence (git history at 223ff12).

## Incident

During the S03 fix-round-3 tests, an agent's test run started `rsync -a --delete` with `/` as
its destination; it ran for about three minutes before it was killed. Every unlink failed and
no deletion was found afterwards. The output-directory check now refuses `/`, a second guard
runs before `rsync --delete`, `RMCP_LLBC_DIR` is guarded (fix round 4, V3), and the agent role
files (`.claude/agents/*.md`, local only since 2026-11-23, "Safety") restrict destructive commands to scratch directories.
Details: the S03 evidence (git history at 223ff12), "U6: output directory".

[plan]: ../../docs/MCP_SDK_Verification_Master_Plan_EN.md
