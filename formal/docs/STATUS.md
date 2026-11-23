# Request-State Verification — Status

Plan: [`docs/MCP_SDK_Verification_Master_Plan_EN.md`][plan].
Task state: [`board.yaml`](board.yaml) (authoritative). Per-function records:
[`functions/`](functions/). Step evidence: [`evidence/`](evidence/); this report's evidence:
[`evidence/S19.md`](evidence/S19.md).

Last updated 2026-11-23: S19 final status report, written at local commit `aaf997d` (branch
`docs/verification-guides`, not pushed). S19 itself awaits acceptance by the human owner.

Board at this report: S05–S16 and S18 `ACCEPTED` (human approval 2026-11-23); S01, S02, S03, S04
and S04a `IN_PROGRESS` (human items open, see "Open items"); S17 `NOT_STARTED` (needs a push to
GitHub); S19 is this report.

## Results

Plan Section 11 template, filled with the actual results. Three deviations from the template's
wording, each forced by a recorded fact: the SDK commit is a local commit, not a pinned fork commit
(the refactor has not landed); the external contracts are models (definitions, structures and
`opaque` constants), not axioms (human decision 2026-11-23); five native-code axioms are added to
the trusted base. No target is open, so the last sentence names the excluded functions and
non-targets instead.

> At SDK commit `14d2830f57f2841367a83501d0c272cf3514c4b4` (a **local commit** on branch
> `docs/verification-guides`; **not yet a pinned fork commit**, because the refactor PR has not
> landed in the fork; the non-test source of both target files is unchanged up to `aaf997d`),
> translated for `x86_64-unknown-linux-gnu` with `--no-default-features --features request-state`
> (and the Charon settings committed at `adce319`), the following public request-state wire
> functions and existing codec functions are verified against the Aeneas translation
> (`nightly-2026.08.20-5d08da4`): W01 `b64_len`, W02 `key_length_ok`, W03 `check_kid_len`,
> W04 `bytes_eq`, W05 `next_dot`, W06 `component_count`, W07 `version_of`, W08 `parse_rs1`,
> W09 `parse_rs2`, W10 `transcript_v1`, W11 `transcript_v2`, W12 `decode_expiry`,
> W13 `is_expired`, W14 `open_frame`, W15 `frame` (module `request_state_wire`); E01
> `open_authenticated_body`, E02 `b64_len`, E03 `validate_key_length`, E04
> `validate_config_kid`, E07 `seal_rs1`, E08 `seal_rs2`, E09 `open_rs1_at`, E09a
> `rs1_fallbacks_verify`, E10 `open_rs2_at`, E11 `open_at` (`RequestStateCodec`); and the
> composition theorems `frame_roundtrip`, `rs1_roundtrip`, `rs2_roundtrip`,
> `open_at_roundtrip_rs1`, `open_at_roundtrip_rs2`. These results rest on the trusted base listed
> in `formal/README.md` and `STATUS.md`: Charon, Aeneas and Lean; the translated configuration;
> the HMAC-SHA256, Base64url and standard-library models in `formal/trusted/` (definitions,
> structures and four `opaque` constants; no trusted axiom); the five Aeneas `toStr` native-code
> axioms locked in `formal/trusted/native-axioms.lock`; the codec-state hypothesis; the
> statements in `formal/specs/`; and the exclusions. They do not establish cryptographic
> security, constant-time execution, or correctness of the public codec wrappers. No target is
> open; the functions not listed are excluded (Section 2.3, "Excluded functions" below) or are
> translatable non-targets (`open`, `open_with`, `new`, `try_new`).

**D10 count (plan Section 8, "Gates").** Of the 25 targets: **verified 25**, **checked but
patched 0**, **open 0**. "Verified" means spec `REVIEWED` (signed off by the spec owner), proof
`CHECKED` and linkage `ORIGINAL` in every record of `functions/`, with the restated theorem in a
spec file; each theorem holds under its stated premises (no-overflow and size domains, codec-state
clauses). Qualification: linkage is `ORIGINAL` with respect to the local commit above; it becomes
a claim about a fork commit only when the refactor lands and the pinned commit is recorded
(S04a, open). Plus 5 composition theorems. Excluded (not counted, not verified): the items
under "Excluded functions" below. Not targets: 4 translatable wrappers.

Restated theorems (`theorem Theorems.…`, each proved by the spec theorem it restates and guarded
by `#guard_msgs in` + `#print axioms`), counted at `aaf997d`:

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
| Pinned commit | **not yet**: the refactor PR (S04a part 1) has not landed in the fork |
| Verified Rust source | local commit `14d2830` (refactor); non-test lines unchanged at `aaf997d` |
| Translation | committed at `adce319` (from `14d2830` + Charon settings); unchanged since |
| Aeneas | release tag `nightly-2026.08.20-5d08da4` ([`evidence/S03.md`](evidence/S03.md)) |

SHA-256 of the target files at `14d2830`: `request_state.rs` `a09f02e3…f076`,
`request_state_wire.rs` `96f433d7…c357`. Since then the files changed only by the S16 test
insertions inside `mod tests` (`790b75e`; `git diff -U0 14d2830 aaf997d` shows two insertion-only
hunks, after line 735 resp. 280), and `crates/rmcp/Cargo.toml` only in comments and the
derived-`Debug` `exclude` entries (`adce319`, `e410368`). The committed translation was reproduced
byte for byte on a fresh clone at `5ea289a` ([`evidence/S18.md`](evidence/S18.md)).

Target files (both compile only with the `request-state` feature):
- `crates/rmcp/src/model/request_state_wire.rs` (new, public; added by the S04a refactor)
- `crates/rmcp/src/model/request_state.rs` (refactored onto it at S04a)

## Translated configuration

Single target, fixed in `scripts/aeneas-translate.sh` (S03):

```
--target x86_64-unknown-linux-gnu --no-default-features --features request-state --lib
--config profile.dev.overflow-checks=true --config profile.dev.debug-assertions=true
```

Charon settings: `[package.metadata.charon]` in `crates/rmcp/Cargo.toml` (`start_from`,
`exclude`, `opaque`), committed. Dependency pins (`PINNED_DEPS`): `hmac 0.13.0`, `sha2 0.11.1`,
`base64 0.23.1`, `digest 0.11.3`, `zeroize 1.9.2`, `chrono 0.4.45`, `serde_json 1.0.154`.
**No translation patch** (no `formal/trusted/patches/` directory exists) and **no hand edit** of the
generated files (`formal/translation/` is reproduced byte for byte by the translate script,
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

Claims apply to the commit and configuration above only, not to upstream releases.

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

Mirrors `formal/docs/functions/*.yaml` (the records are authoritative), checked at `aaf997d`:
every record has `translation: LEAN_OK`, `spec: REVIEWED`, `spec_owner: "Hoang Le Truong"`,
`linkage: ORIGINAL`, `proof: CHECKED`.

| ID | Rust symbol | translation | spec | linkage | proof |
|---|---|---|---|---|---|
| W01 | `request_state_wire::b64_len` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| W02 | `request_state_wire::key_length_ok` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| W03 | `request_state_wire::check_kid_len` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| W04 | `request_state_wire::bytes_eq` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| W05 | `request_state_wire::next_dot` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| W06 | `request_state_wire::component_count` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| W07 | `request_state_wire::version_of` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| W08 | `request_state_wire::parse_rs1` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| W09 | `request_state_wire::parse_rs2` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| W10 | `request_state_wire::transcript_v1` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| W11 | `request_state_wire::transcript_v2` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| W12 | `request_state_wire::decode_expiry` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| W13 | `request_state_wire::is_expired` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| W14 | `request_state_wire::open_frame` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| W15 | `request_state_wire::frame` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| E01 | `RequestStateCodec::open_authenticated_body` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| E02 | `RequestStateCodec::b64_len` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| E03 | `RequestStateCodec::validate_key_length` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| E04 | `RequestStateCodec::validate_config_kid` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| E07 | `RequestStateCodec::seal_rs1` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| E08 | `RequestStateCodec::seal_rs2` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| E09 | `RequestStateCodec::open_rs1_at` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| E09a | `RequestStateCodec::rs1_fallbacks_verify` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| E10 | `RequestStateCodec::open_rs2_at` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |
| E11 | `RequestStateCodec::open_at` | LEAN_OK | REVIEWED | ORIGINAL | CHECKED |

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
  `SealOptions`: not a blocker; they depend on `Aeneas.Std.core.fmt.Formatter` and native-code
  string axioms, and no target uses them (human decision 2026-11-22); `exclude`.
- `seal_json`, `seal_json_with`, `open_json`, `open_json_with`, `Error` for `RequestStateError`:
  B9, `serde` signatures, `Error::source` not modelled; `exclude`.
- crates `serde`, `serde_core` (crate level): B9; only the excluded JSON wrappers use them.

Consequences (plan Section 2.3): the round-trip theorems compose E07/E08 with E09–E11
directly, with no seal wrapper verified; the codec-state invariant is permanently a hypothesis;
`open`, `open_with`, `new` and `try_new` translate but are not targets.

## Trusted base

Checked at `aaf997d` by `scripts/lean-guard.sh axioms` (exit 0; 2110 constants in 46 project
modules; kernel replay of 2107 constants accepted, 3 unsafe/partial skipped):

- **Trusted axioms: 0.** `formal/trusted/axioms.lock` has no entry; the `RmcpExternal` roots
  declare no axiom (human decision 2026-11-23). Allowed builtins: `propext`, `Classical.choice`,
  `Quot.sound`.
- **Native-code axioms: 5**, all reached, used and locked in `formal/trusted/native-axioms.lock`:
  the Aeneas `toStr` side conditions of the string literals `VERSION_V1` ("rs1"), `VERSION_V2`
  ("rs2"), `KID_EMPTY_MSG`, `KID_TOO_LONG_MSG` and the `expect` message of
  `rs1_fallbacks_verify` (separate trust class, human decision 2026-11-22). Each side condition
  also has a kernel proof, so an upstream Aeneas `toStr` fix would remove them (open item).
- **External models** (accepted at S08/S09, human approval 2026-11-23; in use by the proofs): the
  41 placeholder externals of S04a part 2 are replaced by definitions (functions) and structures
  (types) with the generated names; what cannot be computed is one of exactly four `opaque`
  constants: `ExtModel.hmacSha256`, `ExtModel.sipHash13`, `ExtModel.nowMs`,
  `ExtModel.SerdeJsonErrorImpl`. They add no axiom and do not appear in `#print axioms` or the
  locks: a change to a model is caught only by review of `formal/trusted/`. Their 72 laws are
  proved (`Proofs/External/`) and restated in `Specs/External.lean`.
- **Codec-state hypothesis** (accepted at S12): `Defs/CodecState.lean` defines `CodecValid`
  (keyring clauses; single-key codecs unconstrained; pairwise distinct key ids),
  `CodecFallbacksKnown` (every rs1 fallback id is a key id) and `FallbacksKnown`. It is a
  hypothesis of the statements, not an axiom: E09, E11 and the rs1 round trips assume
  `CodecFallbacksKnown`, E09a `FallbacksKnown`, E10 and rs2 nothing. `CodecValid` implies
  `CodecFallbacksKnown`. The excluded constructors are what establish it in Rust; they are not
  verified.
- **Tools:** Charon `0.1.235` and Aeneas (`nightly-2026.08.20-5d08da4`), Lean `v4.31.0` kernel,
  prebuilt Aeneas Lean library (archive sha256 checked) and Mathlib oleans (not digest-checked).
- **Configuration:** the translated configuration above. **Patches:** none. **Hand edits of the
  translation:** none. **Exclusions:** the list above (plan Section 2.3).
- **Statements:** `formal/specs/Defs/` and `formal/specs/Specs/`.

External models (plan Section 4), in `formal/trusted/Rmcp/FunsExternal.lean` and
`TypesExternal.lean`; sources and tests per model in `formal/trusted/evidence/README.md`:

| Contract | Model (no axiom) | Status |
|---|---|---|
| HMAC (`prim.hmac_sha256`, `_verify`) | `ok (hmacSha256 k m)`, `ok (t = …)` | accepted (S08) |
| Base64url, no padding (`prim.b64_*`) | `ExtModel.b64`, `ExtModel.b64Decode` | accepted (S08) |
| Standard library | definitions and structures (list below) | accepted (S09) |
| `zeroize` | `Zeroizing::new`, `Clone`, `Deref`; `Zeroize` impls | accepted (S09) |
| Clock (`now_ms`, opaque) | `ok nowMs`, `opaque ExtModel.nowMs` | accepted (S09) |
| `serde_json::Error` (type) | structure, `opaque ExtModel.SerdeJsonErrorImpl` | accepted (S09) |
| Codec state | `Defs.CodecState` hypotheses (above) | accepted (S12) |

Details:
- HMAC: both functions always succeed. Stated exception: the SHA-256 bit-length `u64` counter
  (`sha2-0.11.1/src/block_api.rs` line 66) overflows for a message of at least `2^61 − 64` bytes
  or a key of at least `2^61` bytes; not modelled (the `x86_64` address space is at most `2^57`
  bytes).
- Base64url: strict decoding; round trip, canonicity, URL-safe alphabet (no `.`) and length laws
  proved (`Proofs/External/Base64.lean`); differential check against `base64 0.23.1`: 25,682,976
  comparisons, 0 mismatches (S18 re-run with the differential toolchain pinned to Rust 1.96).
- Standard library: `Borrow::borrow` (blanket), `Option::ok_or`, `Option` `Default`,
  `Result::is_err`, `Result::map_err`, `&[T]` `Default`, `str::len`, `str::as_bytes`,
  `String::{with_capacity, push_str, push, as_bytes, from_utf8}`, `String` `PartialEq::eq`,
  `Eq::assert_fields_are_eq`, `Clone`, `Hash::hash`, `Vec::is_empty`, `RandomState` `Clone` and
  `build_hasher`, `DefaultHasher` `write` and `finish`, `HashMap::get` (first entry with an equal
  key, no hashing), `HashMap` `Clone`; structures `Duration`, `FromUtf8Error`, `HashMap`
  (association list), `RandomState`, `DefaultHasher` (with `opaque ExtModel.sipHash13`).
- Clock: environmental assumption, not modelled: `Utc::now` panics if the clock is before 1970
  or outside chrono's range.
- Allocation failure is not modelled: `ok` from a `String`/`Vec` model means "returns, or aborts
  or panics for memory reasons".

Review rules that stay in force:
- **Clock.** `nowMs` is one constant, so every reader of the clock is pure in the model. No spec
  statement mentions the functions `rmcp.model.request_state.RequestStateCodec.now_ms`,
  `…RequestStateCodec.open` or `…RequestStateCodec.open_with` (a variable named `now_ms`, such
  as the time parameter of E01, is not covered); opening is specified through `open_at`.
- **`HashMap::get`.** Faithful for `Hash`/`Eq` instances that agree and do not fail (only
  `K = Q = String` occurs).

Opaque items (Charon `opaque` setting in `crates/rmcp/Cargo.toml`, committed):
`rmcp::model::request_state_wire::prim` (wraps the HMAC and base64 `Engine` types, B1, B3),
`rmcp::model::request_state::_::now_ms` (system clock; used only by non-target wrappers), and
the external crates `zeroize`, `base64`, `hmac`, `sha2`, `thiserror`, `chrono`, `serde_json`
(signatures only). Marking an item opaque only keeps its signature; its contract is the model
above.

## Bugs found

**Rust code: no bug found in the 25 verified functions** within the stated scope (the
translated configuration, the external models and their stated exceptions, the codec-state
hypothesis). No proof needed a patch or a change of production code, and no differential or
test run found a disagreement (S13: 125,664 + 12,160 + 216 differential cases, 0
disagreements on inputs satisfying the hypotheses; S04a: about 2.9M `open` calls base vs
refactor, no difference; S16: 95 request-state tests pass, 8 hand-made mutants each caught).
Behaviours recorded as facts, not bugs: a single-key codec built with `new_unchecked` or the
deprecated `new` accepts a key of any length (only `try_new` checks it); and
`rs1_fallbacks_verify` panics (`expect`) if an rs1 fallback id is not a key, which the excluded
keyring constructors prevent (not verified).

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
   a fresh clone could not run it. **Fixed** in `9e584e2` (lock tracked).
5. The differential check was built with whatever Rust toolchain rustup selected. Found at S18
   (F4). **Fixed**: `rdiff/rust-toolchain.toml` pins Rust 1.96 (`aaf997d`).
6. `formal/README.md` status line was stale ("S03: toolchain only"). Found at S18 (F1).
   **Fixed** in `aaf997d`.
7. The macOS Aeneas release bundle links `/nix/store` libraries, so its binaries do not start on
   a plain Mac. Found at S03. **Worked around** (`DYLD_FALLBACK_LIBRARY_PATH=/usr/lib`); not
   reported upstream.
8. Aeneas `toStr` discharges its side condition with `decide +native` although a kernel proof
   exists, adding the five native-code axioms. Found at S03/S04a. **Open** (upstream issue to be
   filed by a human).
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
    only `.github/workflows/lean-build.yml` exists. `aeneas-translation.yml` and `patched-tests.yml`
    were never written. Found at S19. **Open** (S04a part 2, S17).

Items 1–3 are in the plan text the specifications were checked against, not in the Rust code.

## Open items

Human decisions and actions:
- **Owners and budget**: project owner and budget TBD (blocks S01 acceptance and the D2 gate).
- **Refactor PR (S04a part 1)**: not landed in the fork; no pinned commit. Until it lands, every
  result is about local commit `14d2830` (source) / `aaf997d` (proofs). If it is not landed, the
  D2 fallback (refactor as a translation patch, every target `PATCHED`) applies.
- **S01–S04a acceptance**: `IN_PROGRESS` on the board; S02 lacks `CLAUDE.md` and its own review.
- **CI has never run on GitHub**: `.github/workflows/lean-build.yml` needs a push; the
  translation and patched-tests workflows of S04a (`aeneas-translation.yml`,
  `patched-tests.yml`) do not exist yet. S17 (each CI check shown to fail once on a throwaway
  branch) is `NOT_STARTED`.
- **Pilot artifacts** (`formal/docs/pilot/`): copied logs contain absolute local paths with the
  macOS username; total size about 1.2 MB. A human decides before any push.
- **Mathlib oleans** fetched by `lake exe cache get` are not digest-checked (scope decision).
- **Upstream Aeneas `toStr` issue** (`Aeneas/Std/String.lean`): to be filed by a human; after a
  fix and a rev bump, `native-axioms.lock` can be emptied.

Accepted limits, still open (`formal/README.md`, "What CI checks"; `evidence/S03.md`):
- S03 X4: `Specs` imports `Proofs`, so a global instance or notation in `proofs/` could change a
  spec statement's meaning; no structural fix decided. At `aaf997d` a text search finds no
  `instance`, `notation` or infix declaration in `proofs/` or `trusted/` (the two `Decidable`
  instances are in `specs/Defs/`).
- S03 R5a-1: the word bans and allowlists of `lean-guard.sh sources` can be bypassed by gluing a
  banned token to a preceding literal or `)`.
- S03 R5a-2: `axioms.lock` locks referenced constants by name only (moot while it is empty).
- S08–S09 (R3a-1, R3a-2): nothing enforces that `RmcpExternal` imports only Aeneas and
  `Rmcp.Types` (at `aaf997d` it does: `import Aeneas`, `import Rmcp.Types`), and global
  `notation`/`instance` in `trusted/` is not banned; a root-level name in `trusted/` could make a
  generated name ambiguous. Reviewers check these by hand.
- External models are not covered by any lock: a hash lock over the declarations of
  `RmcpExternal` was offered at the S08/S09 sign-off and not adopted (deferred).

Documents:
- `docs/VERIFICATION.md` differs from the project's design in eight documented places (build
  gate, `#guard_msgs` form, generated root module, reading `proofs/`, `globs`, native-code
  axioms, externals as definitions (amended), `theorem Theorems.…` instead of `recall`).
- Docs-sync round 3 (2026-11-22) left ten wording items open; at `aaf997d` items (7) base64
  `0.23.x` and (8) `b64_decode` no longer appear in the guides; the others were not re-checked.
- The guides do not describe the `sources` attribute and `#`-command allowlists or the
  `lean-guard.sh fresh` step (text search at `aaf997d`).

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
  Next-sprint scope: [`evidence/S19.md`](evidence/S19.md).

## Incident

During the S03 fix-round-3 tests, an agent's test run started `rsync -a --delete` with `/` as
its destination; it ran for about three minutes before it was killed. Every unlink failed and
no deletion was found afterwards. The output-directory check now refuses `/`, a second guard
runs before `rsync --delete`, `RMCP_LLBC_DIR` is guarded (fix round 4, V3), and the agent role
files (`.claude/agents/*.md`, "Safety") restrict destructive commands to scratch directories.
Details: [`evidence/S03.md`](evidence/S03.md), "U6: output directory".

[plan]: ../../docs/MCP_SDK_Verification_Master_Plan_EN.md
