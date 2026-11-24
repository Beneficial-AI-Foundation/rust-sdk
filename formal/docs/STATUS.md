# MCP SDK Verification — Status

Plan: [`docs/MCP_SDK_Verification_Master_Plan_EN.md`][plan].
Task state: [`board.yaml`](board.yaml) (authoritative). Per-function records:
[`functions/`](functions/). Step evidence: [`evidence/`](evidence/); this report's evidence:
the S19 evidence (git history at 223ff12).

Last updated 2026-11-23: S19 final status report, written at local commit `aacfbf7` (branch
`docs/verification-guides`, not pushed). S19 was accepted by the human owner on 2026-11-23 (`board.yaml`).
Updated 2026-11-23 for the D2 fallback (human decision 2026-11-23): the SDK `*.rs` files are
byte-identical to upstream `origin/main` (`7caec76`); the `request_state_wire` refactor and all
added tests are translation patch `formal/trusted/patches/01-request-state-wire.patch`, applied
only to the translated copy; every Phase 1 target's (W/E) linkage is `patch-01` (proved on upstream
`7caec76` plus translation patch 01). The translation and all 25 proofs are unchanged.

Board at this report: S05–S16 and S18 `ACCEPTED` (human approval 2026-11-23); S01, S02, S03, S04
and S04a `IN_PROGRESS` (human items open, see "Open items"); S17 `NOT_STARTED` (needs a push to
GitHub); S19 is this report.

Updated 2026-11-23 for **Phase 2** (plan Part II, Sections 13–25): S20 started; human decisions
H1–H4 accepted, H5 (owner and budget) open; 25 Phase 2 records added; board tasks S20–S37 added.
See "Phase 2" below. Nothing about the Phase 1 results changes.

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
> for `x86_64-unknown-linux-gnu` with `--no-default-features --features request-state` (and the
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
the items under "Excluded functions" below. Not targets: 4 translatable wrappers.

Restated theorems (`theorem Theorems.…`, each proved by the spec theorem it restates and guarded
by `#guard_msgs in` + `#print axioms`), counted at `aacfbf7`:

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
| Verified Rust source | the patched copy (`7caec76` + patch 01); its non-test lines equal those of `f8fb6a7`, so line numbers are unchanged |
| Translation | committed at `9bd8144` (from `f8fb6a7` + Charon settings); reproduced byte for byte through the patch path (2026-11-23) |
| Aeneas | release tag `nightly-2026.08.20-5d08da4` (the S03 evidence (git history at 223ff12)) |

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
`opaque`), committed (they name `request_state_wire`, which exists only in the patched copy).
Dependency pins (`PINNED_DEPS`): `hmac 0.13.0`, `sha2 0.11.1`, `base64 0.23.1`, `digest 0.11.3`,
`zeroize 1.9.2`, `chrono 0.4.45`, `serde_json 1.0.154`, checked since S21 on rmcp's own edges in the
translated configuration (human decision 2026-11-23; other versions used only by other crates,
e.g. `oauth2`'s `sha2 0.10.9`, are allowed). **One translation patch**,
`formal/trusted/patches/01-request-state-wire.patch` (D2 fallback, 2026-11-23), and **no hand edit**
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
  `SealOptions`: not a blocker; they depend on `Aeneas.Std.core.fmt.Formatter` and native-code
  string axioms, and no target uses them (human decision 2026-11-22); `exclude`.
- `seal_json`, `seal_json_with`, `open_json`, `open_json_with`, `Error` for `RequestStateError`:
  B9, `serde` signatures, `Error::source` not modelled; `exclude`.
- crates `serde`, `serde_core` (crate level): B9; only the excluded JSON wrappers use them.

Consequences (plan Section 2.3): the round-trip theorems compose E07/E08 with E09–E11
directly, with no seal wrapper verified; the codec-state invariant is permanently a hypothesis;
`open`, `open_with`, `new` and `try_new` translate but are not targets.

## Trusted base

Checked at `aacfbf7` by `scripts/lean-guard.sh axioms` (exit 0; 2110 constants in 46 project
modules; kernel replay of 2107 constants accepted, 3 unsafe/partial skipped):

- **Trusted axioms: 0.** `formal/trusted/axioms.lock` has no entry; the `RmcpExternal` roots
  declare no axiom (human decision 2026-11-23). Allowed builtins: `propext`, `Classical.choice`,
  `Quot.sound`.
- **Native-code axioms: 35**, all reached, used and locked in `formal/trusted/native-axioms.lock`
  (separate trust class, human decision 2026-11-22). Phase 1 (5): the Aeneas `toStr` side
  conditions of the string literals `VERSION_V1` ("rs1"), `VERSION_V2` ("rs2"), `KID_EMPTY_MSG`,
  `KID_TOO_LONG_MSG` and the `expect` message of `rs1_fallbacks_verify`. Phase 2 (30, human
  decision H2, locked 2026-11-24 at S29): the 18 request and 10 notification method-name literals
  of `async_rw.rs` (`is_standard_method` lines 399–416, `is_standard_notification` lines 423–432)
  and `"http"`/`"https"` of `tower.rs` `default_port` (lines 1148–1149), used by T05–T08 and C05. Each side condition
  also has a kernel proof, so an upstream Aeneas `toStr` fix would remove them (open item).
- **External models** (accepted at S08/S09, human approval 2026-11-23; in use by the proofs): the
  41 placeholder externals of S04a part 2 are replaced by definitions (functions) and structures
  (types) with the generated names; what cannot be computed is one of exactly four `opaque`
  constants: `ExtModel.hmacSha256`, `ExtModel.sipHash13`, `ExtModel.nowMs`,
  `ExtModel.SerdeJsonErrorImpl` (Phase 1; S26/S27 add a fifth, see below). They add no axiom and do not appear in `#print axioms` or the
  locks: a change to a model is caught only by review of `formal/trusted/`. Their 72 laws are
  proved (`Proofs/External/`) and restated in `Specs/External.lean` (since 2026-11-24:
  `formal/proofs/Proofs/Internal/External.lean`).
- **Translation pin** (S21, human decision 2026-11-23): `formal/trusted/translation-pins.txt` records
  the sha256 of `formal/translation/Rmcp/Funs.lean` and the one line on which `lean-guard.sh sources`
  excuses a metaprogramming word (line 1971, the word `initialize`, the T06 literal). It is a trusted
  file: the guard cannot see lexical context, so a pin whose hash is updated together with an edited
  `Funs.lean` excuses whatever stands at the pinned line; only the byte-for-byte regeneration of
  `aeneas-translation.yml` and review (each pinned line read in context) catch that. A legitimate
  re-translation must update it in a reviewed PR.
- **Phase 2 external models** (S26/S27, 2026-11-23; reviewed, signed off by the spec owner,
  laws proved): the 26 S21 placeholders are definitions transcribed from `core`/`alloc` of
  nightly-2026-06-01 (strings and `Arc`; `Option`, `Result`, slices, ranges; `i64::from_str`;
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
- **Codec-state hypothesis** (accepted at S12): `Defs/CodecState.lean` defines `CodecValid`
  (keyring clauses; single-key codecs unconstrained; pairwise distinct key ids),
  `CodecFallbacksKnown` (every rs1 fallback id is a key id) and `FallbacksKnown`. It is a
  hypothesis of the statements, not an axiom: E09, E11 and the rs1 round trips assume
  `CodecFallbacksKnown`, E09a `FallbacksKnown`, E10 and rs2 nothing. `CodecValid` implies
  `CodecFallbacksKnown`. The excluded constructors are what establish it in Rust; they are not
  verified.
- **Tools:** Charon `0.1.235` and Aeneas (`nightly-2026.08.20-5d08da4`), Lean `v4.31.0` kernel,
  prebuilt Aeneas Lean library (archive sha256 checked) and Mathlib oleans (not digest-checked).
- **Configuration:** the translated configuration above. **Patches:** one,
  `formal/trusted/patches/01-request-state-wire.patch` (the refactor and its tests; D2 fallback,
  2026-11-23; reviewed by two independent agents and signed off by the human on 2026-11-23, VERIFICATION.md §4). **Hand edits of the translation:** none.
  **Exclusions:** the list above (plan Section 2.3).
- **Statements:** `formal/specs/Defs/` and `formal/specs/Specs/` (public API; index
  `formal/specs/README.md`), and `formal/proofs/Proofs/Internal/` with `formal/proofs/Proofs/Defs/`
  (private, crate-internal and patch-only functions and the model laws; human decision 2026-11-24).

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
| Phase 2: strings, `Arc`, `Option`, `Result`, slices, ranges | definitions (S26) | signed off 2026-11-23; 22 laws proved |
| Phase 2: `i64::from_str`, `Ipv4Addr`/`Ipv6Addr` | definitions, structures (S27) | signed off 2026-11-23; 21 laws proved |
| `serde_json::Value` (type) | `opaque ExtModel.SerdeJsonValue` (S27) | signed off 2026-11-23 (no law: only moved) |

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
(signatures only); since S21 (Phase 2, plan Section 15) also the crates of the widened features
(`http`, `tokio`, `tokio_util`, `tracing`, `tracing_core`, `futures`, `futures_util`, `futures_core`,
`bytes`, `sse_stream`, `hyper`, `tower_service`, `uuid`, `schemars`, `pin_project_lite`,
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
    only `.github/workflows/lean-build.yml` existed. Found at S19. **Fixed** (2026-11-23):
    `aeneas-translation.yml` and `patched-tests.yml` written, reviewed and checked locally
    (the CI-workflows evidence (git history at 223ff12)); they have not run on GitHub yet (S17).

Items 1–3 are in the plan text the specifications were checked against, not in the Rust code.

## Phase 2

Plan Part II (Sections 13–25). Twenty-five existing upstream functions in six files of
`crates/rmcp/src/` at `7caec76`, unmodified, to be verified with linkage `ORIGINAL`, plus the
composition theorems C01–C05. Selected by a measured pilot (plan Section 14, 2026-11-23); the
pilot is not the project's translation, which is S21.

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
record: `translation: LEAN_OK` (S21), `spec: DRAFT`, `linkage: ORIGINAL` (pending the
S22 check), `proof: OPEN`.

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

Board: S20 `IN_PROGRESS`; S21 `IN_PROGRESS` (translated, all 25 `LEAN_OK`; human sign-off and CI pending);
S22 `IN_PROGRESS` (linkage check written and reviewed; local evidence below; not yet in CI); S24 `IN_PROGRESS` (statements signed off 2026-11-24; awaits human acceptance); S25 `IN_PROGRESS` (statements signed off 2026-11-24; awaits human acceptance); S28–S33 `IN_PROGRESS` (proved, restated and proof-reviewed 2026-11-24; awaits human acceptance); S26/S27 `IN_PROGRESS` (signed off, proved); the other steps `NOT_STARTED`.

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
- **Upstream Aeneas `toStr` issue** (`Aeneas/Std/String.lean`): to be filed by a human; after a
  fix and a rev bump, `native-axioms.lock` can be emptied.

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
