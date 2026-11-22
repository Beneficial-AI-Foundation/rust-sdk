# MCP SDK Verification — Master Plan

Date: 22 November 2026. This is the single current plan.

**Current state:** the pilot was run in a scratch copy outside the repository (Section 8, "Pilot results").
- **Unchanged source:** most targets cannot be extracted.
- **With a small behaviour-preserving adapter (Section 9):** all eleven targets extract and compile in Lean.
- **Not yet done:** nothing has been committed to the repository, no proof exists, and no agent role has been set up. Every proof is `OPEN`.
- **Waiting on the human owner:** the D2 decision (Section 8) — whether to land the adapter.

## Fixed requirements

| Requirement | Section |
|---|---|
| Verify existing SDK functions; no new runtime or replacement implementation | 1, 2 |
| Eleven concrete existing functions, each with an independent specification | 2, 3 |
| Dalek-style crate-local Lean project with `Specs` / `Theorems` / `Proofs` / `Checks` libraries | 5 |
| Two-week sprint with measured feasibility gates | 8, 9 |
| Operational Claude agent stack | 10 |
| Ordered steps with exact files, timing and ownership | 8 |
| Explicit status and acceptance evidence per function | 6, 7 |
| Stated security scope and reproducibility | 1, 4, 11 |
| AI may draft specifications; a named human spec owner accepts every one | 6, 10 |

Change a requirement only when the user changes it, or a documented technical incompatibility forces an explicit decision.

**Governing guides.** Day-to-day rules for this plan live in four guides under `docs/`. This plan defines scope, targets, steps and status; the guides define how work is written, submitted and reviewed. If the two disagree, fix whichever is wrong in the same PR.

| Guide | Covers |
|---|---|
| [`WORKFLOW_AND_PR_GUIDE.md`](WORKFLOW_AND_PR_GUIDE.md) | Generated files, extraction, import roots, status records, PR format, trust rules, AI contributions |
| [`STYLE_GUIDE.md`](STYLE_GUIDE.md) | Lean headers, tactics, library layering, `Specs` definitions, spec theorem layout, composition and public theorem files |
| [`REVIEWER_GUIDE.md`](REVIEWER_GUIDE.md) | Review criteria and steps, including review of AI-drafted specifications |
| [`AI_PR_REVIEW_QUESTIONS.md`](AI_PR_REVIEW_QUESTIONS.md) | Checklist and report format for AI-assisted PR review |

---

## 1. Source baseline and scope

- **Repository:** https://github.com/truonghoangle/rust-sdk (the user's fork of the Rust MCP SDK).
- **Pinned source commit:** `0e2396f73a88617141b31f645de6f1171ed5f993`. The current `main` (`7caec76`) adds only `verification/host_origin/`; `crates/rmcp/src/model/request_state.rs` is byte-identical between the two commits (SHA-256 `41e69cad94869be4b93120f3cd39a10fad4a3730585240b712c2ada1b311b416`). Record the hash of that file in `verification/manifest.yaml` and re-check it before every extraction.
- **Target file:** `crates/rmcp/src/model/request_state.rs`. It compiles only with the `request-state` feature (`crates/rmcp/Cargo.toml`, `request-state = ["dep:hmac", "dep:zeroize", "base64"]`).
- **Build configuration:** `--no-default-features --features request-state --lib`, on the target the toolchain is pinned to (x86_64/aarch64, 64-bit `usize`).

**Objective:** implementation-linked correctness of the request-state codec — framing, configuration checks, version dispatch, MAC transcripts, expiry, and seal/open round-trip — under explicitly named contracts for HMAC-SHA256, Base64url and the standard-library operations the code uses.

**Not claimed:** HMAC unforgeability or any other cryptographic security property; constant-time behaviour of the compiled code; correctness of the `hmac`, `sha2`, `base64` or `zeroize` crates; coverage of the public wrappers (`seal_with`, `open_with`, `seal_at`, JSON helpers, constructors); full MCP protocol verification. Claims apply to the pinned commit and configuration only, not to upstream releases.

## 2. The eleven target functions

All are associated functions of `RequestStateCodec`. Line numbers refer to the pinned commit.

| ID | Function / line | Independent specification | Rust features it exercises |
|---|---|---|---|
| E01 | `open_authenticated_body` / 722 | `len < 8` → `MalformedFormat`; expiry = first 8 bytes as signed big-endian `i64`; `expiry ≠ 0 ∧ now > expiry` → `Expired`; otherwise `Ok(body[8..])` | `Vec`, slice ranges, `try_into` to `[u8; 8]`, `i64::from_be_bytes`, `to_vec` |
| E02 | `b64_len` / 780 | `4 * ceil(n / 3)` when `ceil(n/3) * 4` fits in `usize`; an upper bound on unpadded Base64url length | `usize::div_ceil`, multiplication |
| E03 | `validate_key_length` / 755 | `Ok` iff `len ≥ 32`; otherwise `KeyTooShort { minimum: 32, actual: len }` | slice length |
| E04 | `validate_config_kid` / 765 | `Ok` iff UTF-8 byte length is in `1..=255`; empty and too-long give their two distinct `InvalidKeyring` messages | `str::len`, `str::is_empty` |
| E05 | `mac_v1` / 735 | Returned HMAC state has key `key` and absorbed bytes `DOMAIN_V1 ++ be64(len ad) ++ ad ++ body` | `Hmac::new_from_slice`, `Mac::update`, `u64::to_be_bytes` |
| E06 | `mac_v2` / 744 | Absorbed bytes `DOMAIN_V2 ++ be64(len kid) ++ kid ++ be64(len ad) ++ ad ++ body` | as E05 |
| E07 | `seal_rs1` / 584 | Output = `"rs1." ++ b64(body) ++ "." ++ b64(tag)`, `tag = HMAC(key, E05 transcript)` | E02, E05, `finalize().into_bytes()`, `String::with_capacity`, `push_str`, `encode_string` |
| E08 | `seal_rs2` / 599 | Output = `"rs2." ++ b64(kid) ++ "." ++ b64(body) ++ "." ++ b64(tag)` with the E06 transcript | E02, E06, as E07 |
| E09 | `open_rs1_at` / 620 | Exact parse and error order (Section 3); accept iff some configured key verifies the tag; then E01 | `str::split('.')`, `HashMap::get`, `Zeroizing` deref, `verify_slice`, Base64 decode, E01, E05 |
| E10 | `open_rs2_at` / 676 | Exact parse and error order (Section 3); MAC binds kid, ad and body; then E01 | `str::split('.')`, `String::from_utf8`, `HashMap::get`, Base64 decode, `verify_slice`, E01, E06 |
| E11 | `open_at` / 571 | First `.`-component `"rs1"` → E09, `"rs2"` → E10, anything else → `MalformedFormat`; result passed through unchanged | `str::split('.')`, `Iterator::next`, string equality |

The order is a work queue, not a call graph. E03/E04 are used only when constructing a codec; they are not called by the opening functions.

## 3. Source behaviour that the specifications must capture

**E01 — expiry.** `now_ms == expiry` is accepted. A negative nonzero expiry is compared as a signed value like any other. E01 performs no authentication; its theorem is about byte handling only.

**E02 and seal capacities — arithmetic.** The workspace sets no `overflow-checks`, so debug builds panic on overflow and release builds wrap. Aeneas models overflow as failure, which matches debug builds only. Every arithmetic theorem (E02, and the `with_capacity` sums in E07/E08) is therefore stated on the domain where no overflow occurs, and that domain is written into the theorem. Allocation failure is an explicit assumption, not a no-panic claim.

**E04 — kid alphabet.** Any nonempty UTF-8 string of at most 255 bytes is accepted. Do not add an alphabet restriction to the specification.

**E05/E06 — return type.** These functions return a `HmacSha256` *state*, not a tag. Their theorems are stated over the abstract HMAC state of Section 4. Lengths are cast `usize → u64`; on a 64-bit target this cast is exact, which the theorem records as a hypothesis.

**E09 — error order.**
1. Fewer than 3 or more than 3 `.`-parts, or version ≠ `rs1` → `MalformedFormat`.
2. Ring codec with empty `rs1_fallbacks` → `UnknownKeyId` (before any decoding).
3. Body Base64 decode fails, then tag Base64 decode fails → `InvalidEncoding`.
4. Single key: one verification. Ring: every fallback key is tried without early exit; none matches → `IntegrityCheckFailed`. `keys.get(kid).expect(..)` must not fail, which needs the codec-state invariant (Section 4).
5. E01 on the decoded body.

The loop that tries every key is a timing measure. The functional proof says nothing about timing.

**E10 — error order.**
1. Not exactly 4 parts, or version ≠ `rs2` → `MalformedFormat`.
2. Encoded kid longer than 340 → `InvalidKeyId`.
3. Kid Base64 decode fails → `InvalidEncoding`.
4. Decoded kid empty or longer than 255 → `InvalidKeyId`; not UTF-8 → `InvalidKeyId`.
5. Single-key codec → `UnknownKeyId`; ring without that kid → `UnknownKeyId`.
6. Body, then tag decode → `InvalidEncoding`.
7. MAC mismatch → `IntegrityCheckFailed`.
8. E01.

Normalising these errors before they reach clients is an application obligation and outside this theorem.

**Round-trip.** The seal helpers take a body, not a payload. Round-trip theorems state that opening returns `body[8..]`, under these conditions: the body is at least 8 bytes, expiry is 0 or `now ≤ expiry`, and the associated data is the same. For rs1 the opening codec is either the same single key or a ring whose `rs1_fallbacks` include the signing key. For rs2 the kid is valid UTF-8 of 1–255 bytes and the ring maps it to the signing key. `seal_rs2` accepts any kid, so round-trip holds only on that valid-kid domain.

## 4. External contracts

Each contract describes a primitive on its own terms. No contract may assume that a target function is correct.

| Contract | Model | Not established |
|---|---|---|
| **HMAC state** (`mac::MacState`, Section 9) | Abstract state `⟨key, absorbed : List U8⟩`. `MacState::new k` always succeeds with `⟨k, []⟩` (HMAC accepts keys of any length). `update s m = ⟨s.key, s.absorbed ++ m⟩`. `finalize s = hmacSha256 s.key s.absorbed`, a 32-byte array, where `hmacSha256` is an opaque reference function. `verify s t = true` iff `t.length = 32 ∧ t = finalize s`. | Cryptographic security; correctness of the `hmac`/`sha2` crates; constant time |
| **Base64url (no padding)** (`b64`, Section 9) | `encode_into x out` appends `b64(x)` to `out`. `decode` matches the `URL_SAFE_NO_PAD` engine: rejects padding and non-canonical trailing bits. Law: `decode (b64 x) = Ok x`. | Correctness of the `base64` crate |
| **String / Vec / slice / HashMap** | Value semantics for the operations used. The Aeneas library already provides `Slice.to_vec`, `Vec.index`, the `[u8; 8]` `try_from` and `U64.from_be_bytes`. These need hand-written models: `usize::div_ceil`, `str::len`, `str::is_empty`, `str::as_bytes`, string equality, `dot::split`/`Parts::next` (Section 9, splitting on `.`), `String::with_capacity`/`push_str`/`from_utf8`, `HashMap::get`, and `Zeroizing` deref to a slice. | Unlimited memory; hashing behaviour; zeroisation on drop |
| **Codec state** | Every id in `rs1_fallbacks` and the `seal_mode` key id are keys of `keys`; every key is at least 32 bytes; every kid passes E04. These are the invariants the constructors enforce. | Correctness of the constructors (out of scope) |
| **Translation** | Aeneas-generated Lean is a faithful model of the pinned Rust source under the pinned toolchain. | Compiler or binary correctness |

Prefer law-carrying structures or hypotheses over global `axiom`s. Every remaining axiom must appear in `verification/assumptions.yaml` with an ID, its docstring must name that ID and its justification (style guide, "Specification Definition Guidelines"), and the axiom audit accepts only those IDs. A new ID needs explicit approval from the spec owner in PR review. `native_decide` is not used (workflow guide, "Proof cheats"). Check each contract against concrete examples from the real crates (for example, known HMAC-SHA256 and Base64 test vectors) in the Rust test module. These tests catch a mismatched model; they are not a consistency proof.

## 5. Layout

### Reuse of the existing extraction

`verification/host_origin/` (PR #4) already extracted other `rmcp` code at the same commit. This plan reuses its toolchain, and the pilot confirmed that it builds:

| Component | Version | Notes from the pilot |
|---|---|---|
| Charon | `0.1.235` (commit `f5208b1c`, the `charon-pin` of Aeneas `5d08da45`) | Built from source with `make build` |
| Aeneas | `5d08da45` | Built with `make build-bin build-lib build-bin-dir` in an opam OCaml 5.2.0 switch |
| Rust | `nightly-2026-06-01` | Charon's own `rust-toolchain` file pins this |
| Lean | `4.31.0` | Aeneas Lean library needs Mathlib `v4.31.0` (`fabf563a`) |

Lessons from host_origin and from the pilot:
- Aeneas cannot handle the generic associated types (GATs) used by `hybrid_array` (inside `hmac`/`sha2`) and by `core::str::pattern::Pattern` (behind `str::split`). The pilot resolved both with small opaque adapter modules; see Section 9, B1–B2.
- Charon cannot name methods of inherent impls in patterns, and all eleven targets are such methods. Start from the module and use a `_` glob in the impl position (Section 9, B8).
- The pinned Aeneas may emit `Iterator` instance fields (`filter_map`, `any`) missing from its Lean library; host_origin removed them from `Funs.lean` by hand. Record every hand edit to generated files.

`verification/host_origin/` stays where it is. This plan puts request-state verification in the crate-local Lean project below, as the Dalek layout requires. Whether host_origin later moves into that project is a separate decision, not part of this sprint.

### Files

Paths are relative to the repository root. **NEW** = written by hand; **GEN** = produced by the toolchain; **UPDATE** = extend existing content. `Sxx` refers to the steps in Section 8. `<LEAN>` = `crates/rmcp/lean/`.

```
CLAUDE.md                                       NEW   S02   points to the four guides
.claude/agents/mcp-extraction.md                NEW   S02
.claude/agents/mcp-spec.md                      NEW   S02
.claude/agents/mcp-lean.md                      NEW   S02
.claude/agents/mcp-review.md                    NEW   S02
crates/rmcp/src/model/request_state.rs          existing target; adapter of Section 9 added
                                                in S04a (D2 option 1 or 2)
                                                (tests added to its private `mod tests` — S16)
crates/rmcp/lean/
  README.md                                     NEW   S03, final S19
  lakefile.lean, lean-toolchain                 NEW   S03
  lake-manifest.json                            GEN   S03
  scripts/extract.sh                            NEW   S03
  scripts/check.sh                              NEW   S17
  Rmcp.lean                                     GEN   S04
  Rmcp/Types.lean, Rmcp/Funs.lean               GEN   S04
  Rmcp/TypesExternal.lean, Rmcp/FunsExternal.lean   from GEN templates, then edited  S04, S08–S09
  Specs.lean                                    NEW   S05
  Specs/RequestState.lean                       NEW   S05   framing, expiry, lengths, errors
  Specs/External/Hmac.lean                      NEW   S08
  Specs/External/Base64.lean                    NEW   S09
  Specs/External/Str.lean                       NEW   S09   `dot`, string, HashMap, div_ceil models
  Specs/CodecState.lean                         NEW   S12   codec-state invariants
  Proofs.lean                                   NEW   S05
  Proofs/Model/RequestState/
    OpenAuthenticatedBody.lean  E01  S06
    B64Len.lean                 E02  S07
    ValidateKeyLength.lean      E03  S07
    ValidateConfigKid.lean      E04  S07
    MacV1.lean                  E05  S10
    MacV2.lean                  E06  S10
    SealRs1.lean                E07  S11
    SealRs2.lean                E08  S11
    OpenRs1At.lean              E09  S13
    OpenRs2At.lean              E10  S13
    OpenAt.lean                 E11  S14
  Theorems.lean                                 NEW   S05
  Theorems/Model/RequestState.lean              NEW   S05 onward   public E01–E11 statements
  Theorems/Model/RequestStateComposition.lean   NEW   S15          round-trip and dispatch
  Checks.lean                                   NEW   S17
  Checks/Axioms.lean                            NEW   S17
verification/
  manifest.yaml                                 NEW   S01   pins, hashes, features, owners, budget
  assumptions.yaml                              NEW   S05   approved assumption IDs
  board.yaml                                    NEW   S01   task state (authoritative)
  functions/E01.yaml … E11.yaml                 NEW   S01   per-function status
  pilot.md                                      NEW   S04   results, adapter patch, Charon arguments
  evidence/Sxx.md                               NEW   per step
  blockers/Sxx.md                               NEW   on failure only
.github/workflows/lean-build.yml                NEW   S17
docs/MCP_SDK_Verification_Master_Plan_EN.md     this plan
docs/WORKFLOW_AND_PR_GUIDE.md                   existing   workflow, PR format, AI contributions
docs/STYLE_GUIDE.md                             existing   Lean style and file layout
docs/REVIEWER_GUIDE.md                          existing   human review
docs/AI_PR_REVIEW_QUESTIONS.md                  existing   AI-assisted review
docs/RESULTS.md                                 NEW   S19
```

### Library rules

- `Specs` imports nothing from `Proofs`, `Theorems` or `Checks`. Public theorem statements use only `Specs` definitions, so their meaning never depends on proof-private definitions.
- `Proofs` may import `Rmcp` and `Specs`, never `Theorems` or `Checks`.
- `Theorems` imports `Proofs` and re-states accepted results readably. It imports only accepted proofs; drafts with `sorry` live outside the import roots.
- `Checks` imports `Theorems` and audits it. Nothing imports `Checks`. `lake build Checks` must actually run in CI.
- The import roots (`Specs.lean`, `Proofs.lean`, `Theorems.lean`, `Checks.lean`) are maintained by hand and list only accepted modules (workflow guide). File naming, docstrings and the spec theorem layout follow the style guide.

Proposed public theorem names (finalised once the generated signatures are known; the identifier is the full generated function name with `_spec`, per the style guide):

| ID | Theorem |
|---|---|
| E01 | `open_authenticated_body_spec` |
| E02 | `b64_len_spec` |
| E03 | `validate_key_length_spec` |
| E04 | `validate_config_kid_spec` |
| E05 | `mac_v1_spec` |
| E06 | `mac_v2_spec` |
| E07 | `seal_rs1_spec` |
| E08 | `seal_rs2_spec` |
| E09 | `open_rs1_at_spec` |
| E10 | `open_rs2_at_spec` |
| E11 | `open_at_spec` |
| — | `rs1_roundtrip`, `rs2_roundtrip`, `open_at_roundtrip_rs1`, `open_at_roundtrip_rs2` |

Each theorem covers both success and error results, not only the success path.

## 6. Status model

One vocabulary is used everywhere.

**Task state** (in `board.yaml`): `NOT_STARTED` → `IN_PROGRESS` → `ACCEPTED`, or `BLOCKED` / `DEFERRED`. Only `ACCEPTED` is complete. An accepted blocker report closes the *task of reporting*, never the function's proof.

**Function status** (in `functions/Exx.yaml`), four independent fields:

| Field | Values |
|---|---|
| `extraction` | `NOT_TRIED`, `LLBC_OK` (Charon), `LEAN_OK` (Aeneas output compiles), `BLOCKED` |
| `spec` | `DRAFT`, `REVIEWED` |
| `linkage` | `ORIGINAL` (unchanged source), `ADAPTED` (source or translation patched; diff and correspondence argument recorded) |
| `proof` | `OPEN`, `CHECKED` |

Only a named human spec owner sets `spec: REVIEWED` or moves a task to `ACCEPTED`. A specification may be drafted by a person or by an AI agent (workflow guide, "AI contributions"); the drafter is recorded in `spec_drafted_by`, and an AI drafter never sets `REVIEWED`. Any change to an accepted statement returns `spec` to `DRAFT`.

**Verified** means `proof: CHECKED`, `spec: REVIEWED`, `linkage: ORIGINAL`, and the axiom audit shows only approved assumption IDs. Anything else is reported as what it is (for example "checked, adapted source" or "open"). The deadline never changes a status.

Function record template:

```yaml
id: E01
rust_symbol: RequestStateCodec::open_authenticated_body
source_line: 722
source_file_sha256: null        # filled in at S01
generated_symbol: null          # filled in at S04 / S06
extraction: NOT_TRIED
spec: DRAFT
linkage: ORIGINAL
proof: OPEN
proof_file: crates/rmcp/lean/Proofs/Model/RequestState/OpenAuthenticatedBody.lean
theorem: null
assumptions: []                 # IDs from verification/assumptions.yaml
evidence: []                    # paths under verification/evidence/
spec_drafted_by: null           # person, or "AI: <tool>, <model>"
spec_owner: null                # human who accepted the spec
prover: null                    # person, or "AI: <tool>, <model>"; not the AI spec drafter
reviewer: null
```

## 7. Acceptance per step and per function

Every step writes `verification/evidence/Sxx.md` with the exact commands, exit status, source and generated-file hashes, assumptions added, which artifacts were AI-drafted (tool and model), and reviewer decision. On failure also write `verification/blockers/Sxx.md` with a minimal reproducer and leave the task `BLOCKED`.

Boundary cases each proof must cover and the Rust tests must exercise:

| ID | Cases |
|---|---|
| E01 | 0–7 bytes; exactly 8; expiry 0; `now` before, equal to, after expiry; negative expiry |
| E02 | `n mod 3 ∈ {0,1,2}`; `n = 0`; largest `n` with no overflow |
| E03 | 31, 32, 33 bytes; `actual` field value |
| E04 | 0, 1, 255, 256 bytes; multibyte UTF-8 crossing 255 |
| E05 | empty ad and body; transcript order and length prefix |
| E06 | kid, ad, body each varied; transcript order |
| E07 | empty and nonempty body; delimiters; tag encoding |
| E08 | multibyte kid; part order |
| E09 | 2 and 4 parts; wrong version; ring with no fallbacks; bad Base64 body/tag; MAC fails; match on the last fallback; expiry |
| E10 | encoded kid 340/341; decoded kid 0/255/256; invalid UTF-8; single-key codec; unknown kid; bad body/tag; MAC fails; expiry |
| E11 | `rs1`, `rs2`, `rs3`, empty string, no `.` |

The target functions are private, so Rust tests go in the existing `mod tests` of `request_state.rs` (36 tests at the pinned commit). Adding tests changes the file hash; record the diff and confirm it touches only `mod tests`.

## 8. Two-week sprint

Days are relative working days. Dependencies govern acceptance; independent preparation can start earlier.

### Pilot (D1–D2)

The pilot runs extraction on three unchanged functions, each chosen to test a different risk:

| Function | Risk it tests |
|---|---|
| E01 `open_authenticated_body` | `Vec`, slices, fixed-size array conversion, `i64::from_be_bytes` |
| E05 `mac_v1` | external `hmac` trait machinery and its fixed-size output type |
| E11 `open_at` | `str::split('.')` — the string-pattern class that failed for host_origin; gates E09–E11 |

### Pilot results (22 November 2026)

The pilot ran in a scratch copy of the repository on macOS aarch64, with the pinned Charon and Aeneas built from source. It was run twice:
- **Run 1:** on the unchanged source (file hash in Section 1).
- **Run 2:** on a small behaviour-preserving adapter (Section 9).

The generated Lean was compiled with Lean 4.31.0 against an existing build of the Aeneas Lean library at `6e167c9b`. That library's Lean files are identical to the pinned `5d08da45`'s; the only difference is one added utility file. Scratch artifacts are temporary and must be copied into `verification/pilot.md` and `verification/evidence/S04.md` at S01:
- the adapter patch
- the Charon argument list
- the `extract.sh` and `compile.sh` scripts
- the logs

| ID | Run 1: unchanged source | Run 2: with adapter (Section 9) |
|---|---|---|
| E01 | Body generated; Lean compile fails (library bug B6) | Compiles |
| E02 | Body generated | Compiles; `usize::div_ceil` is an external declaration |
| E03 | Body generated | Compiles |
| E04 | Body is `sorry` (B4) | Compiles |
| E05, E06 | Not translatable (B1) | Compile; `MacState` methods are external declarations |
| E07, E08 | Not translatable (B1) | Compile; `MacState` and `b64` are external |
| E09 | Not translatable (B1, B2, B5) | Compiles, via the new helper `rs1_fallbacks_verify` |
| E10 | Not translatable (B1, B2) | Compiles |
| E11 | Body has a `sorry` placeholder (B2) | Compiles; `dot::split` and `Parts::next` are external |

In run 2, Aeneas writes all five output files. `Types`, `TypesExternal`, `FunsExternal` and `Funs` compile with **0 errors**. Seven declarations still contain `sorry`, all outside the target set:
- `Debug`/`Display` impls of `RequestStateError`
- `Debug` impl of `RequestStateCodec`
- `new_with_keyring`, `with_rs1_signing`, `with_rs1_fallback`
- `seal_at`

None of the eleven targets depends on them. The generated code still calls 67 external declarations. Those in the target closure are the contracts listed in Section 4. With the adapter applied, the existing tests pass (39 request-state tests), `cargo clippy --lib -- -D warnings` is clean, and nightly `rustfmt` reports no diff.

**Cost so far:** about 10 minutes to build Charon and Aeneas, about 1 minute per extraction, about 10 seconds per Lean compile, and roughly half a day of agent-assisted investigation in total.

### D2 decision (waiting on the human owner)

The original gate said to pause if E05 blocks. E05 blocked on the unchanged source but works with the tested adapter, so the decision is now narrower:

1. **Land the adapter in the fork and re-pin (recommended).**
   - Review the adapter (Section 9, "Adapter") as an ordinary SDK change and commit it to the fork.
   - Re-pin to that commit. All eleven functions are then `ORIGINAL` relative to the new pin.
   - The adapter's correspondence to the old commit is argued once, in the review (Section 9).
2. **Keep the adapter as a patch.** Do not change the fork, and label every function that the adapter touches `ADAPTED`, with the patch and correspondence argument recorded. This is the same technical work with weaker linkage claims.
3. **No adapter.** Only E02 and E03 have clean bodies on the unchanged source, and E01 needs a library fix (B6). Report the rest as `BLOCKED` and wait for upstream fixes (Section 9, "Upstream"), with no timeline.

Option 1 or 2 keeps the eleven-function sprint feasible. Option 3 reduces it to two or three proofs.

### Steps

| Step | Day | Depends on | Files | Owner — acceptance |
|---|---|---|---|---|
| S01 | D1 | — | `verification/manifest.yaml`, `board.yaml`, `functions/E01–E11.yaml` | Lead — pins, file hash, features, named human owners and budget recorded |
| S02 | D1 | S01 | `CLAUDE.md`, `.claude/agents/*.md` | Lead — roles and edit permissions defined; `CLAUDE.md` points to the four guides |
| S03 | D1 | S01 | `<LEAN>/lakefile.lean`, `lean-toolchain`, `lake-manifest.json`, `scripts/extract.sh`, `README.md` | Extraction — empty project builds with the pinned host_origin toolchain; resolves B10 |
| S04 | D1–2 | S03 | `verification/pilot.md`, `verification/evidence/S04.md` | Extraction — pilot artifacts (adapter patch, Charon arguments, scripts, logs) copied from the scratch run; D2 decision recorded. *Pilot run done outside the repository; copying and decision outstanding.* |
| S04a | D2–3 | S04; D2 option 1 or 2 | `request_state.rs` (adapter, Section 9); `Rmcp.lean`, `Rmcp/*.lean` | Extraction + reviewer — two PRs, as the workflow guide requires: (1) the adapter, whose review checklist (Section 9) passes; with option 1 it is landed and the new pin recorded in `manifest.yaml`; (2) the re-extraction, where generated Lean for all eleven targets builds in the crate-local project with no `sorry` in any target |
| S04b | D2–4 | S04 | `verification/blockers/S04.md`, upstream issues | Extraction — single-file reproducers for B1, B2, B4, B5 (Aeneas) and B8 (Charon) filed; not on the critical path |
| S05 | D2 | S01 | `Specs.lean`, `Specs/RequestState.lean`, `Proofs.lean`, `Theorems.lean`, `Theorems/Model/RequestState.lean`, `verification/assumptions.yaml` | Spec drafter (`mcp-spec` or a person) + spec owner — E01–E04 specs and import direction reviewed and accepted |
| S06 | D2–3 | S04, S05 | `OpenAuthenticatedBody.lean` | Lean — E01 theorem checked |
| S07 | D3 | S04, S05 | `B64Len.lean`, `ValidateKeyLength.lean`, `ValidateConfigKid.lean` | Lean — E02–E04 checked; E02 overflow domain explicit |
| S08 | D3–4 | S04a | `Specs/External/Hmac.lean`, `Rmcp/FunsExternal.lean` | Extraction + spec owner — `MacState` contract reviewed; RFC 4231 vectors pass through `MacState` in Rust tests |
| S09 | D3–4 | S04a | `Specs/External/Base64.lean`, `Specs/External/Str.lean`, `Rmcp/FunsExternal.lean` | Extraction + spec owner — `b64` and `dot` contracts and the string/`HashMap`/`div_ceil` models reviewed; encode/decode law and split behaviour checked against the real crates |
| S10 | D4–5 | S08 | `MacV1.lean`, `MacV2.lean` | Lean — E05/E06 transcript theorems checked |
| S11 | D5–6 | S07, S09, S10 | `SealRs1.lean`, `SealRs2.lean` | Lean — E07/E08 output-format theorems checked on the no-overflow domain |
| S12 | D5 | S05 | `Specs/CodecState.lean` | Spec owner — codec-state invariant reviewed against the constructors |
| S13 | D6–8 | S06, S09, S10, S12 | `OpenRs1At.lean`, `OpenRs2At.lean` | Lean — E09/E10 theorems with full error order checked |
| S14 | D8 | S13 | `OpenAt.lean` | Lean — E11 dispatch theorem checked |
| S15 | D8–9 | S11, S13, S14 | `Theorems/Model/RequestStateComposition.lean` | Lean — each round-trip theorem accepted on its own; missing ones listed `OPEN` |
| S16 | D2–9 | S05 onward | `mod tests` in `request_state.rs` | Review — Section 7 boundary cases and contract test vectors pass under `cargo test --features request-state` |
| S17 | D9 | accepted results | `Checks.lean`, `Checks/Axioms.lean`, `scripts/check.sh`, `.github/workflows/lean-build.yml` | Lead — CI builds `Theorems` and `Checks`; audit fails on an unapproved axiom or `sorry` (shown once with a throwaway branch) |
| S18 | D9–10 | S17 | `verification/evidence/S18.md` | Review — fresh clone reproduces extraction and build; generated files match |
| S19 | D10 | board state; no success required | `docs/RESULTS.md`, `<LEAN>/README.md` | Lead + human owner — honest per-function status, assumptions, blockers, cost; next-sprint scope |

In the Owner column, "spec owner" is the human who accepts specifications and contracts. Any spec, contract or assumption entry in S05, S08, S09 and S12 may be drafted by the `mcp-spec` agent; the spec owner reviews it with the reviewer guide before any proof of it is accepted. Proof steps (S06–S15) start only on accepted specifications.

S19 is mandatory even if every other step fails.

### Gates

- **D2:** pilot decision (Section 8: option 1, 2 or 3). The project owner confirms that people and budget are allocated. Under option 1 or 2, S04a must show all eleven targets building in the crate-local project before proof work on E05–E11 starts; E01–E04 proofs can start on the pilot output.
- **D5:** leaves (E01–E04) and the HMAC/Base64 boundary are measured. Re-estimate the rest from actual effort. Keep all eleven targets visible.
- **D10:** `docs/RESULTS.md` written. Report how many functions are verified, checked-but-adapted, blocked and open.

Eleven verified functions is a stretch goal. The mandatory result is measured extraction feasibility, whatever proofs are actually checked, and accurate blocker reports.

## 9. Blockers and resolutions

Each blocker below lists its cause, the resolution, whether the resolution was tested, and its effect on source linkage. "Tested" means it was done in the pilot's scratch copy and the result is in Section 8, "Pilot results".

### Blocker table

| ID | Blocker | Affects | Cause | Resolution | Tested | Linkage effect |
|---|---|---|---|---|---|---|
| B1 | HMAC types cannot be translated | E05–E10 | `hmac`/`sha2` use `hybrid_array::Array`, which is mutually recursive with the `ArraySize` trait (a GAT). Aeneas rejects mixed type/trait recursion. `--opaque` does not help, because signatures are still translated. `--exclude` leaves the `mac_v1`/`mac_v2` return type undefined. | Adapter module `mac` with a private `MacState(HmacSha256)` and four methods. Mark the module `--opaque` and `--exclude` the `HmacSha256` alias. Aeneas then sees only `MacState` and four signatures. | Yes | Source change |
| B2 | `str::split` crashes Aeneas | E09–E11 | `core::str::pattern::Pattern` has a GAT (`Searcher<'a>`); Aeneas raises an uncaught exception on any signature that mentions it. `Split<'a, P>` stores `P::Searcher<'a>`, so even the iterator type is affected. | Adapter module `dot` with `split(&str) -> Parts` and `Parts::next`, wrapping `split('.')`, marked `--opaque`. | Yes | Source change |
| B3 | `base64` engine instance missing in Lean | E07–E10 | With `base64` opaque, the generated code refers to the `Engine` trait instance for `GeneralPurpose`, which is never declared. Lean fails with an unknown constant and unresolved fields `encode_string`, `decode`. | Adapter module `b64` with `encode_into` and `decode`, marked `--opaque`. | Yes | Source change |
| B4 | Returning a `&'static str` literal | E04 (and `with_rs1_*`) | Aeneas fails with "There should be no bottoms in the value" for any function that moves a string literal into its result, even `fn f() -> &'static str { "x" }`. A named `const` works. | Define `KID_EMPTY_MSG` and `KID_TOO_LONG_MSG` as `const`s and use them in place of the literals. The error text is unchanged. | Yes | Source change |
| B5 | Loop fixed point not found | E09 | Aeneas cannot compute a fixed point for the fallback loop inside `open_rs1_at`, either as a `for` or a `while` loop. Separately, the `matches!(…, Ring { rs1_fallbacks, .. } if …)` guard fails with "Could not match the contexts". | Move the loop unchanged into `rs1_fallbacks_verify`, which takes only shared references. Replace the `matches!` guard with an `if let … && …` let-chain. Every fallback is still tried, with no early exit. | Yes | Source change |
| B6 | Wrong library signature for signed `from_be_bytes` | E01 | The pinned Aeneas Lean library models `i64::from_be_bytes` as taking `Array I8`; Rust takes `[u8; 8]`. Fixed upstream in Aeneas #1355. | **Tested:** decode as `u64::from_be_bytes(..) as i64`, which reinterprets the same bits. **Alternative (untested):** port #1355 into a patched Aeneas library. It does not apply cleanly to the pin. | Workaround tested | Source change (workaround) or toolchain patch |
| B7 | Lean keyword used as an identifier | E09 helper | The pinned Aeneas does not escape `matches`, a Lean keyword, used as a local variable name. Fixed upstream in Aeneas #1306. | Rename the local to `is_match`. | Yes | Source change (name only) |
| B8 | Charon cannot name inherent-impl methods | All | `--start-from` rejects inherent impls, and the name matcher never matches an inherent-impl element (a `TODO` returning `false`, still present upstream). | Start from the module `rmcp::model::request_state`; use the `_` glob in the impl position for `--opaque`/`--exclude`. | Yes | None (tooling only) |
| B9 | Out-of-scope items break Lean compile | Build | The JSON wrappers pull in `serde` trait signatures that have no Lean definitions. The `Error` impl uses `source`, which the Aeneas `core::error::Error` model lacks. | `--exclude` `serde`, `serde_core`, the four JSON wrappers and the `Error` impl; keep `serde_json` `--opaque` (its `Error` type appears in `RequestStateError`). | Yes | None (outside target set) |
| B10 | Generated Lean not yet built in-repo | All | The pilot compiled against an existing Aeneas library build instead of the crate-local Lake project. | S03 builds the crate-local project with the pinned Aeneas; S18 reproduces from a fresh clone. | No | None |

### Adapter

The tested adapter changes only `crates/rmcp/src/model/request_state.rs`: 112 lines added and 63 removed, including formatting. In production code:

| Change | Blocker | Behaviour argument for review |
|---|---|---|
| `mod mac { struct MacState(HmacSha256); new, update, finalize -> [u8; 32], verify -> bool }` | B1 | `new`, `update`, `finalize().into_bytes()` and `verify_slice(..).is_ok()` are the same calls as before, moved behind a type. `verify` still uses `hmac`'s comparison. |
| `mac_v1`/`mac_v2` return `mac::MacState`; callers use `.finalize()` and `.verify(&tag)` | B1 | `?` on `verify_slice(..).map_err(..)` becomes `if !verify { return Err(IntegrityCheckFailed) }`, which returns the same error in the same order. |
| `mod b64 { encode_into, decode }` replaces the five `URL_SAFE_NO_PAD.encode_string` and five `.decode` call sites | B3 | Same engine, same calls; the error type is still `base64::DecodeError`, mapped exactly as before. |
| `mod dot { split, Parts::next }` replaces `sealed.split('.')` in `open_at`, `open_rs1_at`, `open_rs2_at` | B2 | `Parts::next` forwards to `str::Split::next`. |
| `KID_EMPTY_MSG`, `KID_TOO_LONG_MSG` constants | B4 | Same `&'static str` values. |
| `rs1_fallbacks_verify` helper; `if let … && …` let-chain replaces the guarded `matches!` | B5 | The loop body is unchanged. Every fallback is still tried; the empty-fallback check still comes before decoding. |
| `u64::from_be_bytes(..) as i64` | B6 | Bit-identical to `i64::from_be_bytes` on the same 8 bytes. |
| Local `matches` renamed `is_match` | B7 | Name only. |

Test-only changes: the `base64`/`hmac` trait imports move into `mod tests`, and one test drops a now-redundant `.into_bytes()`.

**Review checklist for the adapter commit:**
- [ ] The existing request-state tests and the Section 7 boundary tests pass.
- [ ] The HMAC test vectors (RFC 4231) pass through `MacState`.
- [ ] Tokens sealed before and after the change are byte-identical, for fixed keys and inputs. Add a regression test that pins one rs1 and one rs2 token. *Pre-checked in the pilot:*
  - **Setup:** three codecs (single key; ring sealing rs2 with a multibyte kid; ring sealing rs1 with a fallback), each sealing three payload/associated-data pairs, then `open_with` on each token and five tampered variants.
  - **Result:** 9 tokens and 153 `open` results, byte-identical between the original and the adapted code. The results cover `Ok`, `IntegrityCheckFailed`, `InvalidEncoding`, `MalformedFormat` and `UnknownKeyId`.
  - **Not covered:** `Expired` and `InvalidKeyId`, so the regression test still has to be added.
- [ ] Nothing outside `request_state.rs` changes; the public API is unchanged.

**What the adapter moves into the trusted boundary.** The bodies of `MacState`, `b64` and `dot` are small Rust functions that are *not* extracted; they are covered by contracts (Section 4) and tests. This is a narrower and more explicit trust boundary than the original plan's contracts on the `hmac` and `base64` crate APIs.

### Extraction command (with adapter)

```sh
cd crates/rmcp
R=rmcp::model::request_state
M="$R::_"                                   # `_` matches the inherent impl (B8)
env RUSTUP_TOOLCHAIN=nightly-2026-06-01 "$CHARON" cargo --preset=aeneas --hide-marker-traits \
  --start-from $R \
  --opaque $R::mac --opaque $R::dot --opaque $R::b64 --exclude $R::HmacSha256 \
  --opaque zeroize --opaque base64 --opaque thiserror --opaque chrono --opaque serde_json \
  --opaque "$M::now_ms" \
  --exclude serde --exclude serde_core \
  --exclude "$M::seal_json" --exclude "$M::seal_json_with" \
  --exclude "$M::open_json" --exclude "$M::open_json_with" \
  --exclude "$R::{impl core::error::Error for $R::RequestStateError}" \
  --dest-file /tmp/RmcpRequestState.llbc -- \
  --no-default-features --features request-state --lib
"$AENEAS" -backend lean /tmp/RmcpRequestState.llbc \
  -dest lean/Rmcp -split-files -emit-json -no-progress-bar
```

Aeneas exits with code 1 because of the seven out-of-scope bodies. `scripts/extract.sh` must treat that as success only if no target is among the failures; it should check the target list against the Aeneas log, not the exit code. Then copy the two `*_Template.lean` files to `TypesExternal.lean` and `FunsExternal.lean` and replace their axioms with reviewed models (S08–S09).

### Upstream

The pilot read upstream Aeneas `main` (`2e3d4488`, 20 November 2026) and its Charon pin (`0.1.322`) without building them:

| Item | Status upstream |
|---|---|
| B6 `from_be_bytes` | Fixed (#1355) |
| B7 keyword escaping | Fixed (#1306) |
| B5 loop fixed point | Possibly improved (#1348, "join the break contexts from two iterations"); untested |
| B1 mixed type/trait recursion | Still rejected ("Detected groups of mixed mutually recursive definitions") |
| B4 "no bottoms" | Error still present; untested |
| B8 inherent-impl patterns | Still a `TODO` |
| B2 `Pattern` GAT | Unknown; untested |

**Upgrading the pin would therefore not remove the adapter.** It would remove only the B6 and B7 workarounds, at the cost of:
- a new Rust nightly (`2026-09-17`);
- a new OCaml dependency (`ppx_deriving_hash`, not in the current opam switch);
- the Lean module-system migration in Aeneas (#1230);
- diverging from host_origin's pin.

**Recommendation:** stay on the pinned toolchain for this sprint, and re-evaluate the upgrade afterwards.

File minimal reproducers upstream (S04b) for B1, B2, B4 and B5; B8 should go to Charon. Each reproducer should be a single-file crate that fails with the pinned toolchain, and should note whether upstream `main` still fails once it can be built.

### What remains unresolved

- **B10:** the crate-local Lake build (S03) has not been done; the pilot compiled only against an existing library build.
- **B6:** the alternative of porting #1355 into a patched pinned library, which would keep E01's decoding line unchanged, is untested.
- **Contracts:** the external declarations in the target closure are still axioms. Their contracts (S08–S09) and models are the next real work; the adapter makes their boundary concrete but does not prove anything about it.

## 10. Claude agent stack

The lead is the main Claude Code session. It owns the board, integrates changes, and is the only writer of shared files: generated `Rmcp/` output, the import roots, and `lakefile.lean`. Workers run in separate git worktrees.

| Role file | Responsibility | May edit |
|---|---|---|
| `mcp-extraction.md` | Run Charon/Aeneas, list external declarations, write reproducers for blockers | `scripts/`, `Rmcp/*External.lean`, `verification/pilot.md`, `blockers/` |
| `mcp-spec.md` | Draft specifications, contracts and assumption entries, each clause citing the Rust lines or plan section it encodes | the assigned `Specs/…` file, the statement in `Theorems/…`, `verification/assumptions.yaml` (proposed entries) |
| `mcp-lean.md` | Prove one accepted spec against the generated code | the assigned `Proofs/…` file |
| `mcp-review.md` | Boundary tests, contract test vectors, challenge specs and assumptions with `AI_PR_REVIEW_QUESTIONS.md`; may propose labelled replacement statements | `mod tests` in `request_state.rs`, review notes |

Start with the lead and two workers (extraction and review). Add the spec worker when S05 starts, and the Lean worker once generated code and an accepted spec exist. One heavy build at a time until memory use is measured.

Template for `.claude/agents/mcp-lean.md`:

```markdown
---
name: mcp-lean
description: Prove one reviewed request-state spec against the Aeneas-generated Lean code.
---
Read CLAUDE.md and the task given by the lead.
Edit only the assigned file under crates/rmcp/lean/Proofs/.
Do not change theorem statements, specs, generated files, or contracts.
Do not prove a spec that this session drafted.
Do not add axioms or sorry. Follow docs/STYLE_GUIDE.md.
Report the exact commands run, exit status, theorem names, and any open goal.
If the spec appears false, return a concrete counterexample instead of weakening it.
```

Template for `.claude/agents/mcp-spec.md`:

```markdown
---
name: mcp-spec
description: Draft one request-state specification or external contract for human review.
---
Read CLAUDE.md, docs/WORKFLOW_AND_PR_GUIDE.md, docs/STYLE_GUIDE.md and the task given by the lead.
Edit only the assigned Specs/ or Theorems/ file and proposed entries in assumptions.yaml.
Cite, for every clause, the Rust lines at the pinned commit or the plan section it encodes.
Cover the Ok case and every Err case, in the Rust order of checks.
Never set spec: REVIEWED, never accept a task, never prove a spec you drafted.
Report the drafted statements, their sources, and any behaviour you could not pin down.
```

Rules for every worker:
- Role prompts do not restrict anything by themselves. Enforce edit limits with permission settings and review each diff before merging.
- Two agents agreeing is not a review. A human spec owner accepts every spec and every final claim.
- An AI agent may draft a specification, but the drafter may not prove or AI-review the same statement. AI drafting is disclosed in the PR footer and recorded in the evidence file (workflow guide, "AI contributions").
- Re-extracting after any source change invalidates earlier proof evidence for the affected functions.

## 11. Results template

To be filled in only with actual results in `docs/RESULTS.md`:

> At SDK commit `[SHA]`, built with `--features request-state`, the following existing request-state codec functions are verified against Aeneas-generated Lean semantics: `[list]`. These results assume the HMAC-SHA256, Base64url, standard-library and codec-state contracts listed in `verification/assumptions.yaml`. They do not establish cryptographic security, constant-time execution, or correctness of the public wrappers. Functions not listed are open or blocked for the reasons given below.

## 12. Deferred to a later sprint

These were considered and deliberately left out to keep the sprint focused on extraction and proofs. Add them only once the core results exist.

- Public wrappers `seal_at`, `seal_with`, `open_with`, and the constructors (which would remove the codec-state assumption).
- A public-definition audit (`Checks/Definitions.lean`) and a coverage audit with negative test files.
- Mutation testing.
- Per-claim cards and per-run agent provenance records, beyond the tool-and-model line that evidence files and function records already require.
- A translation-drift CI workflow.
- Moving `verification/host_origin/` into the crate-local Lean project.
