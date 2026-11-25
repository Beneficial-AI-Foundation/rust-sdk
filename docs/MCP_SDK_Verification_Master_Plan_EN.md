# MCP SDK Verification — Master Plan

Date: 23 November 2026. This is the single current plan. It covers two project phases:

| Phase | Scope | Status | Sections |
|---|---|---|---|
| **Phase 1** (request-state codec) | 25 targets: W01–W15 (`request_state_wire`, created by translation patch 01) and E01–E11, E09a (`RequestStateCodec`), plus 5 composition theorems | Proofs done: all 25 specified, signed off and proved; linkage `patch-01` (patch 01 reviewed and signed off 2026-11-23, `STATUS.md` "Open items"); the human items of S01–S04a are still open | 1–12 (the record; section numbers unchanged because `formal/`, `STATUS.md` and the guides cite them) |
| **Phase 2** (protocol, transport and SSRF foundations) | 25 new targets: existing upstream functions M01–M14, T01–T08, A01–A03, plus 5 composition theorems | Planned; translation measured in a pilot (Section 14) | 13–25 |

"Phase 1/Phase 2" name project phases. "Phase A/B/C" inside a project phase still name the process stages of Section 8 (crate-wide translation, per-function pipeline, refinement).

**Current state (23 November 2026).**
- **Phase 1:** all 25 targets and the composition theorems are specified, signed off by the spec owner and proved. Steps S05–S16, S18 and S19 are accepted (`formal/docs/board.yaml`; results in `formal/docs/STATUS.md`, "Results"). The results are about upstream `origin/main` `7caec76` plus translation patch `formal/trusted/patches/01-request-state-wire.patch` (D2 fallback, human decision 2026-11-23): every SDK `*.rs` file is byte-identical to `7caec76`, the refactor and its tests exist only in the patched copy, and every target's linkage is `patch-01` (D10: 0 verified on original code, 25 proved with translation patch 01, 0 open).
- **Phase 2:** a pilot on 23 November 2026 measured about 60 existing upstream functions with the pinned toolchain (Section 14: 25 selected, about 30 not taken, 6 held in reserve). It selected 25 that translate **from the unmodified upstream source**, with no translation patch, no `sorry`, no Aeneas error, no hand edit and no dependency on the Aeneas `core.fmt.Formatter` axiom. The 25 coexist in one Charon/Aeneas run with the Phase 1 targets, every Phase 1 generated block stays byte-identical, and the result compiles in Lean under `warningAsError`. Their translated definitions are identical (up to the `Source:` line numbers in docstrings) whether or not patch 01 is applied, so all 25 can reach linkage `ORIGINAL`, which no Phase 1 target has.
- **Waiting on the human owner (both phases):** naming the project owner and budget for both phases (S01; Phase 2: H5, which blocks S20 acceptance; H1–H4 were accepted on 2026-11-23 and the Phase 2 spec owner is Hoang Le Truong, Section 21, "Human decisions"); the open human items of S02, S03, S04 and S04a; running the three CI workflows on GitHub for the first time (needs a pull request; S17). See `formal/docs/STATUS.md`, "Open items".

## Fixed requirements

| Requirement | Section |
|---|---|
| Verify existing SDK functions, and the new public `request_state_wire` functions they are built on (since the D2 fallback, 2026-11-23: in the patched copy); no replacement of the `hmac`, `sha2` or `base64` crates | 1, 2 |
| Every target is a concrete function in the pinned source, with an independent specification | 2, 3, 16, 17 |
| New functions are public, foundational (pure byte/integer logic, no I/O) and reusable outside the codec | 2 |
| Every target translates with the pinned toolchain; no target may depend on an unresolved blocker | 2, 9, 14 |
| Functions that cannot be translated with the pinned toolchain are excluded from the project, not deferred | 2.3, 9, 16.5 |
| Layout and process of `VERIFICATION.md`: a single `formal/` folder, one translated configuration, spec files restating each theorem (as `theorem Theorems.…`) with `#print axioms` checks | 5, 9, 15, 20 |
| Aeneas pinned by one GitHub release tag in `formal/lakefile.toml`, read by both scripts | 5 |
| Patches, axioms and spec statements are reviewed by multiple independent agents, then signed off by a human | 4, 6, 10, 21 |
| CI checks that the translation is current, the Lean project builds, and the patched copy passes the crate's tests | 5, 8, 19 |
| Process: crate-wide translation and review once, then a per-function spec → review → sign-off → proof pipeline, then proof refinement once at the end | 8, 21 |
| Two-week sprint with measured feasibility gates | 8, 21 |
| Operational Claude agent stack | 10 |
| Ordered steps with exact files, timing and ownership | 8, 21 |
| Explicit status and acceptance evidence per function | 6, 7, 22 |
| Stated security scope, trusted base and reproducibility | 1, 4, 11, 13, 18 |
| AI may draft specifications; a named human spec owner accepts every one | 6, 10, 21 |
| **Phase 2:** 25 new targets, each an existing upstream function that translates without any change to the Rust code (no SDK edit and no translation patch that touches translated code); linkage `ORIGINAL`, checked mechanically | 13, 14, 19 |
| **Phase 2:** each target is a foundation that later phases reuse: its theorem is a lemma for a named larger function | 13, 23 |
| **Phase 2:** the same bar as Phase 1: every target measured to translate and compile before the plan commits to it; same review, sign-off and CI gates; no axiom in `trusted/` | 14, 18, 21 |

**Requirement changes.**
1. 22 November 2026 (by the user): the plan was extended from existing functions only to new public functions that Aeneas supports, and every unresolvable blocker was removed from the plan (third and fourth rows).
2. 22 November 2026 (by the user): every function that cannot resolve its blockers is removed from the project (fifth row). Under the process guide, "removed" means listed in Charon's `exclude` setting (Section 2.3).
3. 22 November 2026 (by the user): `VERIFICATION.md` was adopted as the process. It replaces the earlier crate-local `crates/rmcp/lean/` project with `Specs`/`Theorems`/`Proofs`/`Checks` libraries, the hand-written extraction command, `verification/manifest.yaml` and `verification/assumptions.yaml` (rows six to nine).
4. 23 November 2026 (by the user): Phase 2 adds 25 new targets that need no modification of the Rust code, are reusable in later phases, and meet the Phase 1 success bar (last three rows).

Change a requirement only when the user changes it, or a documented technical incompatibility forces an explicit decision.

**Governing guides.** `VERIFICATION.md` defines the process: layout, scripts, Charon settings, patches, axioms, spec files and CI. This plan defines scope, targets, steps and status for both phases. Four further guides under `docs/` define how work is written, submitted and reviewed. If any two disagree, fix whichever is wrong in the same PR.

| Guide | Covers |
|---|---|
| [`VERIFICATION.md`](VERIFICATION.md) | The Aeneas process: `formal/` layout, install and translate scripts, Charon settings, patches, external axioms, spec files, proofs, CI |
| [`WORKFLOW_AND_PR_GUIDE.md`](WORKFLOW_AND_PR_GUIDE.md) | Generated files, translation, status records, PR format, trust rules, AI contributions |
| [`STYLE_GUIDE.md`](STYLE_GUIDE.md) | Lean headers, tactics, library layering, `Defs` definitions, spec file layout |
| [`REVIEWER_GUIDE.md`](REVIEWER_GUIDE.md) | Review criteria and steps, including review of AI-drafted specifications |
| [`AI_PR_REVIEW_QUESTIONS.md`](AI_PR_REVIEW_QUESTIONS.md) | Checklist and report format for AI-assisted PR review |

> The four `docs/` guides were aligned with this plan on 22 November 2026 (`formal/` layout, the Lean build gate, spec files with `#guard_msgs`, `STATUS.md`, independent agent reviews, phases A–C). S20 updated them for Phase 2: the spec- and proof-file paths and theorem names of Section 20, the M/T/A function IDs, the linkage check of Section 19 and the H3 test rule. The translated-configuration text, feature flags and procedure commands of `WORKFLOW_AND_PR_GUIDE.md` and `AI_PR_REVIEW_QUESTIONS.md`, and the module docstrings of the Phase 1 spec files, change with the configuration at S21.

---

# Part I — Phase 1: request-state codec (record)

Sections 1–12 are the Phase 1 plan as executed. Where they say "this plan", "this sprint" or "the targets", they mean Phase 1. They are kept, with their numbering, because `formal/`, `STATUS.md`, the guides and the CI workflows cite them, and Phase 2 reuses their rules: layout, CI, status model, trusted-base rules and agent stack. Notes marked **Phase 2** point to the Part II sections that change a Phase 1 setting.

## 1. Source baseline and scope

- **Repository:** https://github.com/truonghoangle/rust-sdk (the user's fork of the Rust MCP SDK).
- **Base commit:** `0e2396f73a88617141b31f645de6f1171ed5f993`. The current `main` (`7caec76`) adds only `verification/host_origin/`, and `crates/rmcp/src/model/request_state.rs` is byte-identical between the two (SHA-256 `41e69cad94869be4b93120f3cd39a10fad4a3730585240b712c2ada1b311b416`).
- **Pinned commit:** the fork commit that lands the `request_state_wire` refactor (S04a). Record it in `formal/docs/STATUS.md`. **D2 fallback (human decision 2026-11-23).** The refactor was not landed; the pinned commit is upstream `origin/main` `7caec76`, every SDK `*.rs` file is byte-identical to it, and the refactor is translation patch 01 (Section 9, "Refactor"). From then on, the translation CI (Section 5) guarantees that the committed translation matches the Rust source in the repository (since the D2 fallback: that source with patch 01 applied), so no separate hash check is needed.
- **Target files** (since the D2 fallback, in the patched copy `.llbc/work/` only; line numbers refer to it):
  - `crates/rmcp/src/model/request_state_wire.rs` (new, public; created by patch 01)
  - `crates/rmcp/src/model/request_state.rs` (refactored onto it by patch 01)
- **Feature:** both files compile only with the `request-state` feature (`crates/rmcp/Cargo.toml`, `request-state = ["dep:hmac", "dep:zeroize", "base64"]`).
- **Translated configuration (single target):** `--target x86_64-unknown-linux-gnu --no-default-features --features request-state --lib`, fixed in `scripts/aeneas-translate.sh`, with overflow checks and debug assertions pinned on: every cargo call (also through Charon) gets `--config profile.dev.overflow-checks=true --config profile.dev.debug-assertions=true`, so arithmetic panics on overflow, which is what Aeneas models as failure. Nothing else may change the build: the script refuses environment variables that change how cargo or rustc build (`RUSTFLAGS`, `RUSTC*`, `RUSTDOC*`, `CHARON_*`, `AENEAS_*`, every `CARGO_*` outside a short allowlist, and every `RUSTUP_*` except `RUSTUP_TOOLCHAIN` and `RUSTUP_HOME`), a selected `rustc` whose `rustc -vV` is not the pinned nightly, a `.cargo/config` or `.cargo/config.toml` in the source, the work copy or any ancestor of it, and `[profile]`, `[patch]`, `[replace]` or `cargo-features` in the workspace or `crates/rmcp` manifest; it runs cargo with an isolated `CARGO_HOME`, requires every dependency of `rmcp` in this configuration to come from crates.io at the pinned versions (Section 4), and requires the build script to be `crates/rmcp/build.rs` with the sha256 pinned in the script (`BUILD_RS_SHA256`) and an empty output (exact lists: `formal/README.md`, "Translated configuration"). **The proofs hold only for this configuration.** It is stated in `formal/README.md` and in the module docstring of each spec file. The pilot ran on macOS aarch64 without `--target`; S03 records whether the output differs.
- **Phase 2:** the feature list is widened to `request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth` (Section 15; human decision H1). The pilot showed the Phase 1 translation byte-identical under the widened list (Section 14).

**Scope decision (VERIFICATION.md §0).** Aeneas handles pure, sequential, safe Rust well. The request-state codec is mostly that: framing, parsing, length checks and byte transcripts. The parts that are not (HMAC and Base64 crate internals, the system clock, `serde` JSON wrappers, formatting impls) are either behind four opaque primitives with hand-written models (Section 4) or excluded (Section 2.3). The verification concentrates on the byte logic underneath them.

**Objective:** implementation-linked correctness of the request-state codec — framing, configuration checks, version dispatch, token parsing, MAC transcripts, expiry, and seal/open round-trip. It holds under explicitly named contracts for HMAC-SHA256, Base64url and the standard-library operations the code uses. Most of this correctness is proved once, on the public wire functions, and reused by the codec.

**Not claimed:**
- HMAC unforgeability or any other cryptographic security property;
- constant-time behaviour of the compiled code;
- correctness of the `hmac`, `sha2`, `base64` or `zeroize` crates;
- any excluded function (Section 2.3);
- the translatable public wrappers `open`, `open_with`, `new` and `try_new`, which are not targets;
- any configuration other than the one above;
- full MCP protocol verification.

Claims apply to the pinned commit and configuration only (since the D2 fallback, 2026-11-23: with translation patch 01 applied), not to upstream releases.

## 2. Targets

### 2.1 Public foundation: `rmcp::model::request_state_wire` (new)

**D2 fallback (human decision 2026-11-23).** "New" and "public" below describe the patched copy: the module exists only after translation patch 01 is applied (Section 9, "Refactor"); the SDK sources at `7caec76` do not contain it.

These are module-level `pub fn`s that use only slices, integers, fixed arrays and `Vec<u8>`. Each one is useful outside the codec, for example to a client or a gateway that inspects a token's version, or to tooling that builds test vectors. All fifteen translated in run 3.

| ID | Function | Independent specification |
|---|---|---|
| W01 | `b64_len(len: usize) -> usize` | `4 * ceil(len / 3)` on the domain where it fits in `usize` (equal to `len.div_ceil(3) * 4`, without calling `div_ceil`) |
| W02 | `key_length_ok(len: usize) -> bool` | `len ≥ MIN_KEY_LENGTH (32)` |
| W03 | `check_kid_len(len: usize) -> Result<(), KidError>` | `0` → `Empty`; `> 255` → `TooLong`; otherwise `Ok` |
| W04 | `bytes_eq(a: &[u8], b: &[u8]) -> bool` | `a = b` as byte lists |
| W05 | `next_dot(s: &[u8], start: usize) -> usize` | least `i ≥ start` with `s[i] = '.'`, otherwise `s.len()` |
| W06 | `component_count(s: &[u8]) -> usize` | `(splitOn '.' s).length` = 1 + number of `.` bytes |
| W07 | `version_of(s: &[u8]) -> Option<Version>` | first `splitOn '.'` component `= "rs1"` → `V1`, `= "rs2"` → `V2`, otherwise `None` |
| W08 | `parse_rs1(s: &[u8]) -> Option<Rs1Parts>` | `Some {body, tag}` iff `splitOn '.' s = ["rs1", body, tag]` |
| W09 | `parse_rs2(s: &[u8]) -> Option<Rs2Parts>` | `Some {kid, body, tag}` iff `splitOn '.' s = ["rs2", kid, body, tag]` |
| W10 | `transcript_v1(ad, body) -> Vec<u8>` | `DOMAIN_V1 ++ be64(len ad) ++ ad ++ body` |
| W11 | `transcript_v2(kid, ad, body) -> Vec<u8>` | `DOMAIN_V2 ++ be64(len kid) ++ kid ++ be64(len ad) ++ ad ++ body` |
| W12 | `decode_expiry(head: [u8; 8]) -> i64` | two's-complement value of the big-endian bytes |
| W13 | `is_expired(expiry: i64, now_ms: i64) -> bool` | `expiry ≠ 0 ∧ now_ms > expiry` |
| W14 | `open_frame(body: &[u8], now_ms) -> Result<&[u8], FrameError>` | `len < 8` → `TooShort`; W13 on W12 of the first 8 bytes → `Expired`; otherwise `Ok(body[8..])` |
| W15 | `frame(expiry: i64, payload: &[u8]) -> Vec<u8>` | `be64(expiry as u64) ++ payload` |

The public types `KidError`, `Version`, `FrameError`, `Rs1Parts` and `Rs2Parts` are `#[non_exhaustive]`. The public constants are `VERSION_V1/V2`, `DOMAIN_V1/V2`, `EXPIRY_LEN`, `MIN_KEY_LENGTH`, `MAX_KID_LEN`, `MAX_ENCODED_KID_LEN` and `TAG_LEN`. The codec takes its constants from this module, so each value is defined in exactly one place, with four recorded exceptions, each with its own reason: (1) the codec keeps `VERSION_V1`/`VERSION_V2` as `&str` constants (`"rs1"`, `"rs2"`) next to `wire::VERSION_V1`/`V2: &[u8]`, because deriving them with a `const` `str::from_utf8(wire::VERSION_V1)` initializer would give Charon a global whose body can panic (the `Result` has to be unwrapped; not tried on this tree); (2) the "255" inside the E04 message constant `KID_TOO_LONG_MSG` stays a literal, because E04 (Section 2.2, B4) must keep its `InvalidKeyring` messages as `&'static str` constants with the base text, and a `const` formatter would face the same panicking-global problem; (3) the private alias `MAX_ENCODED_KID_LEN = wire::MAX_ENCODED_KID_LEN` is an alias, not a second literal; (4) `prim::hmac_sha256` returns `[u8; 32]` rather than `[u8; TAG_LEN]`, so that the S08 axioms are stated against a stable signature. The test `codec_constants_agree_with_wire` (and, for (4), tag-length checks on `wire::TAG_LEN`) checks that they agree with the wire constants (the S04a evidence (git history at 223ff12), "Deviation from plan §2.1/§9 'defined once'").

**Opaque primitives** (`request_state_wire::prim`, public, listed in Charon's `opaque` setting, covered by the external models of Section 4):

| Function | Wraps |
|---|---|
| `hmac_sha256(key, msg) -> [u8; 32]` | `Hmac<Sha256>::new_from_slice`, `update`, `finalize` |
| `hmac_sha256_verify(key, msg, tag) -> bool` | the same, then `verify_slice(tag).is_ok()` (constant-time compare kept) |
| `b64_encode_into(input, out: &mut String)` | `URL_SAFE_NO_PAD.encode_string` |
| `b64_decode(input: &[u8]) -> Option<Vec<u8>>` | `URL_SAFE_NO_PAD.decode(..).ok()` |

These four are the entire trusted boundary to the crypto and encoding crates. They meet the guide's bar for `opaque`: their bodies use HMAC and `Engine` types that cannot be translated (B1, B3), and there is no useful Rust model to patch in.

**Aeneas-safe coding rules for the wire module.** Each rule comes from a measured failure (Section 9), and reviewers check new public functions against it:
1. Use free functions, not inherent methods (B8).
2. Take `&[u8]`, not `&str` patterns (B2).
3. No `&[&[u8]]` or other nested borrows (B11).
4. No HMAC or `Engine` types in signatures (B1, B3).
5. Return error enums, not `&'static str` literals (B4).
6. No identifiers that are Lean keywords (`from`, `prefix`, `matches`, …; B7).
7. No `div_ceil` or `is_multiple_of`, which have no model in the pinned library.
8. Loops are index `while` loops over shared slices.

### 2.2 Existing codec functions (refactored onto the foundation)

These are associated functions of `RequestStateCodec`. Since the D2 fallback (2026-11-23) the refactoring is patch 01, so the verified bodies are those of the patched copy. Line numbers will be filled in from the pinned commit at S01.

| ID | Function | Independent specification | Built on |
|---|---|---|---|
| E01 | `open_authenticated_body` | `TooShort` → `MalformedFormat`, `Expired` → `Expired`, `Ok p` → `Ok(p.to_vec())` | W14 |
| E02 | `b64_len` | equals W01 | W01 |
| E03 | `validate_key_length` | `Ok` iff `len ≥ 32`; otherwise `KeyTooShort { minimum: 32, actual: len }` | W02 |
| E04 | `validate_config_kid` | `Ok` iff the UTF-8 byte length is in `1..=255`; empty and too-long give their two distinct `InvalidKeyring` messages (`const`s) | W03 |
| E07 | `seal_rs1` | Output = `"rs1." ++ b64(body) ++ "." ++ b64(tag)`, `tag = hmacSha256(key, W10 ad body)` | E02, W10, prims |
| E08 | `seal_rs2` | Output = `"rs2." ++ b64(kid) ++ "." ++ b64(body) ++ "." ++ b64(tag)` with W11 | E02, W11, prims |
| E09 | `open_rs1_at` | Exact error order (Section 3); accept iff some configured key verifies the tag; then E01 | W08, W10, E09a, E01 |
| E09a | `rs1_fallbacks_verify` (private helper) | `true` iff some fallback's key verifies; tries every fallback | prims, `HashMap::get` |
| E10 | `open_rs2_at` | Exact error order (Section 3); MAC binds kid, ad and body; then E01 | W03, W09, W11, E01 |
| E11 | `open_at` | `V1` → E09, `V2` → E10, `None` → `MalformedFormat`; result passed through unchanged | W07 |

IDs E05 and E06 are unassigned: they belonged to `mac_v1`/`mac_v2`, which are deleted (Section 2.3). The IDs are not renumbered, so the guides' references stay valid. E03/E04 are used only when constructing a codec; the opening functions do not call them. The ID order is a work queue, not a call graph.

**Total:** fifteen W targets, nine E targets and one helper (E09a). Every one of them has a translated body in run 3.

### 2.3 Excluded from the project

These functions cannot be translated with the pinned toolchain, and no change inside this project's scope resolves them. They are excluded, not deferred: they get no function record, no specification and no proof. They appear in the `exclude` list of `[package.metadata.charon]` (Section 9), each with a comment giving its blocker, and no target calls any of them (VERIFICATION.md §3: nothing we verify may depend on an excluded item). Re-adding one needs a requirement change by the user and a new translation run that shows the blocker resolved — preferably by a translation patch (VERIFICATION.md §4), never by `opaque`.

| Function | Blocker with the pinned toolchain | How it leaves the project |
|---|---|---|
| `mac_v1`, `mac_v2` (were E05, E06) | B1: HMAC types in the return type | Deleted from the source by the refactor; replaced by W10/W11 and `prim` |
| `any_key_verifies` (proposed wire function) | B11: nested borrows in `&[&[u8]]` | Never added to the source |
| `seal_at` | Aeneas "Unreachable" error on the TTL computation | `exclude` |
| `seal_with`, `seal` | Call `seal_at` | `exclude` |
| `new_with_keyring` | Aeneas internal error | `exclude` |
| `with_rs1_signing`, `with_rs1_fallback` | B4: "no bottoms in the value" | `exclude` |
| `Debug`/`Display` for `RequestStateError`, `Debug` for `RequestStateCodec` | Aeneas type assertion and internal error | `exclude` |
| `seal_json`, `seal_json_with`, `open_json`, `open_json_with`, `Error` for `RequestStateError` | B9: `serde` signatures; `Error::source` not modelled | `exclude` |

**Consequences:**
- The round-trip theorems compose E07/E08 with E09–E11 directly; no seal wrapper is verified.
- The codec-state invariant of Section 4 is permanently a hypothesis, because the constructors that establish it are excluded.
- `open`, `open_with`, `new` and `try_new` do translate. They stay in the source and in the generated Lean, but are not targets. (Amendment, human request 2026-11-24: these and the `SealOptions` builder and `new_unchecked` are specified as R01–R08, the public `request_state.rs` API; the other nine public functions are R09–R17 once translated; tracked in `formal/docs/STATUS.md`, "Public request_state.rs API", and `formal/docs/functions/R*.yaml`.)

**Amendment (translation patch 03 v2, human decisions 2026-11-24: targets R09–R15, variant A "minimal Rust change"; reviewed and signed off 2026-11-24; specs signed off, proved and committed in `0cbd67f`, accepted 2026-11-25).** On the toolchain of Section 26 (Aeneas `nightly-2026.11.24-fb44cb4`) the table above no longer holds for eight rows' functions. `with_rs1_signing`, `with_rs1_fallback` and `new_with_keyring` translate with only their `exclude` entries removed (B4 and the B13 internal error are gone). `seal_at` (and so `seal`, `seal_with`) and `open_json`, `open_json_with` translate with translation patch `formal/trusted/patches/03-request-state-public.patch` (+6/−2 non-test lines: `let ttl = options.ttl;` before the `match` in `seal_at`, which avoids the "Unreachable" error; an explicit `match` in place of `.map_err(RequestStateError::Deserialization)` in `open_json_with`, which avoids the unsupported `FnOnce` impl of a variant constructor) and with the crate `serde_core` moved from `exclude` to `opaque` (Section 9 amendment). Still excluded: `seal_json`, `seal_json_with` (B9, narrowed), the `Error`, `Debug`/`Display` and derived `Debug` impls. The public `request_state.rs` API is numbered R01–R17: R01–R08 (`SealOptions::{new, associated_data, ttl}`, `RequestStateCodec::{new, new_unchecked, try_new, open, open_with}`) are specified, signed off and proved; R09–R15 (`seal`, `seal_with`, `with_rs1_signing`, `with_rs1_fallback`, `open_json`, `open_json_with`, `new_with_keyring`) translate with patch 03 v2 and are to be specified next (no statement yet); R16–R17 (`seal_json`, `seal_json_with`) stay excluded, blocked upstream (Section 9 amendment). Once a keyring constructor is verified, the codec-state invariant of Section 4 can be derived for the codecs it builds instead of only assumed; until then the consequences above stand. (Amendment 2026-11-25: R09–R15 are specified (spec cycle of 4 review rounds; signed off by the spec owner 2026-11-25), together with the internal statements R10a (`seal_at` at an explicit time) and R10b (`seal_at` then `open_at`, the translated round trip) and a model round trip; R15 (`new_with_keyring`) states that every codec it returns is `CodecValid`. Their incorporation (Lean statements and proofs, records `formal/docs/functions/R09.yaml`–`R15.yaml`) is done, committed in `0cbd67f` and accepted by the human 2026-11-25; R16–R17 remain the only uncovered public functions. The clock rule of Section 4 is extended to `open_json`/`open_json_with` and its `seal`/`seal_with` wording changed, see the Section 4 Clock row.)

**Amendment (2026-11-25, public `skill.rs` API, targets K01–K20; human decisions 2026-11-25: all twenty targets, translation patch 04 with hunks H1–H9, opaque SHA-256/NFKC/General_Category functions whose laws enter statements only as premises (no axiom), the script change for the `_::new` and `_::with_meta` globs (Section 15, rule 3), 13 targets ORIGINAL; translation stage and specifications signed off by the spec owner 2026-11-25).** The twenty public functions of `crates/rmcp/src/model/skill.rs` (upstream `7caec76`, unmodified in the repository) are added as targets K01–K20: `Resource::is_directory`, `SkillsCapability::{new, with_directory_read}`, `SkillResource::{new, from_bytes, verify}`, `sha256_digest`, `SkillFrontmatter::{new, with_field}`, `Skill::{new, with_meta, name, validate}`, `skill_name_from_uri`, `is_sha256_digest`, `validate_skills`, `GetSkillResult::{new, with_ttl_ms, with_cache_scope, with_meta}`. None is excluded. K01–K04, K08–K12 and K17–K20 translate from the unmodified source (linkage `ORIGINAL`, checked by `scripts/check-original-linkage.sh`, Section 19 amendment 2026-11-25); K05–K07 and K13–K16 translate with translation patch `formal/trusted/patches/04-skill-public.patch` (a private module `prim` of twelve one-line wrappers of the original expressions, opaque in the translation and modelled in `formal/trusted/`, and hunks H1–H9 that use them or loops without an early return, keeping the computed values; linkage `patch-04`). The translation stage passed 3 review rounds. 51 statements (20 spec theorems, 3 corollaries, 10 compositions, 18 consequences of the model; definitions `formal/specs/Defs/Skill.lean`) passed a spec cycle of 3 review rounds, were signed off by the spec owner 2026-11-25 and are proved (`formal/proofs/Proofs/Model/Skill/`); records `formal/docs/functions/K01.yaml`–`K20.yaml`; the public restatement is `formal/specs/Specs/Model/Skill.lean`. Patch 04 induces premises the original code would not need: `NfkcFits` (the patched copy collects NFKC forms into a `Vec<char>`), stated as a domain restriction of K13 and K16, and the URI-size part of `SkillFits`/`UriFits` (the patched `prim::split_slash`/`split_percent` collect their parts into a `Vec<String>`), met by every value held in memory. Not covered: caller conversions with side effects, SHA-256 for inputs of at least `2^61` bytes, the `HashSet` random source, the `serde_json` feature `preserve_order`. No bug was found. Tracked in `formal/docs/STATUS.md`, "Public skill.rs API (K01–K20)", and on the board as PATCH04-SKILL and SPEC-K01-K20 (both accepted by the human owner 2026-11-25; committed 061f014 and de7b8de).

## 3. Source behaviour that the specifications must capture

**What a spec means (VERIFICATION.md §6).** Aeneas translates each function into the `Result` monad, where panics, arithmetic overflow and out-of-bounds indexing become failure. A spec `f x ⦃ r => P r ⦄` therefore says that `f x` terminates without panicking and that its result satisfies `P`. Preconditions state when the function is guaranteed not to panic; a weaker precondition is a stronger result.

**W14/E01 — expiry.** `now_ms == expiry` is accepted. A negative nonzero expiry is compared as a signed value like any other. E01 performs no authentication; its theorem is about byte handling only.

**W01 and the seal capacities — arithmetic.** The workspace sets no `overflow-checks`, so debug builds panic on overflow and release builds wrap. Aeneas models overflow as failure, which matches debug builds only; the translation pins `overflow-checks=true` (Section 1). (W15 has no arithmetic: it builds its output with `Vec::new` and `extend_from_slice`, without `with_capacity`.) Every arithmetic theorem (W01, and the `with_capacity` sums in E07/E08) is therefore stated on the domain where no overflow occurs, and that domain is written into the theorem as a precondition. W01 also carries the lemma `b64_len n = (n.div_ceil 3) * 4` on that domain, which ties it to the original definition. Allocation failure is an explicit assumption, not a no-panic claim.

**Lean-model domains (notes for the S05 drafters; the spec owner decides at S05).** Some preconditions are needed only because the Lean model is more general than Rust:
- W06 `component_count` (and through it W08, W09, E09 and E10) needs `s.length < Usize.max` in Lean, stated as fewer than `Usize.max` `.` bytes: its counter `n` starts at 1 and `n + 1` can overflow on a slice of `Usize.max` bytes, which cannot exist in Rust (slices are at most `isize::MAX` bytes). E11 needs no such premise: it calls W08/W09 only on tokens whose first component is `"rs1"` or `"rs2"`, which therefore contain a byte other than `.` (spec-owner decision 2026-11-23, the S05 evidence (git history at 223ff12) open question (j)).
- W10, W11 and W15 need the total output length to be at most `Usize.max`, the precondition of the Lean model of `Vec::extend_from_slice`.

**W03/E04 — kid alphabet.** Any nonempty UTF-8 string of at most 255 bytes is accepted. Do not add an alphabet restriction to the specification.

**W06–W09 — splitting.** The specifications are stated with Lean's `List.splitOn '.'`, independent of the Rust loops. Splitting a UTF-8 string on the ASCII byte `.` gives the same components as `str::split('.')`, because no multibyte UTF-8 sequence contains `0x2E`. The pre-refactor review records this argument, and the token byte-identity tests check it. W08/W09 return `None` in exactly the cases where the original code returned `MalformedFormat` from its part checks.

**W10/W11 — transcripts.** HMAC over a concatenation equals HMAC with incremental `update` calls over the same bytes. This is how the refactor moves from `mac_v1`/`mac_v2` to a transcript plus one-shot `prim` calls without changing tags. The pinned token tests check it. Lengths are cast `usize → u64`; in the translation this is `UScalar.cast .U64` on `Usize`, which zero-extends and is exact whether `Usize` has 32 or 64 bits, so the theorems need no target-width hypothesis (S05 draft; the spec owner may restore one).

**E09 — error order.**
1. W08 returns `None` → `MalformedFormat`.
2. Ring codec with empty `rs1_fallbacks` → `UnknownKeyId` (before any decoding).
3. Body Base64 decode fails, then tag Base64 decode fails → `InvalidEncoding`.
4. Single key: one `hmac_sha256_verify`. Ring: E09a tries every fallback key without early exit; none matches → `IntegrityCheckFailed`. `keys.get(kid).expect(..)` must not fail, which needs the fallback clause of the codec-state predicate (Section 4).
5. E01 on the decoded body.

The loop that tries every key is a timing measure. The functional proof says nothing about timing.

**E10 — error order.**
1. W09 returns `None` → `MalformedFormat`.
2. Encoded kid longer than 340 → `InvalidKeyId`.
3. Kid Base64 decode fails → `InvalidEncoding`.
4. W03 rejects the decoded kid (empty or longer than 255) → `InvalidKeyId`; not UTF-8 → `InvalidKeyId`.
5. Single-key codec → `UnknownKeyId`; ring without that kid → `UnknownKeyId`.
6. Body, then tag decode → `InvalidEncoding`.
7. MAC mismatch → `IntegrityCheckFailed`.
8. E01.

Normalising these errors before they reach clients is an application obligation and outside this theorem.

**Round-trip.** The seal helpers take a body, not a payload. Each round-trip theorem states that opening returns `body[8..]`, under these conditions:
- the body is at least 8 bytes;
- expiry is 0 or `now ≤ expiry`;
- the associated data is the same.

For rs1, the opening codec is either the same single key or a ring whose `rs1_fallbacks` include the signing key. For rs2, the kid is valid UTF-8 of 1–255 bytes and the ring maps it to the signing key. `seal_rs2` accepts any kid, so round-trip holds only on that valid-kid domain. W15/W14 give the payload-level lemma `open_frame (frame e p) now = Ok p` when `¬ is_expired e now`.

## 4. External axioms and the trusted base

Aeneas translates only the crate. Every function it calls from outside (std functions the Aeneas library does not model, the `prim` functions, `now_ms`) is declared by hand in `formal/trusted/Rmcp/FunsExternal.lean` (types in `TypesExternal.lean`), starting from the generated `*External_Template.lean` files. Each contract describes a primitive on its own terms; no contract may assume that a target function (W or E) is correct.

**Decision (human, 2026-11-23): no axioms in the trusted base.** Every external is a Lean definition (functions) or `structure` (types) with the generated name and signature; what a model cannot compute is an `opaque` constant, which adds no axiom (`#print axioms` does not list it). The four opaque constants (five since S26/S27, which adds the abstract type `ExtModel.SerdeJsonValue`) are `ExtModel.hmacSha256`, `ExtModel.sipHash13`, `ExtModel.nowMs` and the type `ExtModel.SerdeJsonErrorImpl`. The laws the earlier design stated as axioms (Base64 round trip, `HashMap::get`) are theorems in `formal/proofs/Proofs/External/`. What remains trusted is that each definition describes its Rust function, with the stated exceptions in its docstring (evidence: `formal/trusted/evidence/README.md`).

| Contract | Model | Not established |
|---|---|---|
| **HMAC** (`prim.hmac_sha256`, `prim.hmac_sha256_verify`) | `opaque hmacSha256 : List U8 → List U8 → Array U8 32#usize` is the reference function. `def hmac_sha256 k m := ok (hmacSha256 k m)`. `def hmac_sha256_verify k m t := ok (t = hmacSha256 k m)` (as byte lists, so a wrong-length tag is rejected). Both always succeed (HMAC accepts keys of any length). Stated exception: the SHA-256 bit-length counter (`sha2-0.11.1/src/block_api.rs` line 66) overflows (a panic under overflow checks) for a message of at least `2^61 − 64` bytes or a key of at least `2^61` bytes (a long key is hashed by `get_der_key`); not modelled, as it lies outside the size convention of `FunsExternal.lean` (no claim about inputs of at least `2^61` bytes, which cannot exist on `x86_64`, whose address space is at most `2^57` bytes). | Cryptographic security; correctness of the `hmac`/`sha2` crates; constant time |
| **Base64url, no padding** (`prim.b64_encode_into`, `prim.b64_decode`) | `b64 : List U8 → List U8` and `b64Decode : List U8 → Option (List U8)` are **definitions** (RFC 4648 Section 5 alphabet, no padding, strict decoding), matching the `URL_SAFE_NO_PAD` engine: the decoder rejects padding, foreign bytes, length `≡ 1 (mod 4)` and non-canonical trailing bits. `b64_encode_into x out` appends `b64 x` to `out`; `b64_decode x = ok (b64Decode x)`. Theorems (`Proofs/External/Base64.lean`): `b64Decode (b64 x) = some x`; `b64Decode s = some y ↔ b64 y = s`; every output byte is in the URL-safe alphabet (no `.`); `(b64 x).length = (4n + 2) / 3`. Differential check against `base64 0.23.1` (`formal/trusted/evidence/differential/`). | Correctness of the `base64` crate beyond the tested inputs |
| **Standard library** | Value semantics for the operations in the target closure. Provided by the Aeneas library: `Vec::{with_capacity, extend_from_slice, push}`, `to_be_bytes`, `U64.from_be_bytes`, slice ranges, `Slice.to_vec`. Hand-written models, all **definitions**: `str::len`, `str::as_bytes`, `String::{with_capacity, push_str, push, as_bytes, from_utf8}`, `Option::ok_or`, `Result::{is_err, map_err}`, `Zeroizing` deref (identity on the wrapped value). `HashMap` is a structure holding an association list; `HashMap::get` is a definition (first entry with an equal key, no hashing); `RandomState`/`DefaultHasher` are structures with the opaque `sipHash13`. `ok` from a `String` model means "returns, or aborts or panics for memory reasons" (out of memory; amortized growth past `isize::MAX`). | Unlimited memory; hashing behaviour; zeroisation on drop |
| **Clock** (`now_ms`, opaque: reads the system clock) | `ok nowMs` with `opaque nowMs : I64`. Environmental assumption (not modelled): `chrono::Utc::now` panics if the system clock is before 1970 or outside chrono's range. One constant makes every reader of the clock pure, so **no spec statement mentions the functions `rmcp.model.request_state.RequestStateCodec.now_ms`, `…RequestStateCodec.open` or `…RequestStateCodec.open_with`** (review rule; a variable named `now_ms`, such as the time parameter of E01 `open_authenticated_body`, is not covered); `open`/`open_with` are translated but not targets, `seal_with` is excluded (amended 2026-11-24, translation patch 03: `seal_with` and `seal` translate and call `now_ms`; see the second amendment in the next column). | Two readings differ; clock correctness. Amendment (human decision 2026-11-24): only the spec theorems of `open` and `open_with` and their `Theorems.*` restatements may name these two functions and `ExtModel.nowMs`, and only with the postcondition `resultBytes result = openAt … ExtModel.nowMs.val`; their docstrings state the one-reading caveat and the inherited exceptions. No other statement names `ExtModel.nowMs`, no statement has a premise or conclusion about its value, and no statement involves two clock readings; `now_ms` itself stays unmentioned (`formal/README.md`, "Trusted base"). Amendment (human decision 2026-11-24, translation patch 03, which translates `seal_with`): the rule extends to `seal` and `seal_with`: no spec statement mentions `…RequestStateCodec.seal` or `…RequestStateCodec.seal_with` except their spec theorems and `Theorems.*` restatements, which may name these two functions and `ExtModel.nowMs` only with a postcondition stating the result as that of the translated `seal_at` at `ExtModel.nowMs` (`seal_with self payload options` relates to `seal_at self payload options ExtModel.nowMs`), with the same one-reading caveat and inherited exceptions in their docstrings. Amendment (spec owner, 2026-11-25, R09–R15 specification, finding sR-a-1): the rule covers `…RequestStateCodec.open_json` and `…RequestStateCodec.open_json_with` as well (they read the clock through `open_with`). Only the spec theorems of `open`, `open_with`, `open_json`, `open_json_with`, `seal` and `seal_with`, their `Theorems.*` restatements and the corollaries `open_with_spec_of_length_le`, `seal_with_spec_of_length_le` and `seal_spec_of_length_le` (and their restatements) may name these functions and `ExtModel.nowMs`, and only with these postconditions: `open`/`open_with`, `resultBytes result = openAt … ExtModel.nowMs.val`; `open_json`/`open_json_with`, the error of `openAt … ExtModel.nowMs.val` unchanged, otherwise the `ExtModel.serdeJsonFromSlice` outcome for the opened payload with `Err` mapped to `Deserialization`; `seal`/`seal_with`, `sealAt … ExtModel.nowMs.val = some (ExtModel.utf8 result)`, with `sealAt` the `Defs.CodecState` model of the private `seal_at` (human decision 2026-11-25; this replaces the wording "the result of the translated `seal_at` at `ExtModel.nowMs`" of the previous amendment; no statement equates `seal_with` with the translated `seal_at`). Docstrings state the one-reading caveat and the inherited exceptions; no statement relates two readings; `now_ms` stays unmentioned; the internal statements of `seal_at` (R10a) and of its round trip with `open_at` (R10b) use explicit times (`formal/README.md`, "Trusted base"). |
| **Codec state** | For a keyring codec: the key ids are pairwise distinct; every id in `rs1_fallbacks` and the `seal_mode` key id are keys of `keys`; every key is at least 32 bytes; every kid passes E04. The keyring constructors enforce these (`new_with_keyring`, `with_rs1_signing`, `with_rs1_fallback`). A single-key codec is unconstrained: `new_unchecked` and the deprecated `new` accept a key of any length (only `try_new` checks it). Stated as the `Defs` definition `CodecValid` (`Defs/CodecState.lean`), never as an axiom. Each opening statement takes only the clauses it needs: E09 and E11 that every rs1 fallback is a key id (so `keys.get(kid).expect(..)` cannot panic), E09a the same for its arguments, E10 none (its lookup returns an `Option`, and HMAC accepts keys of any length). The round trips may assume `CodecValid`, which implies these (spec-owner decisions 2026-11-23). | Correctness of the constructors (excluded, Section 2.3) |

**Rules for externals and axioms** (VERIFICATION.md §5):
- **No `axiom` in `trusted/`** (human decision 2026-11-23): use definitions, structures, `opaque` constants and hypotheses on the specs; `trusted/axioms.lock` stays empty. Adding an axiom again needs a human decision, a justification docstring, backing Rust tests, a lock line and a consistency model (below).
- **Never leave a bare `axiom f : … → Result T`.** Give an exact model or `ok` of an opaque value, as in the table; a bare `Result` axiom asserts nothing returns, so proofs through it get stuck.
- **Do not axiomatise a function whose Lean type merges distinct Rust types** (for example `size_of`); state the fact as a hypothesis on the spec instead.
- **Pin the dependency versions the models rely on** (in `PINNED_DEPS` of `scripts/aeneas-translate.sh`: `hmac 0.13.0`, `sha2 0.11.1`, `base64 0.23.1`, recorded at S03; `digest 0.11.3`, `zeroize 1.9.2`, `chrono 0.4.45`, `serde_json 1.0.154`, added at S08–S09 because the models cite them; `serde_core 1.0.229`, added with translation patch 03 on 2026-11-24, signed off). `Cargo.lock` is git-ignored in this repository and never copied into `.llbc/work/`, so the dependencies are resolved afresh on every run. The script runs one `cargo tree` over the whole dependency tree of `rmcp` in the translated configuration (same `--config`, `--target` and feature arguments, normal edges) and fails if any dependency does not come from crates.io (a path, git or other-registry source) or if a pinned crate resolves to a version other than the pinned one. Every later cargo call on that resolution (Charon's build, the translation's `cargo metadata` and the patched tests) uses `--locked`; each CI job resolves and checks its own graph (no committed lockfile).
- **Evidence.** RFC 4231 HMAC-SHA256 vectors and Base64 test vectors pass through `prim` in the `request_state_wire` Rust tests. `formal/trusted/evidence/README.md` names those tests per model; any test program that is not part of the crate's build lives in `formal/trusted/evidence/` (the Base64/UTF-8 differential check in `formal/trusted/evidence/differential/`). These tests catch a mismatched model; they are not a proof.
- **Consistency.** No consistency models are needed while `trusted/` declares no axiom: definitions and `opaque` constants (whose types are inhabited) cannot prove `False`. The `formal/proofs/Proofs/Consistency/` directory of the earlier design is dropped (decision 2026-11-23); it is required again for any axiom added later.
- **Review.** Each external model and each `opaque` constant is reviewed like a patch: by multiple independent agents, then by the human spec owner. Every model appears in the trusted-base section of `formal/docs/STATUS.md` with its justification, and its docstring repeats that justification (Rust source cited by file and line, stated exceptions). `#print axioms`, the spec files' `#guard_msgs` lists and `axioms.lock` show axioms only: the external models (definitions, structures and `opaque` constants of `trusted/`) do not appear in them, so a change to a model is caught only by review of `formal/trusted/` (a hash lock over the declarations of `RmcpExternal` is an option for the human at the S08/S09 sign-off).
- Where a model is generally useful (most std functions), prefer adding it to the Aeneas library upstream, so it leaves the trusted base here.
- `native_decide` and `bv_decide` may be used while developing a proof, never in an accepted one: both add an axiom that the spec files' `#print axioms` checks and the CI axiom audit flag. The only native-code axioms the audit accepts are the Aeneas `toStr` side conditions of string literals declared in the generated `Rmcp.Types`/`Rmcp.Funs`, and they must be locked in `formal/trusted/native-axioms.lock` once a `Defs`/`Proofs`/`Specs` constant depends on them (audit scope, 2026-11-23) ("What must be trusted" below; human decision 2026-11-22); it accepts no other native-code axiom, listed or not.

Dependencies are handled as hand-written external models, not by translating them with `-extern-crate`: targets reach `hmac`, `sha2` and `base64` only through the four `prim` functions, `chrono` only through `now_ms`, `zeroize` through its own models (`Zeroize`, `Zeroizing::{new, clone, deref}`) and `serde_json` only through the type `serde_json::Error`; the crates' own correctness is out of scope (Section 1).

### What must be trusted

A proved spec says something about the Rust code only if all of the following are right (VERIFICATION.md §7):

- **Tools:** Charon and Aeneas translate the Rust faithfully, and Lean's kernel checks proofs correctly.
- **Configuration:** the target and features fixed in `scripts/aeneas-translate.sh` (Section 1).
- **Translation patches** (`formal/trusted/patches/`): none were planned. If the refactor is not landed (Section 8, D2 fallback), it becomes a patch here and every target's linkage is `patch-01` (proved on upstream `7caec76` plus translation patch 01). Since 2026-11-23 (human decision) this is the case: `01-request-state-wire.patch` (the refactor and its tests) is in the trusted base; its VERIFICATION.md §4 review (multiple agents, then the human) is pending.
- **External models:** the definitions, structures and `opaque` constants of `formal/trusted/Rmcp/FunsExternal.lean` and `TypesExternal.lean` (the `RmcpExternal` roots) describe the Rust functions, with the stated exceptions in their docstrings (Section 4); since S08–S09 these roots declare no axiom (human decision 2026-11-23).
- **Axioms:** any declared in the `RmcpExternal` roots (none since S08–S09), plus Lean's `propext`, `Classical.choice` and `Quot.sound`, plus the native-code axioms listed in `formal/trusted/native-axioms.lock` — only Aeneas `toStr` string-literal side conditions (`decide (<literal>.toByteArray.size ≤ U32.max) = true`), each with a pinned statement and declared in the generated `Rmcp.Types`/`Rmcp.Funs`, handled as in the SPQR project (human decision 2026-11-22; a kernel proof exists, so an upstream Aeneas `toStr` fix would remove them); the CI axiom audit rejects any project constant (including all of `Rmcp.Types`/`Rmcp.Funs`) that depends on another axiom, or on a native-code axiom of another form or module; the locks are required only for the trusted and native-code axioms reachable from some constant of a `Defs`, `Proofs` or `Specs` module (audit scope, human decision 2026-11-23 for `axioms.lock`, applied by the lead to `native-axioms.lock`), so a trusted axiom (none since S08–S09) or a `toStr` native axiom that no `Defs`/`Proofs`/`Specs` constant depends on needs no lock entry, and its statement is checked only by review of `trusted/` and of the translation diff (Section 5, CI); the spec files' `#guard_msgs` lists show which of them each proof uses.
- **Statements:** the definitions in `formal/specs/Defs/` and the statements in `formal/specs/Specs/` say what we mean for the public API; since 2026-11-24 (human decision, Section 20 amendment) the statements about private, crate-internal and patch-only functions and the model laws are in `formal/proofs/Proofs/Internal/`, with the definitions only they use in `formal/proofs/Proofs/Defs/`, and are trusted in the same way.
- **Exclusions:** excluded items (Section 2.3) are not verified at all, and neither is anything outside the scope of Section 1.

The proofs and the generated translation do not need to be read: Lean checks the former and CI regenerates the latter. An auditor reads all of `formal/trusted/` and `formal/specs/` (start at `formal/specs/README.md`), and, for the guarantees about private functions and the model laws, `formal/proofs/Proofs/Internal/` and `formal/proofs/Proofs/Defs/`.

## 5. Layout

### Toolchain

`verification/host_origin/` (PR #4) already extracted other `rmcp` code at the base commit with the toolchain below, which the pilot built from source and used for all three runs. The plan keeps the same Aeneas commit, now taken from its GitHub release bundle as VERIFICATION.md §1–2 requires:

| Component | Version | Source |
|---|---|---|
| Aeneas | release tag `nightly-2026.08.20-5d08da4` (commit `5d08da45`) | `rev` in `formal/lakefile.toml`: the single source of truth |
| Charon | `0.1.235` (commit `f5208b1c`, the `charon-pin` of that Aeneas) | in the release bundle |
| Rust | `nightly-2026-06-01` | the bundle's `rust-toolchain` file |
| Lean | `4.31.0` (Mathlib `v4.31.0`, `fabf563a`) | the bundle's `backends/lean/lean-toolchain`, copied to `formal/lean-toolchain` |

S03 checks that the bundle's Charon, Rust and Lean versions are the ones in this table, and that the bundle's binaries reproduce the run-3 output. To upgrade Aeneas, change the `rev`, rerun both scripts and fix whatever breaks (deferred, Section 12).

`verification/host_origin/` stays where it is and keeps its own reproduction notes. Moving it into `formal/` is a separate decision, not part of this sprint.

### Files

Paths are relative to the repository root. **NEW** = written by hand; **GEN** = produced by the toolchain and never edited by hand; **UPDATE** = extend existing content. `Sxx` refers to the steps in Section 8.

```
CLAUDE.md                                       NEW    S02   points to the guides
.claude/agents/mcp-extraction.md                LOCAL    S02
.claude/agents/mcp-spec.md                      LOCAL    S02
.claude/agents/mcp-lean.md                      LOCAL    S02
.claude/agents/mcp-review.md                    LOCAL    S02
.gitignore                                      UPDATE S03   .aeneas/, .llbc/, formal/.lake/, *External_Template.lean
crates/rmcp/Cargo.toml                          UPDATE S03   [package.metadata.charon] (Section 9)
crates/rmcp/src/model/request_state_wire.rs     NEW    S04a  public foundation (Section 2.1)
crates/rmcp/src/model/request_state.rs          UPDATE S04a  refactored onto the wire module
                                                (tests added to its private `mod tests` — S16)
crates/rmcp/src/model.rs                        UPDATE S04a  `pub mod request_state_wire;`
scripts/aeneas-install.sh                       NEW    S03   pinned bundle into .aeneas/
scripts/apply-patches.sh                        NEW    S03   copy into .llbc/work/, apply patches
scripts/aeneas-translate.sh                     NEW    S03   configuration, version checks, charon + aeneas
scripts/lean-guard.sh                           NEW    S03   CI guard steps: sources, build-log,
                                                       axioms, aeneas-archive
scripts/lean_guard.py                           NEW    S03   lakefile, banned constructs, build-log
                                                       allowlist, archive checks (python3 -I)
scripts/lean-axiom-audit.lean                   NEW    S03   axiom audit and kernel replay of every
                                                       project constant
scripts/llbc-dir-guard.sh                       NEW    S03   RMCP_LLBC_DIR guard (sourced by
                                                       apply-patches.sh, aeneas-translate.sh)
.github/workflows/lean-build.yml                NEW    S03   jobs build (sources, lake build) and
                                                       check (lean-guard.sh on the artifact)
.github/workflows/aeneas-translation.yml        NEW    S04a  translation is not stale
.github/workflows/patched-tests.yml             NEW    S04a  crate tests on the patched copy
formal/
  README.md                                     NEW    S03, final S19   layout, configuration, trusted base
  lakefile.toml                                 NEW    S03   pins Aeneas; five libraries (below)
  lean-toolchain                                GEN    S03   copied by aeneas-install.sh
  lake-manifest.json                            GEN    S03
  docs/
    STATUS.md                                   NEW    S01, final S19   owners, budget, pinned commit,
                                                       per-function status, trusted base, bugs found,
                                                       open items, results (Section 11)
    board.yaml                                  NEW    S01   task state (authoritative)
    functions/W01.yaml … W15.yaml, E01.yaml … E11.yaml, E09a.yaml   NEW S01   per-function status
                                                       carry `.ref` suffixes)
    evidence/Sxx.md                             NEW    per step
    blockers/Sxx.md                             NEW    on failure only
  trusted/                                      READ ALL OF IT
    aeneas-bundle.sha256                        NEW    S03   sha256 of every Aeneas release asset used
    axioms.lock                                 NEW    S03   name and statement hash of every trusted axiom
                                                       used by a Defs/Proofs/Specs constant (and any
                                                       reviewed unused one locked early)
    native-axioms.lock                          NEW    S04a  name, module and statement hash of every accepted
                                                       native-code axiom (Aeneas `toStr` side conditions)
                                                       used by a Defs/Proofs/Specs constant
    patches/                                    empty unless the D2 fallback is used
                                                       (used since 2026-11-23:
                                                       01-request-state-wire.patch)
    Rmcp/TypesExternal.lean                     NEW    S04a from the template, edited S08–S09
    Rmcp/FunsExternal.lean                      NEW    S04a from the template, edited S08–S09
    evidence/README.md                          NEW    S08   Rust source and tests backing each external model
    evidence/differential/                      NEW    S08   Base64/UTF-8 models vs base64 0.23.1 and std (not built)
  specs/                                        READ ALL OF IT
    Defs.lean                                   NEW    S05
    Defs/Wire.lean                              NEW    S05   splitOn, be64, transcripts, frame
    Defs/RequestState.lean                      NEW    S05   codec errors and outputs
    Defs/CodecState.lean                        NEW    S12   codec-state invariant
    Specs.lean                                  NEW    S05
    Specs/Model/RequestStateWire.lean           NEW    S06 onward   W01–W15 + frame_roundtrip
    Specs/Model/RequestState.lean               NEW    S07 onward   E01–E11, E09a + round trips
    Drafts/                                     NEW    S05   reviewed statements awaiting proofs;
                                                       in no library, so never built
  translation/                                  GEN — never edited
    Rmcp/Types.lean, Rmcp/Funs.lean             GEN    S04a  (no `Rmcp.lean`: -split-files -subdir Rmcp)
    translation.json                            GEN    S04a
  proofs/                                       checked by Lean
    Proofs.lean                                 NEW    S05
    Proofs/Model/RequestStateWire/
      B64Len.lean          W01   S06     ParseRs1.lean        W08   S10
      KeyLengthOk.lean     W02   S06     ParseRs2.lean        W09   S10
      CheckKidLen.lean     W03   S06     TranscriptV1.lean    W10   S10
      BytesEq.lean         W04   S06     TranscriptV2.lean    W11   S10
      NextDot.lean         W05   S06     DecodeExpiry.lean    W12   S06
      ComponentCount.lean  W06   S06     IsExpired.lean       W13   S06
      VersionOf.lean       W07   S10     OpenFrame.lean       W14   S06
                                         Frame.lean           W15 + frame_roundtrip   S06
    Proofs/Model/RequestState/
      OpenAuthenticatedBody.lean  E01  S07     Rs1FallbacksVerify.lean  E09a S13
      B64Len.lean                 E02  S07     OpenRs1At.lean           E09  S13
      ValidateKeyLength.lean      E03  S07     OpenRs2At.lean           E10  S13
      ValidateConfigKid.lean      E04  S07     OpenAt.lean              E11  S14
      SealRs1.lean                E07  S11     Roundtrip.lean           round trips  S15
      SealRs2.lean                E08  S11
    Proofs/External/
      Base64.lean, String.lean, Prim.lean, Std.lean   NEW  S08–S09   laws and specs of the external models
docs/VERIFICATION.md                            NEW    S02   process guide
docs/MCP_SDK_Verification_Master_Plan_EN.md     this plan
docs/WORKFLOW_AND_PR_GUIDE.md                   UPDATE S02   align with formal/ layout
docs/STYLE_GUIDE.md                             UPDATE S02   align with formal/ layout
docs/REVIEWER_GUIDE.md                          UPDATE S02   align with formal/ layout
docs/AI_PR_REVIEW_QUESTIONS.md                  UPDATE S02   align with formal/ layout
```

**Committed and ignored** (VERIFICATION.md, "What is committed"). The generated translation, the hand-written externals, `lake-manifest.json` and `lean-toolchain` are committed; the stale-translation CI needs them in git. `.aeneas/`, `.llbc/`, `formal/.lake/` and `formal/translation/Rmcp/*External_Template.lean` are git-ignored. Generated files are never edited by hand: change the Rust, a patch or the Charon settings and re-run the translation. CI rejects hand edits.

### Lean libraries

`formal/lakefile.toml` requires the Aeneas Lean library at `rev = "nightly-2026.08.20-5d08da4"` and declares one `[[lean_lib]]` per part, each with its own `srcDir` and explicit `roots` (no `globs`; the guard allows only `name`, `srcDir`, `roots` and `leanOptions`), so every module belongs to exactly one library and module names do not mention the folders:

| Library | `srcDir` | Modules | May import |
|---|---|---|---|
| `Rmcp` | `translation` | `Rmcp.Types`, `Rmcp.Funs` (the roots; Aeneas generates no `Rmcp.lean`) | Aeneas, `RmcpExternal` |
| `RmcpExternal` | `trusted` | `Rmcp.TypesExternal`, `Rmcp.FunsExternal` | Aeneas, `Rmcp.Types` (the generated `FunsExternal` template imports it) |
| `Defs` | `specs` | `Defs.*` | Aeneas, Mathlib, `Rmcp`, `RmcpExternal` |
| `Proofs` | `proofs` | `Proofs.*` | `Rmcp`, `RmcpExternal`, `Defs` |
| `Specs` | `specs` | `Specs.*` | `Defs`, `Proofs` |

- Spec statements use only `Defs` definitions, so their meaning never depends on proof-private definitions. `Proofs` never imports `Specs`; nothing imports `Specs`.
- The library roots (`Defs.lean`, `Specs.lean`, `Proofs.lean`) are maintained by hand. Statements awaiting proofs stay in `formal/specs/Drafts/`, outside every library; a proof with `sorry` is never merged, because every library sets `warningAsError` and CI fails on any warning in this project's files (CI, below).
- E proofs use W theorems as lemmas and never unfold a W definition. This is what makes the foundation reusable.
- Lean commands (`lake build`, `lake exe cache get`) run in `formal/`; `.aeneas/` and `.llbc/` stay at the repository root.

### Spec files

(Since 2026-11-24 the public/internal split of Section 20, amendment, applies: `formal/specs/` holds the public API only, the other statements are in `formal/proofs/Proofs/Internal/`, and the signed-off definitions in `formal/proofs/Proofs/Defs/` count as `Defs` for the rule that statements use only `Defs` definitions.) There is one spec file per Rust source file (VERIFICATION.md §7): `Specs/Model/RequestStateWire.lean` and `Specs/Model/RequestState.lean`. Each lists its file's targets in source order. Each statement is restated as a `theorem` in the `Theorems` namespace (as in the curve25519-dalek fork's `ForHumans/Theorems`; human decision 2026-11-23), proved by the spec theorem it restates, so Lean checks the restated type against the proved one. It is followed by the axioms that proof depends on, checked by `#print axioms`:

```lean
open rmcp.model.request_state_wire  -- for `Rs1Parts`; the theorem is still named in full

/-- `parse_rs1`: `Some {body, tag}` iff the token splits on `.` into `["rs1", body, tag]`. -/
theorem Theorems.request_state_wire.parse_rs1 (s : Slice U8) :
    rmcp.model.request_state_wire.parse_rs1 s ⦃ (r : Option Rs1Parts) =>
      r = (Defs.parseRs1 s.val) ⦄ :=
  rmcp.model.request_state_wire.parse_rs1_spec s

/-- info: 'Theorems.request_state_wire.parse_rs1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Theorems.request_state_wire.parse_rs1
```

The guard accepts only this form: a bare `#guard_msgs in` (no options) followed by exactly one `#print axioms` line, so the docstring must match the complete message, which prints the full name of the theorem. The module docstring states the translated configuration, names the `Defs` the statements use, and lists what was not translated (Section 2.3). If a proof starts using a new axiom, the `#guard_msgs` check fails the build, so every change to the trusted base shows up as a diff of a spec file.

**Theorem names.** Each identifier is the full generated function name with `_spec`, per the style guide. Aeneas generates every definition inside `namespace rmcp` (run-3 `Funs.lean`: `rmcp.model.request_state_wire.parse_rs1`, `rmcp.model.request_state.RequestStateCodec.open_rs1_at`), so the spec theorems are, for example, `rmcp.model.request_state_wire.parse_rs1_spec` and `rmcp.model.request_state.RequestStateCodec.open_rs1_at_spec`; proof files may open the namespace. In the spec files the restated theorem is `Theorems.<module>.<function>` (for example `Theorems.request_state_wire.parse_rs1`), and the laws of the external models are `Theorems.External.<original name>`; `#print axioms` and the `#guard_msgs` message use that full name. The composition theorems are `rs1_roundtrip`, `rs2_roundtrip`, `open_at_roundtrip_rs1`, `open_at_roundtrip_rs2` (end of `RequestState.lean`) and `frame_roundtrip` (`RequestStateWire.lean`). Each spec covers both success and error results, not only the success path.

### CI

Three workflows (VERIFICATION.md §9) keep the repository honest:

- **Translation is not stale** (`aeneas-translation.yml`). Runs when `crates/rmcp/src/`, `crates/rmcp/Cargo.toml`, `crates/rmcp/build.rs`, the root `Cargo.toml` or any other workspace `Cargo.toml` (dependency resolution is workspace-wide), `formal/trusted/patches/`, the scripts, `formal/lakefile.toml`, `formal/lean-toolchain`, `formal/trusted/aeneas-bundle.sha256`, `formal/trusted/Rmcp/` or `formal/translation/` change. Runs `scripts/aeneas-install.sh` (caching `.aeneas/` and the nightly by the pinned tag), then `scripts/aeneas-translate.sh`, and fails if `git status --porcelain` shows any difference. This catches a Rust change, a patch, a Charon setting or an Aeneas bump committed without regenerating, and any hand edit to generated files. Because `Cargo.lock` is not committed, the translate script's dependency check (Section 4) is what keeps dependency resolution from drifting silently. The script also checks its own inputs (exact lists: `formal/README.md`, "Translated configuration" and "Commands"): `RUSTUP_HOME` is allowed (container images set it), but after selecting the bundle's channel the `rustc` that cargo runs must report, in `rustc -vV`, commit-hash `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, commit-date `2026-05-31` and release `1.98.0-nightly` (nightly-2026-06-01), and `charon toolchain-version` must print the bundle's channel; every other `RUSTUP_*` except `RUSTUP_TOOLCHAIN` is refused. The work directory `RMCP_LLBC_DIR` gets `rsync --delete` and `rm -rf`, so `scripts/llbc-dir-guard.sh` (used by `apply-patches.sh` and `aeneas-translate.sh`) refuses one that is `/`, `$HOME`, the repository or contains one of them, contains or lies inside the source (except `<source>/.llbc`), has a symlinked `work/`, `out/`, `cargo-home/` or `target/`, or exists, is not empty and has no marker file `.rmcp-llbc-dir` (written into every work directory the guard accepts; the repository's own `.llbc` is accepted without it).
- **Lean project builds** (`lean-build.yml`). Runs when anything under `formal/`, `scripts/lean-guard.sh`, `scripts/lean_guard.py`, `scripts/lean-axiom-audit.lean`, `scripts/aeneas-install.sh` or the workflow itself changes. The build gate (human decision, S03): every `[[lean_lib]]` sets `leanOptions = { warningAsError = true }`, so a plain `lake build` fails on any warning in this project's modules, including `sorry`, and runs every `#guard_msgs` axiom check. `lake build --wfail` is not used: the pinned Aeneas Lean library has four `sorry` warnings (`Aeneas/Std/Slice.lean:363,586`, `Aeneas/Std/StringIter.lean:12,15`) that Lake replays on every build, and `--wfail` fails on them (the S03 evidence (git history at 223ff12)). The gate can return to `--wfail` once an Aeneas bump removes them. The workflow has two jobs, because `lake build` elaborates the project, and elaboration runs code that could rewrite files of the runner (a `#eval` rewriting `scripts/lean-guard.sh`, say) before a later step of the same job:
  - Job `build` (`working-directory: formal`): checkout without persisted credentials; a pinned elan binary checked by sha256; `scripts/lean-guard.sh sources` before any Lean code of the project runs; restore of the `formal/.lake/packages` cache (keyed on `formal/lean-toolchain` and `formal/lake-manifest.json`; only this job uses it, and `formal/.lake/build` is never cached); `lake exe cache get`; `lake build` with `pipefail`, output tee'd to `.lake/build.log`; then `.lake/build` and the log packed as one tar file and uploaded as the artifact.
  - Job `check` (`needs: build`): a fresh runner and a fresh checkout, so the scripts come from git and not from job `build`; the pinned elan installed afresh; `sources` again; Mathlib cache and the Aeneas release archive fetched afresh with no cache (`lake exe cache get`, `lake build Aeneas`, which builds nothing of this project), then `aeneas-archive`; then the artifact is downloaded and unpacked with `scripts/lean-guard.sh unpack-build` (only `build/` and `build.log`, no absolute or `..` paths, no links or devices, no existing build); then `build-log` and `axioms`. No Lake command runs after the unpack, and the audit runs no code from the `.olean` files, so no project code runs in this job.

  Because a file can switch `warningAsError` off, hide messages, add declarations without a kernel check or run code during the build, the guard (`scripts/lean-guard.sh`; checks in `scripts/lean_guard.py`, run with `python3 -I`, Python 3.11 or later, and `scripts/lean-axiom-audit.lean`) has these subcommands:
  - `sources`: (1) `formal/lakefile.toml`, parsed as TOML, has exactly the five libraries of "Lean libraries" below with their fixed `srcDir` and roots, each with exactly the keys `name`, `srcDir`, `roots`, `leanOptions` and `leanOptions` exactly `{ warningAsError = true }`; the package has only `name`, `defaultTargets` (including `Defs`, `Proofs`, `Specs`), one `[[require]]` (aeneas) and the libraries; no `formal/lakefile.lean` exists. (2) `formal/lake-manifest.json` lists exactly the ten recorded packages at their recorded commits (`MANIFEST_PACKAGES` in `scripts/lean_guard.py`): Aeneas at `5d08da45a405913bbee6fd544e01debf8154ac9d` with `url`, `inputRev` and `subDir` equal to the lakefile's `git`, `rev` and `subDir`, Mathlib at `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (`v4.31.0`), and the eight packages Mathlib brings in; a PR that bumps the Aeneas rev updates this list. (3) Every hand-written `.lean` file under `formal/` (everything except `.lake/`, `specs/Drafts/` and `translation/`) fails on the whole words `warningAsError`, `sorry`, `sorryAx`, `admit`, `native_decide`, `bv_decide`, `skipKernelTC`, `proofAsSorry`, `implemented_by`, `extern`, `unsafe`, `ofReduceBool`, `ofReduceNat` and `trustCompiler`, on the `native` option of `decide` (`+native`, `-native`, `native :=`), on `set_option linter.<name> false` (in `trusted/` too), and, outside `trusted/`, on `axiom`. It also fails, in `proofs/`, `specs/` and `trusted/` alike, on anything that runs or registers a metaprogram during the build: `#eval`, `#exit`, `run_cmd`, `run_tac`, `run_elab`, `run_meta`, `elab`, `elab_rules`, `initialize`, `builtin_initialize`, `macro`, `macro_rules`, `syntax`, `simproc`, `dsimproc`, `simproc_decl`, `builtin_simproc`, `register_option`, `register_simp_attr`, `declare_syntax_cat`, `addDecl`, `addAndCompile`, `modifyEnv`, `setEnv`, `withOptions`, the metaprogramming types (`IO`, `EIO`, `BaseIO`, `CoreM`, `MetaM`, `TermElabM`, `TacticM`, `CommandElabM`, `MacroM`, `SimpM`, `DelabM`, `CommandElab`, `TermElab`), the namespace `Lean.Elab`, any `debug.` option, and the attributes that register a metaprogram (`command_elab`, `term_elab`, `tactic`, `init`, `builtin_*`, `delab`, `app_delab`, `simproc`, `env_linter`, code actions, `widget_module`). `macro` and `syntax` are banned because a macro can produce any command without writing its keyword; `notation`, `infix`, local instances and attributes such as `simp` are allowed. A proof that needs a custom tactic writes it out inline; a reviewed tactic module with its own rules would be a separate human decision (lead decision 2026-11-22: the ban stays everywhere). The list is defence in depth, not complete (an Aesop rule that runs a tactic definition is not covered), so reviewers check for metaprogramming. The check is textual, so comments and docstrings count. `#guard_msgs` is allowed only in `specs/Specs.lean` and `specs/Specs/`, and there only as a bare `#guard_msgs in` followed, on the same or the next line, by exactly one `#print axioms <name>` that ends the line (no options such as `(drop all)` or `(whitespace := lax)`); written in backticks on both sides (`` `#guard_msgs` ``) it is prose and skipped. This backtick exemption applies only to `#guard_msgs`, not to the banned words. Generated files in `translation/` get the same word, `native` and metaprogramming rules (**Phase 2:** one exception, human decision 2026-11-23, S21: a metaprogramming word in a generated file is excused only at a line number pinned, with that word and the line's exact text, in the trusted file `formal/trusted/translation-pins.txt`, and only while the file's bytes have the sha256 pinned there; today one entry, the T06 comparison with the MCP method name "initialize". A hand edit alone changes the hash and restores the strict rule; an edit together with an updated pin is caught only by the byte-for-byte regeneration of `aeneas-translation.yml` and by review, which must read each pinned line in context. No lexing is involved (review rounds bypassed the earlier lexing-based exemption five times)); `#guard_msgs` is banned there, Aeneas's `set_option linter.* false` is allowed, and `axiom` is banned except in the unbuilt `*_Template.lean` files, which are exempt. Symlinks under `formal/` fail.
  - `build-log`: an exact allowlist. The log must contain a `Build completed successfully` line, and every line containing `warning:` or `error:` must be exactly one of the four lines `` warning: Aeneas/Std/Slice.lean:363:4: declaration uses `sorry` ``, `…/Slice.lean:586:8: …`, `…/StringIter.lean:12:4: …` and `…/StringIter.lean:15:4: …`.
  - `axioms` (only after a successful build): fails if `formal/.lake/build/lib/lean` holds anything but modules named `Rmcp`, `Defs`, `Proofs`, `Specs` or below them, or a symlink. It then runs `lean-axiom-audit.lean` with the toolchain's own `lean` (`lean --run`, not `lake env`, which would put `formal/.lake/build/bin` first on `PATH` and `formal/.lake/build/lib` on the shared-library path), with an explicit `LEAN_PATH` (toolchain library, then the manifest's packages, then the project build, so no project `.olean` can shadow `Init`, `Lean`, `Lake` or a package module) and no dynamic-loader variables. The audit imports the roots of the default-target libraries with `loadExts := false`, so no code of an imported module runs, and fails if (a) a project `.olean` is stale: the source hash in its Lake `.trace` file differs from the hash of the current source; (b) the constants declared in project modules that the roots reach reach (one order-independent walk over all of them, through types, values and whole inductive blocks) an axiom other than `propext`, `Classical.choice`, `Quot.sound`, the axioms declared in the `RmcpExternal` roots (`Rmcp.TypesExternal`, `Rmcp.FunsExternal`) and the native-code axioms that are the Aeneas `toStr` side condition of a string literal and are declared in `Rmcp.Types` or `Rmcp.Funs` (nothing else native), which catches `sorryAx` (also when inherited from the Aeneas library or hidden from the build log) and the `<decl>._native.*` axioms (`native_decide`, `decide +native`); or (c) the kernel rejects a project constant when every project constant is replayed (`Lean.Environment.replay`, the check `leanchecker` runs) onto the non-project modules they import, which catches declarations added without a kernel check (for example through `debug.skipKernelTC` set from a metaprogram) and altered `.olean` files; or (d) an `RmcpExternal` root declares a constant in the namespace `rmcp` or adds an alias (`export`), which would take precedence over the names the generated `namespace rmcp` code means (`sources` checks the same textually in `trusted/`). `leanchecker` is not run separately (it uses the same replay). Then (e) the locks, with the audit scope of the human decision of 2026-11-23 (for `axioms.lock`; the lead applied the same rule to `native-axioms.lock`): every trusted axiom (declared in the `RmcpExternal` roots) and every native-code axiom reachable from some constant declared in a `Defs`, `Proofs` or `Specs` module (every constant of such a module counts, including private helpers, instances and auxiliary declarations), transitively through any constant including the generated `Rmcp.Types`/`Rmcp.Funs` definitions (one walk with a single visited set over types, values and whole inductive blocks, independent of the order of the constants; a superset of what `#print axioms` reports), must be in `formal/trusted/axioms.lock` (`lean_guard.py axiom-lock`) or `formal/trusted/native-axioms.lock` (`lean_guard.py native-lock`, also with its module) with the sha256 of its canonical statement; axioms that no such constant depends on are listed for information and need no entry (so importing `Rmcp.Funs` into a proof does not require locking every placeholder external); an entry for a declared but unused axiom is reported as "unused (allowed)", so S08–S09 can lock reviewed models early; an entry for an axiom no longer declared, or with another statement hash, fails. The statement of a declared axiom that is neither locked nor used (none since S08–S09, which replaced the 41 placeholder externals by definitions) is not checked and can change or vanish in any PR, ordinary or forged, without CI failing; review of `trusted/` is the barrier for such axioms. (a)–(d) and the `toStr`-form and module restrictions on native-code axioms cover every project constant regardless of this scope. Only the import closure of the default-target roots is audited, so (d) and (e) cover `Rmcp`/`RmcpExternal` once a `Defs`/`Proofs`/`Specs` module imports `Rmcp.Funs` (S06) or they become default targets (a lakefile change by the lead; unused placeholders no longer block it, evidence S03 D1).
  - `aeneas-archive`: every Lake-fetched Aeneas Lean-library archive matches `formal/trusted/aeneas-bundle.sha256`, and the installed Aeneas build and the archive hold the same regular files with the same bytes (every file except `*.hash` and `*.trace`); a build without an archive fails unless `LEAN_GUARD_AENEAS_FROM_SOURCE=1` marks a build from the pinned sources.
  - `unpack-build TAR`: job `check` only, as above.

  Limits: the `sources` rules are textual, not semantic; only the axioms declared in the `RmcpExternal` roots (`Rmcp.TypesExternal`, `Rmcp.FunsExternal`) are trusted by the audit, so those files still have to be read and reviewed; a module that no root imports is neither built nor audited; unlike `#print axioms`, the audit does not lose axioms on inductive/constructor cycles: it follows types, values and whole inductive blocks with one visited set (an over-approximation). Residual risks of the two-job design (`formal/README.md`, "What CI checks"): (1) the artifact is attacker-controlled data if the build ran malicious code; job `check` replays it in the kernel and audits its axioms, but cannot tell whether it was compiled from these sources, since a build that runs code could upload output of a different (or empty) project, and the only barrier is that the build runs no project code: the metaprogramming bans of `sources`, checked in job `build` before the build, and review (a ban that misses a way to run code is a hole in this barrier, not only in the textual check); (2) `.olean` files are memory images that Lean maps without validating them, so a crafted file could crash the audit or worse (job `check` has read-only repository permissions and no secrets, so the worst outcome is a wrong check result); (3) the Mathlib oleans of job `check` come from Mathlib's cache server and are not checked against a committed digest (open scope question for the human). On the translation side, a fake `rustc` that prints exactly the pinned `rustc -vV` lines is not caught by asking it (`charon-driver` would then not find its `librustc_driver`).
- **Patched copy passes the crate's tests** (`patched-tests.yml`). Same paths as the translation check (including `crates/rmcp/build.rs` and the root `Cargo.toml`), plus `crates/rmcp-macros/**` (**Phase 2**, S21: the test build compiles it). Installs the pinned nightly, runs `scripts/aeneas-translate.sh --check-deps` (`apply-patches.sh` plus the translation's own dependency checks: crates.io sources and `PINNED_DEPS`), and runs `cargo test --locked --no-default-features --features request-state --lib` (**Phase 2**, from S21: `--features "$FEATURES,macros"`, with `FEATURES` read from `scripts/aeneas-translate.sh`; Section 15) in `.llbc/work/crates/rmcp` on the `Cargo.lock` just checked. With no patches this is the plain test suite; it becomes evidence for the patches if the D2 fallback is used, which it is since 2026-11-23 (patch 01 carries the refactor's tests, so the run is evidence for patch 01).
- **Phase 2:** `aeneas-translation.yml` also runs the linkage check of Section 19, and `patched-tests.yml` uses the widened feature list of Section 15.

## 6. Status model

One vocabulary is used everywhere.

**Task state** (in `formal/docs/board.yaml`): `NOT_STARTED` → `IN_PROGRESS` → `ACCEPTED`, or `BLOCKED` / `DEFERRED`. Only `ACCEPTED` is complete. An accepted blocker report closes the *task of reporting*, never the function's proof.

**Function status** (in `formal/docs/functions/<ID>.yaml`), four independent fields:

| Field | Values |
|---|---|
| `translation` | `NOT_TRIED`, `LLBC_OK` (Charon), `LEAN_OK` (Aeneas output compiles), `BLOCKED` |
| `spec` | `DRAFT`, `REVIEWED` |
| `linkage` | `ORIGINAL` (pinned source, no patch touches it), `patch-NN` (its translation depends on translation patch NN in `formal/trusted/patches/`, e.g. `patch-01`). Since the D2 fallback (2026-11-23) all 25 Phase 1 targets (W/E) are `patch-01` (patch 01); the Phase 2 targets (M/T/A) are `ORIGINAL` only while the Section 19 check passes; a target whose proof is about a patched copy is reported as proved with translation patch 01, not verified (D10) |
| `proof` | `OPEN`, `CHECKED` |

**Phase 2:** for the M/T/A targets, `ORIGINAL` is checked mechanically by `scripts/check-original-linkage.sh` (Section 19), because patch 01 touches `model.rs`.

Specifications follow VERIFICATION.md §6: drafted (by a person or the `mcp-spec` agent), **reviewed independently by multiple agents**, then signed off by a named human spec owner, all before any proof work starts. Only the spec owner sets `spec: REVIEWED` or moves a task to `ACCEPTED`. The drafter is recorded in `spec_drafted_by`, and an AI drafter never sets `REVIEWED`. Any change to an accepted statement returns `spec` to `DRAFT`.

**Verified** requires all of the following:
- `proof: CHECKED` (the proof is in `Proofs`, and the statement is restated in `Specs` as a `theorem Theorems.…` with its `#guard_msgs` check);
- `spec: REVIEWED`;
- `linkage: ORIGINAL`;
- the external models it uses are signed off (S08/S09), and any axiom its `#guard_msgs` list shows besides `propext`, `Classical.choice` and `Quot.sound` is in the trusted-base section of `STATUS.md`. `#print axioms`, the spec files' `#guard_msgs` lists and `axioms.lock` show axioms only: the external models (definitions, structures and `opaque` constants of `trusted/`) do not appear in them, so a change to a model is caught only by review of `formal/trusted/`; a hash lock over the declarations of `RmcpExternal` is an option for the human at the S08/S09 sign-off (not adopted).

Anything else is reported as what it is (for example "checked, patched source" or "open"). The deadline never changes a status.

Function record template:

```yaml
id: W08
rust_symbol: rmcp::model::request_state_wire::parse_rs1
source_file: crates/rmcp/src/model/request_state_wire.rs
source_line: null               # filled in at S01
generated_symbol: null          # filled in at S04a
translation: NOT_TRIED
spec: DRAFT
linkage: ORIGINAL
proof: OPEN
proof_file: formal/proofs/Proofs/Model/RequestStateWire/ParseRs1.lean
spec_file: formal/specs/Specs/Model/RequestStateWire.lean
theorem: null
used_by: [E09]                  # targets whose proofs consume this theorem
axioms: []                      # as printed by `#print axioms` in the spec file
evidence: []                    # paths under formal/docs/evidence/
spec_drafted_by: null           # person, or "AI: <tool>, <model>"
spec_reviews: []                # independent agent reviews (tool, model, verdict)
spec_owner: null                # human who signed off the spec
prover: null                    # person, or "AI: <tool>, <model>"; not the AI spec drafter
reviewer: null
```

## 7. Acceptance per step and per function

(The per-step evidence files of S01–S19 were removed from the working tree on 2026-11-23 by human decision; they remain in git history at commit `223ff12`, and `formal/docs/STATUS.md` keeps the results. A later step records the same content in its commit message and in `STATUS.md`.)

Every step writes `formal/docs/evidence/Sxx.md` with:
- the exact commands and their exit status;
- the pinned Aeneas tag and the commit translated;
- axioms added or changed;
- which artifacts were AI-drafted or AI-reviewed (tool and model);
- the reviewer decision.

On failure, also write `formal/docs/blockers/Sxx.md` with a minimal reproducer and leave the task `BLOCKED`.

Boundary cases each proof must cover and the Rust tests must exercise:

| ID | Cases |
|---|---|
| W01/E02 | `n mod 3 ∈ {0,1,2}`; `n = 0`; largest `n` with no overflow; agreement with `div_ceil(3) * 4` |
| W02/E03 | 31, 32, 33; E03's `actual` field value |
| W03/E04 | 0, 1, 255, 256 bytes; multibyte UTF-8 crossing 255 |
| W04 | equal; different lengths; same length, last byte differs; both empty |
| W05/W06 | empty input; no `.`; leading, trailing and consecutive dots; `start > len` |
| W07/E11 | `rs1`, `rs2`, `rs3`, `rs1x`, empty string, no `.` |
| W08/W09 | 2, 3, 4, 5 components; wrong version; empty components |
| W10/W11 | empty ad and body; transcript order and length prefix; kid, ad, body each varied |
| W12–W15/E01 | 0–7 bytes; exactly 8; expiry 0; `now` before, equal to, after expiry; negative expiry; `frame`/`open_frame` round trip |
| E07/E08 | empty and nonempty body; delimiters; tag encoding; multibyte kid |
| E09/E09a | ring with no fallbacks; bad Base64 body/tag; MAC fails; match on the last fallback; expiry |
| E10 | encoded kid 340/341; decoded kid 0/255 (256 bytes is unreachable through `open`: 340 encoded characters decode to at most 255 bytes and the encoded-length check rejects first, so 256 is tested on `check_kid_len` directly); invalid UTF-8; single-key codec; unknown kid; bad body/tag; MAC fails; expiry |

W tests go in a new `mod tests` of `request_state_wire.rs`. E tests go in the existing `mod tests` of `request_state.rs` (36 tests at the base commit; 39 after S04a, which adds 3).

The refactor PR must also commit a regression test that pins one rs1 and one rs2 token, plus the `open` results of the run-3 token harness (Section 9). It must add `Expired` and `InvalidKeyId` cases, which that harness does not cover.

## 8. Two-week sprint

Days are relative working days. Dependencies govern acceptance; independent preparation can start earlier.

### Pilot results (22 November 2026)

All runs ran on macOS aarch64, with every output in scratch directories under `/tmp`: run 1 compiled the repository's own `crates/rmcp`, except its `e04`/`e04c` attempts, which used the scratch source `/tmp/rs-pilot/src`; runs 2 and 3 used scratch copies (`/tmp/rs-pilot/src`, `/tmp/rs-wire/src`). Charon and Aeneas were built from source at the pinned commits. The generated Lean was compiled with Lean 4.31.0 against an existing build of the Aeneas Lean library at `6e167c9b`. That library's sources are identical to the pinned `5d08da45`'s; under `backends/lean/`, `5d08da45` only adds `ExtractLeanKeywords.lean` and one `lean_exe` in `lakefile.lean`. No Charon or Aeneas exit status was recorded for any run; details and the full list of corrections are in the pilot record (removed from git history on 2026-11-23) ("Disagreements between the plan and the artifacts"). The repository will use the release bundle `nightly-2026.08.20-5d08da4` of the same commit instead (S03).

| Target | Run 1: unchanged source | Run 2: private adapter shims | Run 3: public wire API |
|---|---|---|---|
| W01–W15 | — | — | All translate and compile; no `sorry` |
| E01 | Lean compile fails (B6); only the generated `core.num.I64.from_be_bytes` call survives, no compile log | Compiles | Compiles |
| E02, E03 | Body generated | Compiles | Compiles |
| E04 | Body is `sorry` (B4) | Compiles | Compiles |
| E05, E06 | Not translatable (B1) | Compile | Deleted (Section 2.3) |
| E07, E08 | Not translatable (B1) | Compile | Compile |
| E09 | Not translatable (B1, B2, B5) | Compiles via helper | Compiles via E09a |
| E10 | Not translatable (B1, B2) | Compiles | Compiles |
| E11 | `sorry` placeholder (B2) | Compiles | Compiles |

**Run 3 in detail** (scratch: `/tmp/rs-wire`; copy into the pilot record (removed from git history on 2026-11-23) at S04):
- **Refactor:** `request_state_wire.rs` adds 251 non-blank lines (277 in total). In `request_state.rs`, 82 non-blank lines are added and 130 removed (85 and 135 in total), including formatting; `model.rs` gains 2 lines. Patch: `/tmp/rs-wire/wire-refactor.patch`.
- **Rust checks:** the pilot claimed that `cargo clippy --lib -- -D warnings` was clean in both the normal and the test profile, that nightly `rustfmt` reported no diff, and that 39 request-state tests passed (36 in `request_state.rs`'s `mod tests`, plus 3 in `mrtr.rs` selected by the `request_state` name filter; inferred). None of this is recorded: no log survives, only partial Cargo fingerprints (the pilot record (removed from git history on 2026-11-23), disagreement 5). S04a re-ran the checks on the refactor: 265 library tests pass, including 39 in `request_state.rs` and 28 in `request_state_wire.rs`, and `clippy` (both profiles) and `rustfmt` are clean (the S04a evidence (git history at 223ff12)).
- **Token identity:** the pilot harness checks three codecs × three payload/ad pairs, then `open` on each token and five variants (three derived from the token, the empty string and a fixed string), with each of the three codecs. All 9 tokens and all 162 `open` results (9 tokens × 6 candidates × 3 codecs) are **byte-identical** to the unmodified base commit. The results cover `Ok`, `IntegrityCheckFailed`, `InvalidEncoding`, `MalformedFormat` and `UnknownKeyId`.
- **First translation (only B9 excluded):** the Charon log shows no warnings; Aeneas generated partial files because seven bodies failed: `Debug`/`Display` of `RequestStateError`, `Debug` of `RequestStateCodec`, `new_with_keyring`, `with_rs1_signing`, `with_rs1_fallback` and `seal_at`. In addition, one generated `Eq for str` instance did not compile in Lean (B12); the compiled output carries one hand edit for it (`out-full` `Funs.lean` line 113).
- **Final translation (Section 2.3 exclusions, settings in Section 9):** the Charon and Aeneas logs show no errors or warnings. `Types`, `TypesExternal`, `FunsExternal` and `Funs` compile with **0 errors and no `sorry` anywhere**, without any hand edit. All 15 W, 9 E and the E09a definitions are present; so are the non-target `open`, `open_with`, `new` and `try_new`.
- **Target closure externals:** the four `prim` functions plus the standard-library operations of Section 4. No `str::split`, HMAC type, `base64::Engine` instance or `div_ceil` remains.

Run 3 also checked the B6 alternative, a crate-namespace definition of `core.num.I64.from_be_bytes`. A probe was written (its compile and `#print axioms` output were not recorded), but the refactor no longer needs it.

**Cost so far:** about 10 minutes to build Charon and Aeneas, about 1 minute per translation, and about 10 seconds per Lean compile. In total, roughly one day of agent-assisted investigation across the three runs.

### Process

The work runs in three phases. Only phase B is per function. Translation and its review happen once for the whole crate, because one Aeneas run produces every target and its exclusions, patches and axioms affect many targets at once. Proof refinement happens once at the end, because earlier proofs can still break until everything is proved.

```
Phase A — once, crate-wide (S01–S04a, S08–S09)
  scope → translate → review the translation → CI on
Phase B — per function, pipelined in batches (S05–S15)
  spec draft → ≥ 2 independent agent reviews → human sign-off → proof → restated theorem in spec file
Phase C — once, after every proof is checked (next sprint, Section 12)
  proof refinement, with spec statements frozen
```

**Phase A: translation and its review.**
1. Record the scope decision of Section 1 (S01).
2. Install the pinned bundle; translate with the Charon settings of Section 9 (S03, S04a).
3. Triage every error and skipped item: out of scope → `exclude`; in scope → patch or upstream fix; `opaque` only as the last resort. Check that every target has a real body in `Funs.lean`.
4. Review the trusted part of the translation, not the generated Lean: the `exclude`/`opaque` lists and their comments, any patches, and the external models (definitions, structures and `opaque` constants since S08–S09; S04a, S08–S09). Each item gets at least two independent agent reviews, then sign-off by the spec owner.
5. Turn on the three CI workflows (S03, S04a). From then on, the translation can only change through a reviewed PR that regenerates it.

Phase B may start drafting specs during phase A (S05 needs only S01), but no proof starts before step 4 has signed off the external models that proof uses (S08/S09 signed off) and any trusted axiom it uses (none since S08–S09).

**Phase B: per-function pipeline.** Each target moves through its own pipeline. A proof starts as soon as its own spec is signed off; it does not wait for the whole batch. Targets are batched in call-graph order, because an E proof uses the accepted W theorems and never unfolds a W definition:

| Batch | Targets | Specs | Proofs | Needs |
|---|---|---|---|---|
| 1 | W01–W06, W12–W15, `frame_roundtrip` | S05 | S06 | phase A translation |
| 2 | W07–W11 | S05 | S10 | batch 1 (W05, W06) |
| 3 | E01–E04 | S05 | S07 | batch 1 |
| 4 | E07, E08 | S05 | S11 | batches 2–3 (E07/E08 call E02), external models used (S08/S09 signed off) |
| 5 | E09a, E09, E10, E11 | S05, codec state S12 | S13, S14 | batches 2–3, S12 |
| 6 | round trips | S05 | S15 | batches 4–5 |

In each pipeline:
- The drafter (the `mcp-spec` agent or a person) writes the statement into `formal/specs/Drafts/`, citing the Rust lines for each clause.
- At least two `mcp-review` runs review it independently with `AI_PR_REVIEW_QUESTIONS.md`. Each checks three things: is the spec faithful to the Rust and its documentation, is it strong enough to be useful, and does it assume what it should prove? Then the spec owner signs it off (`spec: REVIEWED`).
- An `mcp-lean` worker who did not draft the spec proves it in its own proof file. Any working proof is acceptable. The worker then moves the statement from `Drafts/` into the spec file as a `theorem Theorems.…` proved by the spec theorem, with a `#guard_msgs` axiom check, and CI must pass.

**What sends work back.** Each of these is recorded in `formal/docs/blockers/Sxx.md` or the function record:

| Event | Back to | Effect |
|---|---|---|
| The prover finds a counterexample to a spec | The spec stage of phase B | `spec: DRAFT`; re-review and re-sign-off; never weaken a spec silently |
| A proof needs a new axiom or a stronger one | Phase A, step 4 | The axiom is reviewed like any other; the `#guard_msgs` diff shows it |
| A target turns out to need a patch, or the Rust source changes | Phase A, steps 2–4 | Re-translate; CI re-checks every proof; broken proofs return to `proof: OPEN` |
| A spec owner rejects a spec | The drafter | New draft; a different agent reviews it |

**Phase C: refinement.** Phase C starts only once every target is `CHECKED` or definitively `OPEN`. It shortens proofs, makes them robust to translation changes and Aeneas upgrades, and factors out shared lemmas. Spec statements must not change during it, and a `#guard_msgs` axiom list may only lose axioms, never gain any (human decision 2026-11-24: a smaller trusted base is allowed; the spec file's list and the function record's `axioms` field are updated with it). It is out of scope for this sprint (Section 12).

### Steps

| Step | Day | Depends on | Files | Owner — acceptance |
|---|---|---|---|---|
| S01 | D1 | — | `formal/docs/STATUS.md`, `board.yaml`, `functions/*.yaml` | Lead — base commit, scope decision (Section 1), named human owners and budget recorded; 25 function records |
| S02 | D1 | S01 | `CLAUDE.md`, `.claude/agents/*.md`, `docs/VERIFICATION.md`, the four `docs/` guides | Lead — roles and edit permissions defined; `CLAUDE.md` points to the guides; the guides describe the `formal/` layout, the Lean build gate (Section 5, CI), spec files with `#guard_msgs` and `STATUS.md` instead of the old layout |
| S03 | D1 | S01 | `formal/lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `formal/README.md`, `formal/trusted/aeneas-bundle.sha256`, `scripts/aeneas-*.sh`, `scripts/apply-patches.sh`, `scripts/lean-guard.sh`, `scripts/lean_guard.py`, `scripts/lean-axiom-audit.lean`, `scripts/llbc-dir-guard.sh`, `crates/rmcp/Cargo.toml`, `.gitignore`, `lean-build.yml` | Extraction — `aeneas-install.sh` installs `nightly-2026.08.20-5d08da4` and is a no-op on rerun; bundle versions match Section 5; the pinned Charon reads `[package.metadata.charon]` (otherwise the script passes the same lists as flags, recorded in the evidence); the empty project builds in CI (B10); `aeneas-translate.sh` fails on a nonzero Aeneas exit, a missing target, any `sorry`, or a dependency version mismatch; output on the fixed Linux target compared with the run-3 output |
| S04 | D1 | S01 | pilot record and S04 evidence (removed 2026-11-23; git history at 223ff12) | Extraction — runs 1–3 artifacts (refactor patch, Charon arguments, scripts, logs, token harness) copied from scratch |
| S04a | D1–2 | S03, S04 | `request_state_wire.rs`, `request_state.rs`, `model.rs` (since the D2 fallback, 2026-11-23: `formal/trusted/patches/01-request-state-wire.patch`); `formal/translation/**`; `formal/trusted/Rmcp/*External.lean`; `aeneas-translation.yml`, `patched-tests.yml` | Extraction + reviewer — two PRs, as the workflow guide requires: (1) the refactor, with the checklist of Section 9 passing, landed in the fork and the pinned commit recorded; (2) the translation, where all three CI workflows pass and every target is present in `Funs.lean` with a real body |
| S05 | D2 | S01 | `Defs.lean`, `Defs/Wire.lean`, `Defs/RequestState.lean`, `formal/specs/Drafts/`, `Specs.lean`, `Proofs.lean` | Spec drafter (`mcp-spec` or a person) + independent agent reviewers + spec owner — W01–W15 and E01–E04 statements reviewed by ≥ 2 independent agents, then signed off |
| S06 | D2–4 | S04a, S05 | W01–W06, W12–W15 proof files; `Specs/Model/RequestStateWire.lean` | Lean — W01–W06, W12–W15 checked and restated in the spec file; W01 overflow domain explicit |
| S07 | D3–4 | S06 | E01–E04 proof files; `Specs/Model/RequestState.lean` | Lean — E01–E04 checked using only W theorems |
| S08 | D3–4 | S04a | `formal/trusted/Rmcp/FunsExternal.lean` (model functions, HMAC, Base64), `Proofs/External/Base64.lean`, `Proofs/External/String.lean`, `Proofs/External/Prim.lean`, `formal/specs/Drafts/External.lean` and `Drafts/Staged/External.lean` (shared with S09), `formal/trusted/evidence/README.md`, `formal/trusted/evidence/differential/`, the S08 evidence (git history at 223ff12) | Extraction + reviewers + spec owner — `prim` models (definitions, opaque `hmacSha256`; no axiom, decision 2026-11-23) and their statements reviewed by ≥ 2 independent agents, then signed off; Base64 laws proved; RFC 4231 and Base64 vectors pass through `prim` in Rust tests; the differential check passes |
| S09 | D3–4 | S04a | `formal/trusted/Rmcp/FunsExternal.lean` (standard library, `HashMap`, `zeroize`, clock), `TypesExternal.lean`, `Proofs/External/Std.lean`, `formal/specs/Drafts/External.lean` and `Drafts/Staged/External.lean` (shared with S08), `formal/trusted/evidence/README.md`, the S09 evidence (git history at 223ff12), the `#guard_msgs` update of `formal/specs/Drafts/Staged/RequestState.lean` | Extraction + reviewers + spec owner — standard-library, `HashMap`, `zeroize` and clock models (definitions and structures; opaque `sipHash13`, `nowMs`, `SerdeJsonErrorImpl`; no axiom) and their statements reviewed by ≥ 2 independent agents, then signed off; the Rust tests named in the evidence pass |
| S10 | D4–5 | S06 | W07–W11 proof files | Lean — W07–W11 checked against `List.splitOn` and the transcript specs |
| S11 | D5–6 | S07, S08, S09, S10 | `SealRs1.lean`, `SealRs2.lean` | Lean — E07/E08 output-format theorems checked on the no-overflow domain |
| S12 | D5 | S05 | `Defs/CodecState.lean` | Spec drafter + reviewers + spec owner — codec-state invariant reviewed against the constructors |
| S13 | D6–8 | S07, S08, S09, S10, S12 | `Rs1FallbacksVerify.lean`, `OpenRs1At.lean`, `OpenRs2At.lean`, `Proofs/External/Iter.lean` (slice-iterator helper) | Lean — E09a, E09, E10 checked with full error order |
| S14 | D8 | S10, S13 | `OpenAt.lean` | Lean — E11 dispatch theorem checked |
| S15 | D8–9 | S11, S13, S14 | `Roundtrip.lean`; end of `Specs/Model/RequestState.lean` | Lean — each round-trip theorem accepted on its own; missing ones listed `OPEN` |
| S16 | D2–9 | S04a onward | `mod tests` in both target files (since the D2 fallback, 2026-11-23: in patch 01) | Review — Section 7 boundary cases and contract test vectors pass under `cargo test --features request-state` |
| S17 | D9 | accepted results | the three workflows | Lead — each CI check shown to fail once on a throwaway branch: a hand edit to `Funs.lean`, a new axiom (`#guard_msgs` diff), a `sorry`, and a failing test on the patched copy |
| S18 | D9–10 | S17 | the S18 evidence (git history at 223ff12) | Review — fresh clone: install, translate, `git status` clean, `lake build` and the `scripts/lean-guard.sh` checks pass |
| S19 | D10 | board state; no success required | `formal/docs/STATUS.md`, `formal/README.md` | Lead + human owner — honest per-function status, trusted base, bugs found, open items, cost; next-sprint scope |

In the Owner column, "spec owner" is the human who signs off specifications and axioms; "reviewers" are at least two independent `mcp-review` runs. Any spec, axiom or `Defs` entry in S05, S08, S09 and S12 may be drafted by the `mcp-spec` agent; it is reviewed with the reviewer guide before any proof of it starts. Proof steps (S06–S15) start only on signed-off specifications.

**Proofs: complete first, improve later** (VERIFICATION.md §8). In this sprint, the goal is every spec proved with no `sorry`, by whatever works. Shortening proofs, making them robust to translation changes and Aeneas upgrades, and factoring reusable lemmas happen only after everything is proved, without changing any spec statement (Section 12).

S19 is mandatory even if every other step fails.

### Gates

- **D2:** the refactor PR is approved and landed, and the translation PR passes all three CI workflows with every target present. The project owner confirms that people and budget are allocated.
  - **Fallback if the refactor is not landed in the fork:** commit the refactor as `formal/trusted/patches/01-request-state-wire.patch`, with the header VERIFICATION.md §4 requires (change, why, behaviour argument from Section 9), reviewed by multiple agents and a human. `apply-patches.sh` applies it to the copy, `patched-tests.yml` runs the crate's tests on it, and every target is labelled `patch-01`. The technical work is the same; only the linkage claim is weaker, and the patch joins the trusted base. No path in this plan leaves a target `BLOCKED` by translation. **In use since 2026-11-23 (human decision):** the patch exists, every target's linkage is `patch-01` (proved on upstream `7caec76` plus translation patch 01), and its multi-agent and human review is pending.
- **D5:** W leaves (S06) and the HMAC/Base64/standard-library boundary (S08–S09) are measured. Re-estimate the rest from actual effort. Keep every target visible.
- **D10:** `formal/docs/STATUS.md` written. Report how many functions are verified on the original source, proved with a translation patch, and open.

All twenty-five targets verified is a stretch goal. The mandatory result is:
- translation of every target, which run 3 already demonstrated;
- the excluded functions of Section 2.3 reported as excluded, with their blockers;
- whatever proofs are actually checked;
- an accurate status for the rest.

## 9. Blockers and resolutions

Each blocker lists its cause and how the wire design removes it. "Run 3" means the result is in Section 8, "Pilot results". After run 3 and the exclusions of Section 2.3, **no blocker is open anywhere in the project**; B10 is scheduled work (S03), not an unknown.

### Blocker table

| ID | Blocker (runs 1–2) | Cause | Resolution in the wire design | Evidence |
|---|---|---|---|---|
| B1 | HMAC types cannot be translated | `hmac`/`sha2` use `hybrid_array::Array`, mutually recursive with the `ArraySize` trait (a GAT); Aeneas rejects mixed type/trait recursion, and `opaque` still translates signatures | **Eliminated.** No HMAC type appears in any translated signature. MACs are computed by `prim::hmac_sha256(_verify)` on a W10/W11 transcript; their signatures use only slices, `[u8; 32]` and `bool` | Run 3 |
| B2 | `str::split` crashes Aeneas | `core::str::pattern::Pattern` has a GAT (`Searcher<'a>`) | **Eliminated.** Splitting is byte-level (W05–W09); no `str` pattern API is used | Run 3 |
| B3 | `base64` `Engine` instance missing in Lean | The generated `Engine` instance for `GeneralPurpose` is self-referential through default methods | **Eliminated.** `Engine` is used only inside the opaque `prim`; no `Engine` instance is generated | Run 3 |
| B4 | Returning a `&'static str` literal | Aeneas fails with "There should be no bottoms in the value" | **Avoided by rule** for targets: W03 returns `KidError`; E04 maps it to two `const` messages with the same text. `with_rs1_signing`/`with_rs1_fallback` are excluded (Section 2.3) | Run 3 |
| B5 | Loop fixed point not found in `open_rs1_at` | Aeneas cannot join the loop contexts there | **Eliminated.** The loop lives in E09a, which takes only shared references; W loops are index `while` loops | Run 3 |
| B6 | Wrong library signature for signed `from_be_bytes` | The pinned library types `i64::from_be_bytes` over `I8` bytes | **Eliminated.** W12 is `u64::from_be_bytes(head) as i64`, which is bit-identical. A crate-namespace definition was probed as a backup | Run 3; probe |
| B7 | Lean keyword used as an identifier | The pinned Aeneas does not escape keywords (`matches`, and in run 3 `from`, `prefix`) | **Avoided by rule** (Section 2.1, rule 6) | Run 3 |
| B8 | Charon cannot name inherent-impl methods | The name matcher never matches inherent-impl elements | **Eliminated for W** (free functions). E targets are reached with `start_from` on the module and the `_` glob | Run 3 |
| B9 | Out-of-scope items break the Lean compile | JSON wrappers pull in `serde`; the `Error` impl uses `source` | **Excluded** (Section 2.3) in the Charon settings below | Run 3 |
| B10 | Generated Lean not yet built in-repo | All runs compiled against an existing library build | **Scheduled:** S03 installs the release bundle and builds `formal/` in CI; S18 reproduces from a fresh clone | — |
| B11 | Nested borrows (`&[&[u8]]`) | "Found a case of unsupported nested borrows" | **Avoided by rule** (rule 3). `any_key_verifies` is never added (Section 2.3); E09a keeps the ring loop | Run 3 |
| B12 | Self-referential core `Eq for str` instance | The generated `impl_def` uses `core.cmp.Eq.assert_fields_are_eq.default` of itself, and Lean cannot resolve the recursion | **Eliminated.** Only excluded functions pulled the instance in; with the Section 2.3 exclusions it is not generated, so no hand edit is needed | Run 3 (final) |
| B13 | `seal_at`, `new_with_keyring` and the `Debug`/`Display` impls fail in Aeneas ("Unreachable", internal error, type assertion) | Aeneas limitations in the pinned version | **Excluded** (Section 2.3) | Run 3 |

**Amendment (2026-11-24, translation patch 03 v2; measured on Aeneas `nightly-2026.11.24-fb44cb4`, Charon `0.1.324`; reviewed and signed off 2026-11-24).** This amends the table without rewriting it:
- **B4 is gone on this toolchain:** `with_rs1_signing` and `with_rs1_fallback` translate with only their `exclude` entries removed.
- **B12 is gone on this toolchain:** the newly translated functions pull in the `Eq for str` instance again (`Str.Insts.CoreCmpEq` in the generated `Funs.lean`, whose `assert_fields_are_eq` refers to the instance itself), and it compiles in Lean with no hand edit.
- **B13 is gone on this toolchain** for `new_with_keyring` (no source change) and, with translation patch 03, for `seal_at` (the "Unreachable" error came from matching on a field read through the shared reference `options`; matching on a local copy works) and for `open_json_with` (the `FnOnce` impl rustc generates for a variant constructor used as a function: "Arrow types are not supported yet"); minimal reproducers are kept outside the repository. The `Debug`/`Display` impls stay excluded (N15, separate step).
- **B9 is narrowed** to `seal_json` and `seal_json_with` (and the `Error` impl): Aeneas does not support the mutually recursive trait declarations of `serde_core::ser` (blocked upstream; reproducer kept in a scratch directory outside the repository). Once that is fixed upstream, `seal_json*` would additionally need the variant-constructor workaround of patch 03 hunk 2: `.map_err(RequestStateError::Serialization)` hits "Arrow types are not supported yet" (`request_state.rs` 133:4-133:46 / 461:4-468:5 of the patched copy). `open_json` and `open_json_with` translate once `serde_core` is `opaque` instead of excluded (only signatures and trait declarations are translated; `DeserializeOwned` appears in their signatures); the crate `serde` stays excluded. `scripts/check-original-linkage.sh` requires the non-`request_state` `exclude` list to be exactly `["serde"]`, and `PINNED_DEPS` gains `serde_core 1.0.229`.
- The external models these functions need (14 functions, 2 types, the `opaque` constants `ExtModel.randomState`, `ExtModel.serdeJsonFromSlice`, `ExtModel.SerdeJsonErrorImplCarrier`) are recorded in `formal/docs/STATUS.md`, "Trusted base", and `formal/trusted/evidence/README.md`; reviewed and signed off by the spec owner 2026-11-24.

### Refactor (replaces the run-2 adapter)

The refactor is a real change to the SDK source, landed in the fork, not a translation patch: it adds public API that the user asked for (Section 1). Translation patches (VERIFICATION.md §4) are reserved for behaviour-preserving workarounds applied only to the copy in `.llbc/work/`; none are planned.

**D2 fallback (human decision 2026-11-23).** The refactor was not landed, so the paragraph above no longer holds: the D2 fallback (Section 8) is in use. The refactor and all its tests (S04a, S16) are `formal/trusted/patches/01-request-state-wire.patch` on upstream `7caec76`, applied only to `.llbc/work/` by `scripts/apply-patches.sh`; the SDK `*.rs` files are byte-identical to `7caec76`, and every target's linkage is `patch-01` (proved on upstream `7caec76` plus translation patch 01). The behaviour argument below is the patch's argument; its link to upstream behaviour is the byte-identity regression tests and the S04a differential check (argued and tested, not proved). Landing the refactor upstream would let the patch be deleted and the targets become `ORIGINAL`.

| Change | Behaviour argument for review |
|---|---|
| New public module `request_state_wire` (Section 2.1) | Pure functions; the only consumer in the SDK is the codec |
| Codec constants come from `wire` | Same values; each is defined once, except the four recorded items of Section 2.1, each with its own reason: the `&str` `VERSION_V1`/`V2` (a `const` `from_utf8` derivation would give Charon a panicking global; not tried on this tree), the "255" in the E04 message (E04 keeps `&'static str` messages with the base text), the `MAX_ENCODED_KID_LEN` alias (an alias, not a literal), and `prim::hmac_sha256` returning `[u8; 32]` rather than `[u8; TAG_LEN]` (a stable signature for the S08 axioms); checked by the test `codec_constants_agree_with_wire` and tag-length checks against `wire::TAG_LEN` (the S04a evidence (git history at 223ff12), "Deviation from plan §2.1/§9 'defined once'") |
| `open_at` uses W07 | First `.`-component comparison, as before |
| `open_rs1_at`/`open_rs2_at` use W08/W09 | `None` exactly when the original part checks returned `MalformedFormat`; component equality argued in Section 3 |
| `mac_v1`/`mac_v2` deleted; seal/open use `prim::hmac_sha256(_verify)` on W10/W11 | Same bytes are MACed (Section 3); `verify` still uses `hmac`'s constant-time comparison; errors are returned in the same order |
| `URL_SAFE_NO_PAD` calls replaced by `prim::b64_*` | Same engine and calls; decode errors still map to `InvalidEncoding` |
| `open_authenticated_body` uses W14; `seal_at` uses W15 (`seal_at` itself is excluded, Section 2.3 (amended 2026-11-24, translation patch 03: `seal_at` translates, Section 9, "Blocker table" amendment); W15 stays a public target with the `frame_roundtrip` lemma) | Same framing and expiry comparison; W12 is bit-identical to `i64::from_be_bytes` |
| `validate_*` use W02/W03 | Same conditions; same error values and messages |
| Fallback loop in `rs1_fallbacks_verify` | Loop body unchanged; every fallback is still tried; the empty-fallback check still comes before decoding |

Test-only changes: the `base64`/`hmac`/`sha2` imports and the `HmacSha256` alias move into `mod tests`. One test computes its tag with `prim::hmac_sha256` on W11.

**Review checklist for the refactor PR:**
- [ ] The existing request-state tests and the Section 7 boundary tests pass.
- [ ] RFC 4231 HMAC vectors and Base64 vectors pass through `prim`.
- [ ] Tokens sealed before and after the change are byte-identical for fixed keys and inputs, in a committed regression test. This was pre-checked in run 3 (9 tokens and 162 `open` results); the test must add `Expired` and `InvalidKeyId`.
- [ ] Each new public item has documentation and follows the Aeneas-safe rules of Section 2.1; enums and structs are `#[non_exhaustive]`.
- [ ] The existing public API is unchanged; the only addition is `rmcp::model::request_state_wire`.

### Charon settings (`crates/rmcp/Cargo.toml`)

What gets translated is set in the crate's `Cargo.toml`, not in the script (VERIFICATION.md §3). The lists below are the run-3 final command translated into settings; every entry carries a comment saying why it is there. S03 confirms the key names against `charon cargo --help` for the pinned Charon.

**Phase 2:** Section 15 adds 25 `start_from` entries and opaque entries for the widened dependency graph and the `AuthorizationManager` type; `exclude` is unchanged.

**(Amended 2026-11-24, translation patch 03: the block below is the Phase 1 state. The `exclude` entries of `seal`, `seal_with`, `seal_at`, `new_with_keyring`, `with_rs1_signing`, `with_rs1_fallback`, `open_json` and `open_json_with` are removed, `serde_core` moved from `exclude` to `opaque` (`exclude` keeps `"serde"`), and `now_ms` is called by the targets `seal_with` and `seal`; `crates/rmcp/Cargo.toml` is authoritative. See the "Blocker table" amendment above and Section 19.)**

```toml
[package.metadata.charon]
start_from = [
  "rmcp::model::request_state",
  "rmcp::model::request_state_wire",
]
hide_marker_traits = true
exclude = [
  # B9: serde is out of scope; only the excluded JSON wrappers use it.
  "serde", "serde_core",
  # Section 2.3, B9: JSON wrappers and the Error impl.
  "rmcp::model::request_state::_::seal_json",
  "rmcp::model::request_state::_::seal_json_with",
  "rmcp::model::request_state::_::open_json",
  "rmcp::model::request_state::_::open_json_with",
  "rmcp::model::request_state::{impl core::error::Error for rmcp::model::request_state::RequestStateError}",
  # Section 2.3, B13: Aeneas "Unreachable" error in seal_at; seal and seal_with call it.
  "rmcp::model::request_state::_::seal",
  "rmcp::model::request_state::_::seal_with",
  "rmcp::model::request_state::_::seal_at",
  # Section 2.3, B13: Aeneas internal error.
  "rmcp::model::request_state::_::new_with_keyring",
  # Section 2.3, B4: "no bottoms in the value".
  "rmcp::model::request_state::_::with_rs1_signing",
  "rmcp::model::request_state::_::with_rs1_fallback",
  # Section 2.3, B13: Aeneas type assertion / internal error in formatting impls.
  "rmcp::model::request_state::{impl core::fmt::Debug for rmcp::model::request_state::RequestStateError}",
  "rmcp::model::request_state::{impl core::fmt::Display for rmcp::model::request_state::RequestStateError}",
  "rmcp::model::request_state::{impl core::fmt::Debug for rmcp::model::request_state::RequestStateCodec}",
  # Derived Debug; depends on the Aeneas axiom Aeneas.Std.core.fmt.Formatter and native-decide
  # string axioms; not used by any target (human decision 2026-11-22).
  "rmcp::model::request_state::{impl core::fmt::Debug for rmcp::model::request_state::SealOptions}",
  "rmcp::model::request_state::{impl core::fmt::Debug for rmcp::model::request_state::SealMode}",
  "rmcp::model::request_state_wire::{impl core::fmt::Debug for rmcp::model::request_state_wire::KidError}",
  "rmcp::model::request_state_wire::{impl core::fmt::Debug for rmcp::model::request_state_wire::Version}",
  "rmcp::model::request_state_wire::{impl core::fmt::Debug for rmcp::model::request_state_wire::Rs1Parts}",
  "rmcp::model::request_state_wire::{impl core::fmt::Debug for rmcp::model::request_state_wire::Rs2Parts}",
  "rmcp::model::request_state_wire::{impl core::fmt::Debug for rmcp::model::request_state_wire::FrameError}",
]
opaque = [
  # Wraps HMAC and base64 Engine types that cannot be translated (B1, B3); no Rust model to patch in; Lean models: Section 4.
  "rmcp::model::request_state_wire::prim",
  # Reads the system clock (I/O); no Rust model to patch in; Lean model: Section 4. Used only by non-target wrappers.
  "rmcp::model::request_state::_::now_ms",
  # External crates: only signatures are needed; Lean models: Section 4.
  "zeroize", "base64", "hmac", "sha2", "thiserror", "chrono", "serde_json",
]
```

`scripts/aeneas-translate.sh` then runs, on the patched copy in `.llbc/work/crates/rmcp`:

```sh
charon cargo --preset=aeneas --dest-file .llbc/rmcp.llbc -- \
  --config profile.dev.overflow-checks=true --config profile.dev.debug-assertions=true \
  --target x86_64-unknown-linux-gnu --no-default-features --features request-state --lib
aeneas -backend lean -split-files -emit-json -no-progress-bar \
  -dest .llbc/out -subdir Rmcp .llbc/rmcp.llbc
```

`.llbc` stands for `$RMCP_LLBC_DIR` (default `<repo>/.llbc`). Aeneas writes into the scratch directory `$RMCP_LLBC_DIR/out`, never directly into `formal/translation/`; only after the output checks pass does the script copy `out/` to `formal/translation/` (or `$RMCP_TRANSLATION_DEST`) with `rsync -a --delete --checksum`, and it refuses a destination that holds anything other than an earlier output (`Rmcp/`, `translation.json`). The script fails on a nonzero Charon or Aeneas exit, a target missing from `Funs.lean`, any `sorry` in the generated files, or a dependency version or source mismatch (Section 4). Aeneas writes the `*External_Template.lean` files next to `Funs.lean` (git-ignored); the hand-written `formal/trusted/Rmcp/FunsExternal.lean` and `TypesExternal.lean` are started from them once (S04a) and then maintained by hand (S08–S09). The templates contain `set_option linter.dupNamespace false`, `set_option linter.hashCommand false` and `set_option linter.unusedVariables false`, which `scripts/lean-guard.sh sources` rejects in `trusted/`; these lines are removed when the externals are started from the templates (lead decision, S04a translation PR).

**Open item for the S04a translation PR (part 2): axiom audit of the translation (human decision 2026-11-22; the S04a evidence (git history at 223ff12)).** The first S04a translation failed `scripts/lean-guard.sh axioms` (with `Rmcp` as a default target) through the derived `Debug` impls: their `Debug::fmt` bodies depend on the Aeneas library axiom `Aeneas.Std.core.fmt.Formatter` and on `_native.decide.ax_*` axioms that Aeneas's `toStr` leaves for every string literal (`by decide +native`). Decided: (1) the seven derived `Debug` impls (`KidError`, `Version`, `FrameError`, `Rs1Parts`, `Rs2Parts`, `SealMode`, `SealOptions`) are excluded in the Charon settings of `crates/rmcp/Cargo.toml` (shown in the block above); no target uses them, and the regenerated translation keeps all 25 targets; (2) native-code axioms are a separately classified trust item, as in the SPQR project: the audit accepts one only if its statement is the `toStr` side condition `decide ("…".toByteArray.size ≤ Aeneas.Std.U32.max) = true` of a string literal and it is listed with its statement hash in `formal/trusted/native-axioms.lock`, which holds the five literals of target code (`VERSION_V1`, `VERSION_V2`, `KID_EMPTY_MSG`, `KID_TOO_LONG_MSG`, the `expect` message of `rs1_fallbacks_verify`). These side conditions have a kernel proof (`simp only [U32.max, U32.numBits, UScalarTy.numBits]; decide`), so an upstream Aeneas `toStr` fix and a rev bump would remove the five axioms (open, preferred to a local replacement). The placeholder externals are replaced at S08–S09 by definitions, structures and `opaque` constants, so no trusted axiom remains and `axioms.lock` stays empty (human decision 2026-11-23, Section 4).

**Translating carefully** (VERIFICATION.md §5). After every run, check each error and skipped item: out of scope → `exclude`; in scope → patch, or fix upstream; `opaque` only as the last resort. Check that every target appears in `Funs.lean` with a real body, and commit the regenerated output together with the settings that produced it.

### Upstream

Upstream Aeneas `main` (`2e3d4488`, 20 November 2026; release `nightly-2026.11.22-2e3d448`) fixes B6 (#1355) and B7 (#1306), and may improve B5 (#1348). B1, B4 and B8 are still present there. The project no longer depends on any of them, so **this sprint stays on `nightly-2026.08.20-5d08da4`**. Filing upstream reproducers is optional; it does not bring an excluded function back (Section 2.3).

## 10. Claude agent stack

The agent role files and the `mcp-cycle` skill live in `.claude/`, which is local to each
contributor's checkout and not committed (human decision 2026-11-23; `.gitignore`). The templates
below define them.

The lead is the main Claude Code session. It owns the board, integrates changes, and is the only writer of shared files: `formal/translation/` (regenerated, never edited), the library roots, `formal/lakefile.toml`, the Charon settings in `crates/rmcp/Cargo.toml`, and the scripts. Workers run in separate git worktrees.

| Role file | Responsibility | May edit |
|---|---|---|
| `mcp-extraction.md` | Run the install and translate scripts, list external declarations, draft external models and patches, write reproducers for new failures | `formal/trusted/Rmcp/*External.lean`, `formal/trusted/patches/`, `formal/trusted/evidence/`, the pilot record (removed from git history on 2026-11-23), `formal/docs/blockers/` |
| `mcp-spec.md` | Draft specifications, `Defs` and axiom statements, each clause citing the Rust lines or plan section it encodes | the assigned `formal/specs/Defs/…` or `formal/specs/Drafts/…` file |
| `mcp-lean.md` | Prove one signed-off spec against the generated code, then restate it in the spec file | the assigned `formal/proofs/Proofs/…` file and its entry in the spec file |
| `mcp-review.md` | Independent review of specs, axioms and patches with `AI_PR_REVIEW_QUESTIONS.md` (run at least twice, in separate sessions, with no access to each other's reports); boundary tests and contract test vectors; may propose labelled replacement statements | `mod tests` in both target files, review notes |

Start with the lead and two workers (extraction and review). Add the spec worker when S05 starts, and the Lean worker once the translation and a signed-off spec exist. Because the W proofs are independent of each other, S06 and S10 can use two Lean workers in parallel. Run one heavy build at a time until memory use is measured. A Lean LSP / Beam MCP server (goals at a point, run a tactic, `#print axioms`) speeds proof work; it is an optional aid.

Template for `.claude/agents/mcp-lean.md`:

```markdown
---
name: mcp-lean
description: Prove one signed-off request-state spec against the Aeneas translation.
---
Read CLAUDE.md, docs/VERIFICATION.md and the task given by the lead.
Edit only the assigned file under formal/proofs/Proofs/ and the spec's restated theorem in formal/specs/Specs/.
Do not change spec statements, Defs, generated files, or anything under formal/trusted/.
Do not prove a spec that this session drafted.
Do not add axioms, sorry, native_decide or bv_decide. Follow docs/STYLE_GUIDE.md.
For an E target, use the accepted W theorems; do not unfold W definitions.
Complete first: any working proof is acceptable in this sprint.
Report the exact commands run (cd formal && set -o pipefail && lake build 2>&1 | tee .lake/build.log, then ../scripts/lean-guard.sh sources, build-log .lake/build.log and axioms), exit status, theorem names, the #print axioms output, and any open goal.
If the spec appears false, return a concrete counterexample instead of weakening it.
```

Template for `.claude/agents/mcp-spec.md`:

```markdown
---
name: mcp-spec
description: Draft one request-state specification or external axiom for independent review and human sign-off.
---
Read CLAUDE.md, docs/VERIFICATION.md, docs/WORKFLOW_AND_PR_GUIDE.md, docs/STYLE_GUIDE.md and the task given by the lead.
Edit only the assigned formal/specs/Defs/ or formal/specs/Drafts/ file.
Cite, for every clause, the Rust lines at the pinned commit or the plan section it encodes.
Cover the Ok case and every Err case, in the Rust order of checks. State preconditions as weak as the code allows.
For an axiom: never a bare Result axiom; give an exact model or ok of an opaque value.
Never set spec: REVIEWED, never accept a task, never prove or review a spec you drafted.
Report the drafted statements, their sources, and any behaviour you could not pin down.
```

Rules for every worker:
- Role prompts do not restrict anything by themselves. Enforce edit limits with permission settings and review each diff before merging.
- Specs, axioms and patches each get multiple independent agent reviews, then a human sign-off. Agent agreement alone never accepts anything.
- An AI agent may draft a specification, but the drafter may not prove or review the same statement. AI drafting and AI review are disclosed in the PR footer and recorded in the evidence file (workflow guide, "AI contributions").
- Re-translating after any source change invalidates earlier proof evidence for the affected functions; CI re-checks them on every PR.

## 11. Results template

To be filled in only with actual results, in the results section of `formal/docs/STATUS.md`:

> At SDK commit `[SHA]`, translated for `x86_64-unknown-linux-gnu` with `--no-default-features --features request-state`, the following public request-state wire functions and existing codec functions are verified against the Aeneas translation (`nightly-2026.08.20-5d08da4`): `[list]`. These results rest on the trusted base listed in `formal/README.md` and `STATUS.md`: Charon, Aeneas and Lean; the translated configuration; the HMAC-SHA256, Base64url and standard-library axioms in `formal/trusted/`; the codec-state hypothesis; the statements in `formal/specs/`; and the exclusions. They do not establish cryptographic security, constant-time execution, or correctness of the public codec wrappers. Functions not listed are open for the reasons given below.

## 12. Deferred to a later sprint

These were considered and deliberately left out to keep the sprint focused on translation and proofs. Add them only once the core results exist.

**Phase 2 status of these items:** Phase 2 (Part II) takes up none of them directly; it adds new targets. The Aeneas upgrade and the upstreaming of models are now scheduled as Phase 3 entry work (Section 23); proof refinement covers both phases (Section 25).

- The proof improvement phase (VERIFICATION.md §8): shorter, more robust, better factored proofs, with spec statements unchanged.
- Specifications for the translatable non-targets `open`, `open_with`, `new` and `try_new`.
- Upgrading the Aeneas `rev` (and then deleting any patch an upgrade makes unnecessary).
- Upstreaming the standard-library models of Section 4 to the Aeneas library.
- Proposing `request_state_wire` to the upstream SDK.
- A coverage audit with negative test files, and mutation testing.
- Per-claim cards and per-run agent provenance records, beyond the tool-and-model line that evidence files and function records already require.
- Moving `verification/host_origin/` into `formal/`.

---

# Part II — Phase 2: protocol, transport and SSRF foundations

## 13. Phase 2 scope and objective

**Source baseline.** Upstream `origin/main` `7caec762799bece6fba38e4298b8ca7db8bac12c`, the same pinned commit as Phase 1. `crates/rmcp/src/` in the repository is byte-identical to it (checked 2026-11-23 with `git diff --quiet 7caec76 HEAD -- crates/rmcp/src`). Phase 2 changes no SDK `*.rs` file and adds no translation patch that touches translated code.

**Target files** (upstream, unmodified; line numbers in Section 16 refer to `7caec76`):
- `crates/rmcp/src/model.rs`
- `crates/rmcp/src/model/task.rs`
- `crates/rmcp/src/transport/common/client_side_sse.rs`
- `crates/rmcp/src/transport/async_rw.rs`
- `crates/rmcp/src/transport/streamable_http_server/tower.rs`
- `crates/rmcp/src/transport/auth.rs`

**Selection rule.** A function is a Phase 2 target only if all of the following hold:
1. It was measured, alone and together with all other targets and the Phase 1 targets, in the pinned toolchain (Section 14):
   - Charon exits 0;
   - Aeneas exits 0 with no `[Error]` line;
   - its body is present exactly once in `Funs.lean`;
   - no generated file contains `sorry`;
   - the generated Lean compiles under `warningAsError` with no hand edit.
2. Its `#print axioms` list contains no Aeneas library axiom (in particular not `core.fmt.Formatter`), only externals that can be given definitional models, and Aeneas `toStr` native-code axioms of the accepted class (Section 4).
3. Its translation is the same from unmodified upstream as from the patched copy (Section 19), so its linkage can be `ORIGINAL`.
4. Its theorem is a lemma for a named larger function that later phases want (Section 23).
5. Its behaviour matters for security or protocol correctness, or it is a core data-model operation that most later proofs will touch.

**Objective.** Implementation-linked correctness, on the unmodified SDK source, of three groups of foundations:
- the JSON-RPC message model: classification of a message, request/response id correlation, task state, sampling content and completion references (M01–M14);
- two transport guards: the SSE event-size limiter that bounds client memory (T01–T03), and the line codec's carriage-return stripping and MCP method allow-lists (T04–T06);
- two security guards: the Host/Origin port policy of DNS-rebinding protection (T07–T08), and the IP-address classification of the OAuth metadata SSRF guard (A01–A03).

These results hold under explicitly named models of the standard-library operations they call (Section 18).

**Not claimed (Phase 2):**
- the larger functions that call the targets (`origin_is_allowed`, `host_is_allowed`, `AddressClass::of`, `MetadataAddressResolver::is_allowed`, `bounded_sse_stream`, `should_ignore_notification`, the client's response routing), which are Phase 3 candidates (Section 23);
- DNS resolution, URL parsing, HTTP handling, `async` code and `serde` (de)serialisation;
- correctness of the `std`/`core` functions behind the models (`Ipv4Addr`/`Ipv6Addr` predicates, `i64::from_str`), beyond the differential tests of Section 18;
- any configuration other than the one in Section 15;
- full MCP protocol verification.

Claims apply to `7caec76` and the configuration of Section 15 only.

## 14. Phase 2 pilot (measured 23 November 2026)

**Environment.** macOS aarch64; the pinned bundle `nightly-2026.08.20-5d08da4` from `.aeneas/` (Charon `0.1.235`, Aeneas `5d08da45`, Rust `nightly-2026-06-01`, Lean `4.31.0`); `--target x86_64-unknown-linux-gnu`, overflow checks and debug assertions on, as in Section 1. All work was in a scratch copy made by `scripts/apply-patches.sh` with `RMCP_LLBC_DIR` pointing outside the repository. Only the scratch copy's `[package.metadata.charon]` was edited. Nothing in the repository changed.

**Local-only workaround.** The macOS binaries of the bundle link `libiconv` from a Nix store path that does not exist on a machine without Nix, so `charon` aborts in `dyld`. Setting `DYLD_FALLBACK_LIBRARY_PATH=/usr/lib` loads the system `libiconv`, which reports the same version. CI runs on Linux and is unaffected. S21 records this in `formal/README.md`, "Commands".

**Method.** One Charon + Aeneas run per candidate (about 7 seconds each, with the Phase 1 start points kept), then combined runs, a Lean build of the combined output, `#print axioms` per target, and a translation of the selected targets from the *unpatched* upstream source. The combined Charon invocation (from the scratch copy's `crates/rmcp`):

```sh
DYLD_FALLBACK_LIBRARY_PATH=/usr/lib RUSTUP_TOOLCHAIN=nightly-2026-06-01 \
"$BUNDLE/charon" cargo --preset=aeneas --dest-file x.llbc -- \
  --config profile.dev.overflow-checks=true --config profile.dev.debug-assertions=true \
  --target x86_64-unknown-linux-gnu --no-default-features \
  --features request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth \
  --lib
"$BUNDLE/aeneas" -backend lean -split-files -emit-json -no-progress-bar -dest out -subdir Rmcp x.llbc
```

**Results.**

| Check | Result |
|---|---|
| Widened features, Phase 1 start points only | Charon 0, Aeneas 0; `Types.lean` and `Funs.lean` **byte-identical** to the committed `formal/translation/` (also with `auth` added) |
| Each of the 25 selected targets alone | Charon 0, Aeneas 0, 0 errors, 0 `sorry` |
| All 25 together with Phase 1 | Charon 0, Aeneas 0, 0 errors, 0 `sorry`; each target defined exactly once; all 148 Phase 1 blocks (blank-line-separated paragraphs of the generated files: 20 in `Types`, 128 in `Funs`) present verbatim |
| Lean build of the combined output (`lake build Rmcp`, externals from the generated templates) | `Build completed successfully`, under `warningAsError`, no hand edit |
| New definitions in `Funs.lean` | The 25 targets plus 10 generated helpers: `observe_loop` and `observe_loop.body`; the `matches` closure's `FnOnce` instance and its `call_once`; the derived `PartialEq` instance of `NumberOrString` and its `eq`; and the trait instances `PartialEq` for `str` and `Arc`, `FromStr` for `i64` and `SlicePattern` for arrays |
| `#print axioms` per target | No `fmt` axiom anywhere. 30 distinct `toStr` native-code axioms (T05: 10, T06: 28, T07/T08: 2; overlapping). The other entries are template externals that Section 18 replaces by definitions. `TaskStatus::is_terminal` depends on no axiom. |
| The 25 translated from **unpatched** upstream `7caec76` | Charon 0, Aeneas 0, 0 `sorry`. All 35 `Funs.lean` definitions and all 22 `Types.lean` blocks of that run are identical to those of the patched run once `Source:` line numbers are normalised; patch 01 adds two lines to `model.rs`, so the docstring line numbers shift by two. |
| New externals | 26 functions and 6 types (Section 18) |
| Cost | About 7 s per Charon + Aeneas run with a warm cache, about 10 s per Lean build of `Rmcp`; about 17 GB of Cargo build output for the widened feature set (scratch, deleted) |

**Candidates tried and not taken** (Section 16.5 gives the reason for each; all were run alone except `normalize_authority`, `FixedInterval::retry`, `NeverRetry::retry` and `EventId::from_str`, see 16.5): `requires_base64`, `is_tchar`, `encode_header_value`, `decode_header_value`, `extract_scope_from_header`, `normalize_host`, `normalize_authority`, `quality_is_acceptable`, `host_is_allowed`, `origin_is_allowed`, `validate_tool_name`, `ProtocolVersion::{has_initialize, known_up_to}`, `ResultType::is_complete`, `integral_f64_to_i64`, `json_rpc_body_preview`, `StringSchema::with_length`, `NumberSchema::with_range`, `CreateMessageRequestParams::validate`, `JsonRpcMessageCodec::{max_length, new_with_max_length}`, `LocalSessionWorker::next_http_request_id`, `EventId::from_str`, `AddressClass::of`, `MetadataAddressResolver::is_allowed`, `CompletionInfo::{new, with_all_values}`, `ExponentialBackoff::retry`, `FixedInterval::retry`, `NeverRetry::retry`. Held in reserve (they translate with Charon 0 / Aeneas 0 / no `sorry` in a combined run with the 25; neither a Lean build of that run nor their `#print axioms` was done, so S21's checks must pass for a reserve before it enters): `SamplingMessageContentBlock::{as_text, as_tool_use, as_tool_result}`, `CompletionContext::has_arguments`, `CompletionInfo::{has_more_results, total_available}`.

## 15. Phase 2 translated configuration and Charon settings

**One configuration for both phases** (human decision H1). The feature list of Section 1 is widened, and nothing else changes:

```
--target x86_64-unknown-linux-gnu --no-default-features
--features request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth
--lib
--config profile.dev.overflow-checks=true --config profile.dev.debug-assertions=true
```

The pilot showed that the Phase 1 translation is byte-identical under the widened list, so no Phase 1 proof is affected. `FEATURE_ARGS` in `scripts/aeneas-translate.sh`, the `cargo test` line of `patched-tests.yml` (which reads `FEATURES` from the script and adds `macros`, because upstream tests in `tool_traits.rs` need it; `rmcp-macros`, a workspace path crate, is the one dependency of that test build allowed not to come from crates.io; human decision 2026-11-23), `formal/README.md` and the module docstrings of the spec files change together, in the S21 PR, as do the translated-configuration text, feature flags and procedure commands of `docs/WORKFLOW_AND_PR_GUIDE.md` and `docs/AI_PR_REVIEW_QUESTIONS.md` (deferred there from S20).

**Dependencies.** The widened list pulls in `tokio`, `http`, `hyper`, `reqwest` (without a TLS backend), `oauth2`, `url` and others. The translate script's existing check (Section 4) still requires every dependency to come from crates.io, and Cargo still resolves the graph afresh on every run. `PINNED_DEPS` gains nothing: the Phase 2 models describe `core`/`std` of the pinned toolchain, not a crate. A crate is pinned only when a model cites its source. **Correction found at S21 (the pilot did not run this check):** `oauth2` 5.0.0, reached through `auth`, brings `sha2 0.10.9`, `digest 0.10.7` and `base64 0.22.1` next to the pinned `sha2 0.11.1`, `digest 0.11.3` and `base64 0.23.1`, so the old rule (each pinned crate resolves to exactly one version) failed. Human decision 2026-11-23: the pin is checked on rmcp's own edges. The version that counts is the one `rmcp` reaches through normal dependency edges whose intermediate packages are all pinned crates, read from `cargo tree --prefix depth` for the translated configuration (`cargo metadata` would give the workspace-unified graph, with features only other workspace members enable); it must be unique and equal the pin. Other versions used only by other crates are logged and allowed, because no translated target calls them and the models describe only the versions `rmcp` uses.

**Charon settings** added to `[package.metadata.charon]` in `crates/rmcp/Cargo.toml`. Every entry carries its comment, as in Section 9.

```toml
start_from = [
  # ... Phase 1 entries unchanged ...
  # Phase 2 (Section 16). Inherent methods are reached with the `_` glob (B8); each glob was
  # checked to match exactly one item (Section 14); the translate script fails if a glob later
  # matches more or fewer (rule 3 below).
  "rmcp::model::_::into_request",            # M01
  "rmcp::model::_::into_response",           # M02
  "rmcp::model::_::into_notification",       # M03
  "rmcp::model::_::into_error",              # M04
  "rmcp::model::_::into_result",             # M05
  "rmcp::model::_::numeric_string_value",    # M06
  "rmcp::model::_::matches_response_id",     # M07
  "rmcp::model::task::_::is_terminal",       # M08
  "rmcp::model::_::into_vec",                # M09
  "rmcp::model::_::is_empty",                # M10
  "rmcp::model::_::len",                     # M11
  "rmcp::model::_::first",                   # M12
  "rmcp::model::_::as_prompt_name",          # M13
  "rmcp::model::_::as_resource_uri",         # M14
  "rmcp::transport::common::client_side_sse::_::check_limit",   # T01
  "rmcp::transport::common::client_side_sse::_::finish_line",   # T02
  "rmcp::transport::common::client_side_sse::_::observe",       # T03
  "rmcp::transport::async_rw::without_carriage_return",         # T04
  "rmcp::transport::async_rw::is_standard_notification",        # T05
  "rmcp::transport::async_rw::is_standard_method",              # T06
  "rmcp::transport::streamable_http_server::tower::default_port",  # T07
  "rmcp::transport::streamable_http_server::tower::_::matches",    # T08
  "rmcp::transport::auth::_::embedded_ipv4",                    # A01
  "rmcp::transport::auth::_::is_disallowed_metadata_ipv4",      # A02
  "rmcp::transport::auth::_::is_disallowed_metadata_ipv6",      # A03
]
opaque = [
  # ... Phase 1 entries unchanged ...
  # External crates reached by the widened features: only signatures are needed; no target
  # body calls into them.
  "http", "tokio", "tokio_util", "tracing", "tracing_core", "futures", "futures_util",
  "futures_core", "bytes", "sse_stream", "hyper", "tower_service", "uuid", "schemars",
  "pin_project_lite", "tokio_stream", "http_body", "http_body_util", "rand", "async_trait",
  "pastey", "oauth2", "reqwest", "url",
  # The type only: A01–A03 are associated functions of AuthorizationManager that never use
  # `self`. Translating the type pulls in oauth2's client type aliases, on which Aeneas fails
  # with an internal error (pilot, Section 14). Opaque, the type does not even appear in
  # the generated files; the three function bodies are still translated.
  # [S23 correction, 2026-11-24: without this entry Charon itself fails (a hax panic on the
  # fields `Arc<dyn CredentialStore>` and `Arc<dyn StateStore>`, auth.rs:1252-1253, async-fn
  # traits), before Aeneas runs; and no type declaration is generated, while the name still
  # appears as the namespace of the three translated functions. The comment in
  # crates/rmcp/Cargo.toml was corrected at S37; comments are outside the S22 pins, which hash
  # the parsed manifest without the Charon table.]
  "rmcp::transport::auth::AuthorizationManager",
]
```

`exclude` gains nothing. None of the rejected candidates is reachable from a Phase 2 start point, so none is translated. Section 2.3's rule ("nothing we verify may depend on an excluded item") holds trivially.

**Charon naming rules learned in the pilot** (they join the coding rules of Section 2.1 as process rules for the lead):
1. A `start_from` path that resolves to no item is fatal: Charon stops with "Code failed to compile" (B20).
2. Impl patterns (`{impl Trait for Type}`) are accepted only as the first path element, and `_` does not match trait-impl methods (B20).
3. The `_` glob is fragile, because a future upstream method with the same name in the same module would be pulled in. `aeneas-translate.sh` checks every `_` glob of `start_from` against `translation.json`: it must match exactly one Rust item (distinct local `rust_name`s, matched segment by segment), and the target list requires each target's `def`. Stated exception (translation patch 04, human decisions 2026-11-25): the globs `rmcp::model::skill::_::new` (the `new` methods of `GetSkillResult`, `SkillFrontmatter`, `SkillResource`, `SkillsCapability` and `Skill`; K02, K04, K08, K10, K17) and `rmcp::model::skill::_::with_meta` (of `GetSkillResult` and `Skill`; K11, K20) must match exactly the `rust_name`s listed for them in `MULTI` of the script, no more and no fewer. This turns a glob that catches a new upstream item, or nothing, into a CI failure rather than a silent change (implemented at S21).

## 16. Phase 2 targets

IDs: **M** = message model (`model.rs`, `model/task.rs`), **T** = transport guards, **A** = SSRF address guard. The ID order is a work queue, not a call graph. Line numbers are at `7caec76`. "Reuse" names the Phase 3 function whose proof needs the theorem (Section 23).

### 16.1 Message model (M01–M14)

| ID | Function (generated name under `rmcp.`) | Line | Independent specification | Reuse |
|---|---|---|---|---|
| M01 | `JsonRpcMessage::into_request` (`model.JsonRpcMessage.into_request`) | `model.rs:819` | `Some (request, id)` iff the message is `Request`, else `None` | service dispatch, client routing |
| M02 | `JsonRpcMessage::into_response` | `model.rs:825` | `Some (result, id)` iff `Response` | client routing |
| M03 | `JsonRpcMessage::into_notification` | `model.rs:831` | `Some notification` iff `Notification` | notification handling |
| M04 | `JsonRpcMessage::into_error` | `model.rs:837` | `Some (error, id)` iff `Error` (`id : Option RequestId`) | client routing |
| M05 | `JsonRpcMessage::into_result` | `model.rs:843` | `Response r` → `Some (Ok r.result, Some r.id)`; `Error e` → `Some (Err e.error, e.id)`; `Request`/`Notification` → `None` | client routing |
| M06 | `NumberOrString::numeric_string_value` | `model.rs:322` | `Number _` → `None`; `String s` → `Defs.parseI64 s.bytes`: Rust's `i64::from_str` grammar (optional `+`/`-`, at least one ASCII digit, value in `i64` range), `None` otherwise | response-id correlation |
| M07 | `NumberOrString::matches_response_id` | `model.rs:330` | `self = other` (derived equality: equal numbers, or equal string contents) ∨ (`self = Number n` ∧ M06 `other = some n`) | client response routing |
| M08 | `TaskStatus::is_terminal` (`model.task.TaskStatus.is_terminal`) | `task.rs:38` | `true` iff `Completed`, `Failed` or `Cancelled` | task manager transitions |
| M09 | `SamplingContent::into_vec` | `model.rs:2926` | `Single x` → `[x]`; `Multiple v` → `v` | sampling validation |
| M10 | `SamplingContent::is_empty` | `model.rs:2934` | `Single _` → `false`; `Multiple v` → `v = []` | sampling validation |
| M11 | `SamplingContent::len` | `model.rs:2942` | `Single _` → `1`; `Multiple v` → `v.length` | sampling validation |
| M12 | `SamplingContent::first` | `model.rs:2958` | `Single x` → `some x`; `Multiple v` → `v.head?` | sampling validation |
| M13 | `Reference::as_prompt_name` | `model.rs:3741` | `Prompt p` → `some` (the bytes of `p.name`); otherwise `none` | `completion/complete` routing |
| M14 | `Reference::as_resource_uri` | `model.rs:3749` | `Resource r` → `some` (the bytes of `r.uri`); otherwise `none` | `completion/complete` routing |

Joint lemmas, stated with the targets because later phases use them as a set: M10 `= (M11 = 0)`; M12 `= (M09).head?`; M11 `= (M09).length`; exactly one of M01–M04 is `Some` for every message.

### 16.2 Transport guards (T01–T08)

| ID | Function | Line | Independent specification | Reuse |
|---|---|---|---|---|
| T01 | `SseEventSizeLimiter::check_limit` | `client_side_sse.rs:90` | `Err ()` iff `sat(retained_size + line_size) > max_size`, with `sat` the saturating `usize` sum | SSE bound |
| T02 | `SseEventSizeLimiter::finish_line` | `client_side_sse.rs:75` | New state per `Defs.Sse.finishLine`: an empty line resets `retained_size` to 0; a non-comment line adds `line_size + 1` (saturating; the joining newline); a comment line adds nothing; then `line_size := 0`, `line_is_comment := false`; result is T01 on the new state | SSE bound |
| T03 | `SseEventSizeLimiter::observe` | `client_side_sse.rs:48` | `Defs.Sse.observe st chunk`: a left fold of `Defs.Sse.step` over the bytes that stops at the first `Err`. Both the result and the final `self` are specified, because `self` is mutated before an error returns. CR, LF and CRLF end a line, and a CRLF split across two chunks is one line end (`previous_was_cr`); a line starting with `:` is a comment | `bounded_sse_stream` |
| T04 | `async_rw::without_carriage_return` | `async_rw.rs:385` | If the last byte is `\r`, the slice without it; otherwise the slice unchanged | line codec decode |
| T05 | `async_rw::is_standard_notification` | `async_rw.rs:420` | `method.bytes ∈ Defs.Methods.standardNotifications` and not in `Defs.Methods.codeOmits` (H7) | `should_ignore_notification` |
| T06 | `async_rw::is_standard_method` | `async_rw.rs:396` | `method.bytes ∈ Defs.Methods.standardRequests` and not in `Defs.Methods.codeOmits`, `∨` T05 (H7) | `should_ignore_notification`, `try_parse_with_compatibility` |
| T07 | `tower::default_port` | `tower.rs:1146` | `"http"` → `some 80`; `"https"` → `some 443`; otherwise `none` (exact, case-sensitive byte equality; callers lowercase first) | `origin_is_allowed` |
| T08 | `tower::AllowedPort::matches` | `tower.rs:1164` | `Any`, `Unspecified` → `true`; `Exact p` → `(port <|> T07 scheme) = some p` (default port: RFC 9110 §4.2.1/§4.2.2) | `origin_is_allowed` |

### 16.3 SSRF address guard (A01–A03)

| ID | Function | Line | Independent specification | Reuse |
|---|---|---|---|---|
| A01 | `AuthorizationManager::embedded_ipv4` | `auth.rs:1359` | Over the eight 16-bit segments `[a,b,c,d,e,f,g,h]`: IPv4-mapped `::ffff:0:0/96` or NAT64 `64:ff9b::/96` (RFC 6052) → `some (g·2^16 + h)`; IPv4-compatible `::/96` except `::` and `::1` → `some (g·2^16 + h)`; 6to4 `2002::/16` (RFC 3056) → `some (b·2^16 + c)`; otherwise `none` | `AddressClass::of` |
| A02 | `AuthorizationManager::is_disallowed_metadata_ipv4` | `auth.rs:1343` | `true` iff the address is in one of: `10/8`, `172.16/12`, `192.168/16` (RFC 1918), `127/8`, `169.254/16` (RFC 3927), `255.255.255.255`, `0.0.0.0`, `224/4`, `0/8`, `100.64/10` (RFC 6598), `198.18/15` (RFC 2544). Stated with `Defs.Net` prefixes on the octets, not with the `std` predicates | `AddressClass::of`, `is_allowed_metadata_url` |
| A03 | `AuthorizationManager::is_disallowed_metadata_ipv6` | `auth.rs:1370` | If A01 gives `some v4` → A02 `v4`; otherwise `true` iff `::1`, `::`, `ff00::/8`, `fe80::/10`, `fc00::/7` (RFC 4193), `2001::/32` (Teredo, RFC 4380) or `64:ff9b:1::/48` (RFC 8215) | `AddressClass::of`, `is_allowed_metadata_url` |

### 16.4 Composition theorems

| ID | Statement | Uses | Why it matters |
|---|---|---|---|
| C01 `SseEventSizeLimiter.observe_append` (plan form: `observe_append_of_observe_eq_ok`; renamed to Mathlib style 2026-11-24, was `sse_observe_append`) | Plan form: if `observe st a = Ok` with state `st'`, then `observe st (a ++ b)` equals `observe st' b` (result and state); general form (`observe_append`): `observe st (a ++ b)` is `observe st a` followed by `observe st' b` when the first call returns `Ok`; otherwise the first call's `Err` with its state | T03 | Chunk boundaries do not change the limiter's decision, including a CRLF split across chunks; this is what a later proof of `bounded_sse_stream` needs |
| C02 `SseEventSizeLimiter.max_size_eq_and_satAdd_le_of_observe_eq_ok` (prefix form `exists_observe_eq_ok_and_max_size_eq_and_satAdd_le_of_observe_append_eq_ok`; was `sse_observe_bound`) | If `sat(retained + line) ≤ max` holds before and `observe` returns `Ok`, it holds after | T01–T03 | The limiter's memory guarantee: an accepted stream never retains more than `max_size` bytes of the current event |
| C03 `into_result_eq` (renamed to Mathlib style 2026-11-24, was `into_result_consistent`) | `into_result m = (into_response m).map (fun (r, i) => (Ok r, some i)) <\|> (into_error m).map (fun (e, i) => (Err e, i))` | M02, M04, M05 | Routing code may use either form |
| C04 `AuthorizationManager.is_disallowed_metadata_ipv6_eq_of_embedded_ipv4_eq_ok_some` (corollary in `Defs.Net` terms `is_disallowed_metadata_ipv6_of_ipv4Disallowed`; was `ipv6_embedding_no_bypass`) | `embedded_ipv4 a = some v → is_disallowed_metadata_ipv6 a = is_disallowed_metadata_ipv4 v` | A01–A03 | No SSRF bypass by writing a blocked IPv4 address in IPv4-mapped, compatible, NAT64 or 6to4 form |
| C05 `is_standard_method_of_is_standard_notification` (renamed to Mathlib style 2026-11-24, was `notification_is_standard_method`) | `is_standard_notification m → is_standard_method m` | T05, T06 | The allow-lists are consistent |

### 16.5 Measured and not taken

Each was measured in the pilot (Section 14). None gets a function record, a specification or a proof, and none is reachable from a Phase 2 start point, so none needs an `exclude` entry. The "Unblocked by" column records what would bring each back in a later phase. The rule of Section 2.3 applies: re-adding one needs a requirement change and a measured translation run.

| Function | Blocker with the pinned toolchain | Unblocked by |
|---|---|---|
| `requires_base64`, `encode_header_value`, `decode_header_value`, `extract_scope_from_header`, `normalize_host`, `normalize_authority` (only in the first combined run, through `normalize_host`), `quality_is_acceptable`, `host_is_allowed`, `origin_is_allowed`, `validate_tool_name` | B2 (extended): `str` pattern APIs (`contains`, `starts_with`, `ends_with`, `strip_prefix`/`strip_suffix`, `trim_matches`, `split_once`, `find`) end in "Unimplemented" at `core/str/pattern.rs:99` | Aeneas support for `str::pattern`, or Lean models of the pattern methods for `char`/`&str` patterns |
| `is_tchar` | B17: Aeneas "Failure Unexpected" on `char` pattern matching | Aeneas fix |
| `ProtocolVersion::{has_initialize, known_up_to}`, `ResultType::is_complete` | B14: `Cow<'static, str>` deref: "new value doesn't have the same type as its destination" | Aeneas fix |
| `integral_f64_to_i64`, `NumberSchema::with_range` | B15: `f64` constants and comparisons ("Improperly typed constant value", "Invalid inputs for binop") | Aeneas float support |
| `json_rpc_body_preview`, `StringSchema::with_length` | B4: returning a `&'static str` literal ("no bottoms in the value") | Aeneas fix |
| `CreateMessageRequestParams::validate` | B21: "Continue to outer loops are not supported yet" | Aeneas fix |
| `JsonRpcMessageCodec::{max_length, new_with_max_length}` | B18: the struct holds `PhantomData<fn() -> T>` ("Arrow types are not supported yet") | Aeneas fix |
| `LocalSessionWorker::next_http_request_id` | B18: the worker type holds `dyn` trait objects | Aeneas fix |
| `EventId::from_str` | B20: the `_::from_str` path did not resolve, which stopped the first combined run; the `{impl FromStr for EventId}` form was not tried | Retry with the impl-first pattern |
| `AddressClass::of` | B16: the enum constructor `IpAddr::V4` passed as a function value causes a name clash in the generated code | Aeneas fix; then A01–A03 are its lemmas |
| `MetadataAddressResolver::is_allowed` | B7: the parameter is named `class`, a Lean keyword; translated, but the Lean build fails | Aeneas `main` fixes B7 (#1306, release `nightly-2026.11.22-2e3d448`) |
| `CompletionInfo::{new, with_all_values}` | B19: `format!` reaches the Aeneas library axiom `core.fmt.Formatter` through `Display for usize`; the CI axiom audit rejects it (as for Phase 1's derived `Debug` impls) | An Aeneas `fmt` model without the axiom |
| `ExponentialBackoff::retry` | B19: the trait has a `Debug` supertrait, so the instance pulls in a derived `Debug` impl and `core.fmt.Formatter` | As above |
| `FixedInterval::retry`, `NeverRetry::retry` | Not measured: only tried with a pattern Charon rejects (B20). Same trait, so B19 is expected, not shown | Measure with the impl-first pattern |

**Phase 2 blocker register** (continues Section 9's numbering; each was measured in the Section 14 pilot; B2, B4 and B7 recur from Phase 1):

| ID | Blocker | Message or symptom |
|---|---|---|
| B14 | `Cow<'static, str>` deref | Aeneas: "Assertion failed: new value doesn't have the same type as its destination" |
| B15 | `f64` constants and comparisons | Aeneas: "Improperly typed constant value"; "Invalid inputs for binop" |
| B16 | Enum constructor passed as a function value | Aeneas: "Name clash detected" on `core.net.ip_addr.IpAddr.V4` |
| B17 | `char` pattern match in `is_tchar` | Aeneas: uncaught `Failure Unexpected` |
| B18 | Struct with `PhantomData<fn() -> T>` or `dyn` trait fields | Aeneas: "Arrow types are not supported yet"; "Dynamic trait types are not supported yet" |
| B19 | `format!` or a `Debug` supertrait reaches `core.fmt.Formatter` | Translates and compiles, but depends on an Aeneas library axiom that the CI axiom audit rejects |
| B20 | Charon `start_from` naming | An unresolvable path is fatal ("Code failed to compile"); impl patterns only as the first path element; `_` does not match trait-impl methods |
| B21 | `continue` to an outer loop | Aeneas: "Continue to outer loops are not supported yet" |

## 17. Source behaviour that the Phase 2 specifications must capture

Section 3's meaning of a spec applies unchanged: `f x ⦃ r => P r ⦄` says that `f x` terminates without panicking and its result satisfies `P`. Each spec covers every result, not only success. Notes for the S24/S25 drafters follow; the spec owner decides.

**M01–M05 (generic messages).** `JsonRpcMessage<Req, Resp, Not>` is generic. The specs are stated for all type parameters and need no premise. `serde_json::Value` appears only inside `ErrorData` and is never inspected (an opaque type, Section 18).

**M06 (integer parsing).** `Defs.parseI64` is written from Rust's documented grammar for `i64::from_str` (`core::num`, radix 10): an optional single `+` or `-`, then at least one ASCII digit, and nothing else. Leading zeros are allowed. `"+"`, `"-"`, `""`, whitespace and non-ASCII digits are rejected. Values outside `[-2^63, 2^63 - 1]` are rejected. The model of `i64::from_str` in `trusted/` is a separate definition; a proved law (`Proofs/External/IntParse.lean`) states that it equals `Defs.parseI64` (after S24; until then the laws are about the model only, human decision 2026-11-23). The differential test once planned against `std` was dropped (Section 18, amendment).

**M07 (correlation).** Derived `PartialEq` on `NumberOrString` compares `Arc<str>` by contents (the `Arc` model's equality is value equality). The code is asymmetric, and the spec must state it (no comment or test says whether this is intended): `Number 1` matches `String "1"`, but `String "1"` does not match `Number 1`.

**T01–T03 (SSE limiter).**
- All additions saturate at `usize::MAX`. `Defs.Sse` uses `min (a + b) Usize.max` on `Nat`, so no premise is needed and no overflow failure is possible.
- `observe` loops with `for &byte in chunk`, which the translation turns into a slice iterator loop (`observe_loop`). The spec is about the whole call, through the fold in `Defs`.
- On `Err`, `self` keeps the state reached at the failing byte. In particular, when a CR byte makes `finish_line` fail, `previous_was_cr` stays `false`.
- After an LF that follows a CR, the `continue` branch makes no limit check, and an empty chunk makes none either. C02 needs the bound as a premise for these reasons, and the initial state of `new(max)` (both sizes 0) satisfies it.

**T05/T06 (method lists).** The two lists in `Defs.Methods` are the union of the method names of the official MCP schemas of the five protocol versions the SDK knows (`ProtocolVersion::KNOWN_VERSIONS`: `2024-11-05` to `2026-07-28`; human decision H6, 2026-11-24), not the Rust code. The `2026-07-28` schema alone lacks `initialize` and `ping`, so it cannot be the only source. They cover the core protocol only; extension methods (for example rmcp's Tasks extension `tasks/update`, `notifications/tasks`) are out of their scope by design, and coverage claims for T05/T06 say "core protocol". If they differ from the code on a core method, the S24 reviewers report a finding to the spec owner (Section 22, "Bugs found"). The specs must not be bent to match the code silently: the six core names the code omits are named one by one in `Defs.Methods.codeOmits`, the T05/T06 statements say "in the core list and not in `codeOmits`", and the gap is recorded as a bug (H7).

**T07/T08 (ports).** The comparison is exact byte equality, so `"HTTP"` → `none`. Callers lowercase the scheme first, and that is their obligation, not part of this theorem. `Exact p` with an explicit port ignores the scheme.

**A01–A03 (addresses).**
- The specs are stated on octet and segment lists, with `Defs.Net.inPrefix` defined from first principles, not with the `std` predicates.
- The `std` predicates are models (Section 18), so each theorem rests on the models matching `core::net` at the pinned nightly. The differential tests planned for this were dropped (Section 18, amendment).
- `::` and `::1` are excluded from the IPv4-compatible case of A01 (they fall through to A03's loopback/unspecified clauses).
- `::0.0.0.2` embeds `0.0.0.2`, which A02 rejects through `0/8`.
- The 6to4 case takes segments `b`, `c`, not `g`, `h`.

## 18. External models for Phase 2 (trusted-base delta)

The human decision of 2026-11-23 stands: **no `axiom` in `trusted/`**. Each new external is a Lean definition, `structure` or `opaque` constant with the generated name and signature, its Rust source cited by file and line, and its stated exceptions in its docstring (Section 4, "Rules"). The S21 translation PR adds them as temporary `opaque` placeholders (each `Result` type needs an `Inhabited` instance). They add no axiom, but they assert nothing about the function, the situation Section 4 forbids for finished models. Proofs that do not call them (M08, T01–T03) are unaffected. S26/S27 replace each placeholder with an exact model before any proof that calls it starts, and no placeholder survives S27.

**Amendment (human decision 2026-11-23, S26/S27):** the differential tests of this section (stage 3) were dropped. The models' fidelity rests on the cited `core`/`alloc` source of the pinned nightly, read by two independent reviewers, and on the proved laws (stage 6); unrecorded scratch comparisons against `rustc` found no mismatch but are not reproducible evidence. The IPv4 models are therefore not tested exhaustively; S32 proves A01–A03 through the model laws (`Proofs/External/Net.lean`), which characterise every predicate on all inputs.

| Group | Externals (generated names) | Model | Evidence |
|---|---|---|---|
| Strings and `Arc` | `Str.Insts.CoreCmpPartialEqStr.eq`, `alloc.string.String.Insts.CoreOpsDerefDerefStr.deref`, `alloc.sync.Arc` (type), `Arc…Deref.deref`, `Arc…PartialEq.eq` | Byte-list equality; `String` deref is the identity on bytes; `Arc` is a structure holding its value; deref is projection; equality is value equality | Laws in `Proofs/External/String.lean`; existing Phase 1 string tests |
| `Option`/`Result`/slices | `Option.or_else`, `Option…PartialEq.eq`, `Result.ok`, `Slice.first`, `Slice.strip_suffix`, `Slice…PartialEqArray.eq`, `Array…SlicePattern.as_slice`, `RangeInclusive.contains`, `core.mem.maybe_uninit.MaybeUninit` (type) | The `core` definitions, transcribed | Laws in `Proofs/External/Option.lean` (Option, Result) and `Proofs/External/Std.lean` (slices, ranges) |
| Integer parsing | `core.str.Str.parse`, `I64.Insts.CoreStrTraitsFromStrParseIntError.from_str`, `core.num.error.ParseIntError` (type) | `parse` dispatches to the `FromStr` instance; `from_str` is Rust's grammar (Section 17, M06), with `ParseIntError` as a structure of its `IntErrorKind` | Differential test against `i64::from_str` over a corpus (signs, empty, `+`/`-` alone, leading zeros, both bounds and one past each, non-ASCII digits, whitespace) plus 10^6 random strings over `[+\-0-9a ]` |
| IP addresses | `core.net.ip_addr.Ipv4Addr`, `Ipv6Addr` (types); `Ipv4Addr::{octets, is_private, is_loopback, is_link_local, is_broadcast, is_unspecified, is_multicast}`, `From<u32> for Ipv4Addr`; `Ipv6Addr::{segments, is_loopback, is_unspecified, is_multicast}` | Structures over `Array U8 4` and `Array U16 8`; every predicate is transcribed from `library/core/src/net/ip_addr.rs` of the pinned nightly; `from` is big-endian | IPv4: **exhaustive** test of all 2^32 addresses for every predicate, `octets` and `from`. IPv6: every listed prefix boundary plus 10^6 random addresses. Harness (new design; the Phase 1 harness compares lines from an interpreted Lean run, which cannot cover 2^32 × 9 results): a Cargo program on the pinned nightly and a **compiled** Lean executable in a separate Lake project under `formal/trusted/evidence/differential/net/`, outside `formal/lakefile.toml` so the guard's five libraries are untouched. The Lake project takes the model sources by path. Each side streams one digest per function (count + hash over all results), and the digests are compared; a mismatch is located by bisection. S27 measures the runtime first; if it exceeds a few hours, it falls back to an exhaustive Lean proof that each model equals its `Defs.Net` definition plus a sampled differential test |
| Opaque values | `serde_json.value.Value` (type) | `opaque` type: targets only move values | — |

Total: 26 functions and 6 types, exactly the externals the pilot's template adds for the final 25 (the rejected `CompletionInfo` functions would have added `alloc.fmt.format` and `core.hint.must_use`; they are not needed).

**Native-code axioms.** The 30 `toStr` side conditions of the string literals in T05–T08 are the class accepted in Section 4 (human decision 2026-11-22). Each has a kernel proof, and an Aeneas fix would remove them. S29 adds them to `formal/trusted/native-axioms.lock` (with module and statement hash) once a spec constant depends on them. Human decision H2 accepts them; the alternative is to drop T05–T08 and C05 and swap in reserves (T07/T08 own 2 of the 30).

**What Phase 2 adds to the trusted base:** the widened configuration (Section 15), the Charon settings above, the models of this table, 30 native-code axioms, and the statements in `formal/specs/` for the Phase 2 `Defs` and `Specs`. It adds **no translation patch** to translated code, and no axiom to `trusted/`.

## 19. Linkage: showing "no Rust modification" mechanically

Phase 1's record type `linkage: ORIGINAL` means "pinned source, no patch touches it" (Section 6). Patch 01 does touch `model.rs` (it adds `pub mod request_state_wire;`) and will stay until the refactor lands upstream. So for Phase 2, `ORIGINAL` is made checkable, not argued:

- **New script** `scripts/check-original-linkage.sh` (S22). It first checks that the committed `crates/rmcp/src` is the pinned upstream tree (its git tree id, `4efe696a…` at `7caec76`) and that the working tree has no change under `crates/`; it then copies the repository's tracked files into its own guarded scratch directory (the translate script's work directory inside it goes through `scripts/llbc-dir-guard.sh`), writes a temporary `[package.metadata.charon]` holding the Phase 2 start points, `hide_marker_traits = true`, `exclude = ["serde", "serde_core"]`, and every `opaque` entry except the two Phase 1 function entries `rmcp::model::request_state_wire::prim` and `rmcp::model::request_state::_::now_ms` (that is: the Phase 1 crate entries `zeroize`, `base64`, `hmac`, `sha2`, `thiserror`, `chrono` and `serde_json`, plus the Phase 2 entries; the two function entries are left out because no Phase 2 start point reaches them). This is exactly the setting the pilot measured (Phase 1 start points are left out because they would be unresolvable paths upstream, which B20 makes fatal). It then runs Charon and Aeneas with the translate script's configuration. It then checks that every blank-line-separated block of that output's `Funs.lean`, `Types.lean` and two External templates (each block at most one declaration; every `Source:` path under `crates/rmcp/src/`, `/rustc/` or the cargo registry) occurs in the committed file, after normalising only the `Source: '…', lines …` docstring field, and reports each block as DIFFERS (same name, other text) or MISSING. Part (a), before that, pins the committed source to upstream `7caec76`: the `crates/rmcp/src` tree id, a digest of every other tracked file under `crates/` plus the root `Cargo.toml`, and a digest of `crates/rmcp/Cargo.toml` without its Charon table; the working tree must be clean there and in `formal/translation/`.
- **CI.** `aeneas-translation.yml` runs it after the stale-translation check, on the same paths.
- **Record.** The check shows that the Phase 2 translation does not depend on any translation patch, and that the source is upstream; it compares `Funs.lean`, `Types.lean` and the two External templates block by block. It cannot see a patch that changes the body of an `opaque` SDK item reached by a Phase 2 target (only the signature is translated); such a patch makes the affected records `patch-NN` by rule; the script enforces the precondition: the SDK-side `opaque` list must be exactly the type `AuthorizationManager` (no body), nothing of the SDK may be excluded, and no unmodified-source External template may cite `crates/rmcp/src`. It also fails if a declaration present only in the committed (patched) translation could shadow a name used in a Phase 2 block (Lean resolves names against the enclosing namespaces). Not pinned by the check: dependency resolution beyond `PINNED_DEPS` (workspace members outside `crates/` take part; both sides share it, and the stale-translation check requires a clean tree). A Phase 2 record may say `linkage: ORIGINAL` only while this check passes. If an upstream change or a new patch ever makes it fail, the affected records become `patch-NN` and the D10 count reports them as "proved with a translation patch", as Phase 1 does.

**Amendment (2026-11-24, translation patch 03; lead decision on the human decision of targets R09–R15).** `serde_core` moved from `exclude` to `opaque` in `crates/rmcp/Cargo.toml`, so the temporary table the script writes now has `exclude = ["serde"]`, and the script requires exactly that. It also requires the non-`rmcp::` entries of `opaque` (the external crates) to equal a reviewed constant list `EXTERNAL_OPAQUE` in the script, exactly and in order: the Phase 1 crates `zeroize`, `base64`, `hmac`, `sha2`, `thiserror`, `chrono`, `serde_json`, then `serde_core`, then the Phase 2 crates (Section 15); the change against the earlier setting is the single entry `["serde_core"]`. Checked 2026-11-24 on a scratch clone commit of the working tree (`git diff HEAD` applied, the untracked patch 03 and the git-ignored External templates copied, `.aeneas` symlinked, hooks disabled): exit 0; negative test with `serde_core` removed from `opaque`: exit 1. The other statements of this section are unchanged.

**Amendment (2026-11-25, translation patch 04; human decisions 2026-11-25: targets K01–K20, hunks H1–H9; reviewed and signed off by the spec owner 2026-11-25).** Of the twenty skills targets of `crates/rmcp/src/model/skill.rs`, 13 are ORIGINAL (K01–K04, K08–K12, K17–K20 translate from the unmodified source) and 7 need translation patch 04 (K05–K07, K13–K16). `scripts/check-original-linkage.sh` therefore also drops, from the temporary Charon table, the seven skills `start_from` entries of the patch-04 targets (`rmcp::model::skill::_::from_bytes`, `…::_::verify`, `…::sha256_digest`, `…::_::validate`, `…::skill_name_from_uri`, `…::is_sha256_digest`, `…::validate_skills`; it fails if one of them is missing from `crates/rmcp/Cargo.toml`) and the `opaque` entry `rmcp::model::skill::prim` (the module patch 04 adds); the SDK-side opaque rule is unchanged. In the linkage run (`RMCP_TARGET_SET=phase2`) `scripts/aeneas-translate.sh` checks only the ORIGINAL targets and, new, requires each of its `PATCH04_TARGETS` (the seven targets and the private helpers `is_valid_skill_name`, `manifest_resource_key`, `normalize_percent_encoding` of K13) to be **absent** from the unpatched `Funs.lean`: a patch-04 target translated from the unmodified source is reached from an ORIGINAL start point, so the patch-04 lists disagree with the call graph and the ORIGINAL comparison would skip it. Checked 2026-11-25 on a scratch clone of `b363a8a` with the working tree committed (scratch commit `b3e26c4`; untracked patch 04, `Proofs/External/Skill.lean` and `Defs/Skill.lean` and the git-ignored External templates copied, `.aeneas` symlinked): exit 0, 38 ORIGINAL targets defined, blocks identical up to `Source:` (`Funs.lean` 60/60, `Types.lean` 40/40, External templates 34/34 and 10/10); negative test (scratch commit `a847d99`, the ORIGINAL target `model.skill.Skill.name` added to `PATCH04_TARGETS`): exit 1, "patch-04 target model.skill.Skill.name is translated from the unmodified source" (`formal/trusted/evidence/README.md`, "Linkage of the skills targets"). The other statements of this section are unchanged.

Pilot result: all 35 `Funs.lean` definitions (the 25 targets and their helpers) and all 22 `Types.lean` blocks of the upstream-only run are identical to the patched run (Section 14).

**Tests (human decision H3).** M06/M07 are `pub(crate)` and T01–T08, A01–A03 are private, so their unit tests would have to live in their modules. M01–M05 and M08–M14 are `pub`, but an integration test under `crates/rmcp/tests/` is also an SDK `*.rs` file. Either way, new Rust tests would change the SDK sources. Phase 2 therefore relies on:
- the existing upstream tests, mapped per target at S34 (for example the nine `bounded_sse_stream_*` tests for T01–T03, `test_standard_notification_check` for T05/T06, the allowed-origin port tests in `tower.rs` such as `explicit_port_parses_as_exact`, and the metadata-URL tests in `auth.rs` such as `metadata_url_checks_bracketed_ipv6_literals`, which reach A02/A03 only indirectly);
- the differential programs of Section 18 (**dropped**, human decision 2026-11-23; for the M06 and A01–A03 boundary cases of Section 22 the proved model laws and the target theorems take their place; S34 records that no executable test exercises them, or the owner asks for patch 02).

If the owner wants boundary tests beyond those, they go into a **test-only** translation patch `02-phase2-tests.patch`: only `#[cfg(test)]` code, which the translated `--lib` build does not compile. The linkage check runs on the unpatched source, so patch 02 cannot affect any `ORIGINAL` claim. `patched-tests.yml` runs them.

## 20. Phase 2 layout additions

Same conventions as Section 5 (**NEW**, **GEN**, **UPDATE**; `Sxx` = step of Section 21). One spec file per Rust source file, mirroring the Rust module path, as in Phase 1.

```
crates/rmcp/Cargo.toml                          UPDATE S21   Phase 2 start_from/opaque (Section 15)
scripts/aeneas-translate.sh                     UPDATE S21   FEATURE_ARGS; Phase 2 target list
docs/WORKFLOW_AND_PR_GUIDE.md, docs/AI_PR_REVIEW_QUESTIONS.md   UPDATE S21   configuration text, feature flags, procedure commands
formal/specs/Specs/Model/RequestState{,Wire}.lean   UPDATE S21   module docstrings only: widened configuration
scripts/check-original-linkage.sh               NEW    S22   Section 19
.github/workflows/aeneas-translation.yml        UPDATE S22   runs the linkage check
.github/workflows/patched-tests.yml             UPDATE S21   widened --features
formal/
  README.md                                     UPDATE S21, S37   configuration, macOS note, trusted base
  docs/STATUS.md                                UPDATE S20, S37   Phase 2 records, results
  docs/board.yaml                               UPDATE S20   tasks S20–S37
  docs/functions/M01.yaml … M14.yaml, T01.yaml … T08.yaml, A01.yaml … A03.yaml   NEW S20
  trusted/native-axioms.lock                    UPDATE S29   +30 toStr entries (H2)
  trusted/Rmcp/TypesExternal.lean               UPDATE S21 (placeholders), S26–S27 (models)
  trusted/Rmcp/FunsExternal.lean                UPDATE S21 (placeholders), S26–S27 (models)
  trusted/evidence/README.md                    UPDATE S26–S27, S34 (upstream-test map)
  trusted/evidence/differential/net/            NEW    S27   exhaustive IPv4, sampled IPv6 (not built by lake)
  trusted/evidence/differential/intparse/       NEW    S27   i64::from_str corpus + random
  trusted/patches/02-phase2-tests.patch         NEW    S34   only if H3 = yes; #[cfg(test)] only
  specs/
    Defs/JsonRpc.lean                           NEW    S24   message shapes, M-specs helpers
    Defs/IntParse.lean                          NEW    S24   Rust i64 grammar (M06)
    Defs/Methods.lean                           NEW    S24   MCP method lists, union of 5 versions (T05/T06; H6)
    Defs/Tower.lean                             NEW    S24   URI schemes and default ports (T07/T08)
    Defs/Bytes.lean                             NEW    S24   UTF-8 bytes of a string (shared helper)
    Defs/Sse.lean                               NEW    S25   limiter state, step, finishLine, observe
    Defs/Net.lean                               NEW    S25   octets, segments, prefixes (A01–A03)
    Specs/Model.lean                            NEW    S28   M01–M07, M09–M14, C03 (model.rs)
    Specs/Model/Task.lean                       NEW    S28   M08
    Specs/Transport/Common/ClientSideSse.lean   NEW    S31   T01–T03, C01, C02
    Specs/Transport/AsyncRw.lean                NEW    S29   T04–T06, C05
    Specs/Transport/StreamableHttpServer/Tower.lean   NEW S29   T07, T08
    Specs/Transport/Auth.lean                   NEW    S32   A01–A03, C04
    Specs/External.lean                         UPDATE S26–S27   Theorems.External.* for the new model laws
    Defs.lean, Specs.lean                       UPDATE S24–S33   import the new modules (lead)
  translation/Rmcp/Types.lean, Funs.lean        GEN    S21   regenerated; Phase 1 blocks unchanged
  proofs/Proofs/
    Model/JsonRpcMessage.lean (M01–M05, C03), Model/NumberOrString.lean (M06, M07),
    Model/Task.lean (M08), Model/SamplingContent.lean (M09–M12), Model/Reference.lean (M13, M14)
    Transport/ClientSideSse.lean (T01–T03, C01, C02), Transport/AsyncRw.lean (T04–T06, C05),
    Transport/Tower.lean (T07, T08), Transport/Auth.lean (A01–A03, C04)
    External/Net.lean, External/IntParse.lean, External/Option.lean   NEW S26–S27   model laws
    External/String.lean, External/Std.lean     UPDATE S26   laws of the new string/std models
  proofs/Proofs.lean                            UPDATE S26–S33   imports the new modules (lead)
docs/WORKFLOW_AND_PR_GUIDE.md, STYLE_GUIDE.md, REVIEWER_GUIDE.md, AI_PR_REVIEW_QUESTIONS.md   UPDATE S20
```

**Amendment (human decision 2026-11-24): public and internal specifications.** `formal/specs/` now holds only the public rmcp API (functions `pub` in upstream rmcp: M01–M05, M08–M14, the Section 16.1 joint lemmas and C03), with `formal/specs/README.md` as the one-page index. The other spec files above moved, with their statements and `#print axioms` checks byte-identical (module docstrings gained summary tables), to `formal/proofs/Proofs/Internal/<Rust path>.lean` (M06/M07 `pub(crate)` in `Internal/Model.lean`; `Internal/Model/{RequestState,RequestStateWire}.lean`; `Internal/Transport/{Common/ClientSideSse,AsyncRw,StreamableHttpServer/Tower,Auth}.lean`; the model laws in `Internal/External.lean`), and the definitions used only by them (`Defs/{Wire,CodecState,RequestState,Sse,Net,Methods,Tower}.lean`) to `formal/proofs/Proofs/Defs/` (`Wire` and `CodecState` moved back to `formal/specs/Defs/` for the public `request_state.rs` statements) (Lean names unchanged). `scripts/lean_guard.py` allows `#guard_msgs` in `proofs/Proofs/Internal/` too.

The `formal/lakefile.toml` libraries and roots do not change: new modules are imported from the existing roots `Defs.lean`, `Proofs.lean` and `Specs.lean` (the 2026-11-24 amendment above extended `scripts/lean-guard.sh sources` to accept `#guard_msgs` in `proofs/Proofs/Internal/`). Theorem names follow Section 5 and the committed Phase 1 spec files, `Theorems.<last module segment>.<Type>.<function>` (as in `Theorems.request_state.RequestStateCodec.open_at`). So `rmcp.model.JsonRpcMessage.into_request_spec` in `Proofs` is restated as `Theorems.model.JsonRpcMessage.into_request` in `Specs/Model.lean` with its `#guard_msgs` axiom check; likewise `Theorems.task.TaskStatus.is_terminal`, `Theorems.client_side_sse.SseEventSizeLimiter.observe`, `Theorems.async_rw.is_standard_method`, `Theorems.tower.AllowedPort.matches` and `Theorems.auth.AuthorizationManager.embedded_ipv4`. Model laws are restated as `Theorems.External.<name>` in `Specs/External.lean` (since the 2026-11-24 amendment: `formal/proofs/Proofs/Internal/External.lean`), as in Phase 1. The composition theorems are restated under their Section 16.4 names (`SseEventSizeLimiter.observe_append`, …), with their C-IDs in the docstrings, at the end of their spec files.

## 21. Phase 2 process, steps and gates

The process is Section 8's, unchanged:
1. **Phase A, once:** translation and its review (S21–S23, S26–S27).
2. **Phase B, per target:** spec draft → at least two independent `mcp-review` runs → human sign-off → proof by a worker who did not draft the spec → restated theorem with `#guard_msgs`, pipelined in call-graph batches.
3. **Phase C:** refinement, after everything is proved, with statements frozen; deferred, Section 25.

The agent stack and its rules are Section 10's. The `mcp-cycle` skill runs each step through implement → review → fix → re-review.

### Batches

| Batch | Targets | Specs | Proofs | Needs |
|---|---|---|---|---|
| 1 | M01–M05, M08–M14, C03 | S24 | S28 | S21; models of S26 (Option, `Arc`, `String` deref, `Slice.first`) |
| 2 | T04–T08, C05 | S24 | S29 | S21; S26 (`str` eq, `strip_suffix`, `as_slice`, `or_else`, `Option` eq); H2 |
| 3 | M06, M07 | S24 | S30 | S27 (integer parsing), batch 1 |
| 4 | T01–T03, C01, C02 | S25 | S31 | S21 (no external model needed: the limiter uses only Aeneas library items: `saturating_add`, the slice iterator and the `Try` instances) |
| 5 | A01–A03, C04 | S25 | S32 | S26 (`RangeInclusive.contains`, array equality), S27 (`core::net` models) |
| 6 | C01–C05 cross-checks, final restatement | — | S33 | batches 1–5 |

### Steps

Days are working days of a two-week sprint, relative to S20. Dependencies govern acceptance.

| Step | Day | Depends on | Files | Owner — acceptance |
|---|---|---|---|---|
| S20 | D1 | — | `STATUS.md`, `board.yaml`, `functions/{M,T,A}*.yaml`, the four `docs/` guides | Lead + human — 25 records (template of Section 6, `linkage: ORIGINAL` pending S22); owner and budget named; H1–H5 decided; guides updated for Section 20's paths and the linkage check |
| S21 | D1 | S20 (H1) | `crates/rmcp/Cargo.toml`, `scripts/aeneas-translate.sh`, `patched-tests.yml`, `formal/translation/**`, `formal/trusted/Rmcp/*External.lean`, `formal/README.md`, `docs/WORKFLOW_AND_PR_GUIDE.md`, `docs/AI_PR_REVIEW_QUESTIONS.md`, the module docstrings of `formal/specs/Specs/Model/RequestState{,Wire}.lean`; added at S21 by human decisions: `scripts/lean_guard.py`, `scripts/lean-guard.sh` and the trusted `formal/trusted/translation-pins.txt` (pinned exception for the generated T06 line), `formal/proofs/Proofs/External/Std.lean` (`ok` qualified), the Phase 2 records, `formal/docs/STATUS.md` and this plan's Sections 5, 15 and 21 | Extraction — translation regenerated; script fails on a missing or duplicated Phase 2 target; every Phase 1 block byte-identical (diff shown in the PR); new externals added as `opaque` placeholders (no axiom); all three CI workflows green; `lake build` and every `lean-guard.sh` check pass |
| S22 | D1–2 | S21 | `scripts/check-original-linkage.sh`, `aeneas-translation.yml`; also `scripts/aeneas-translate.sh`, `scripts/apply-patches.sh` (the two switches), `formal/README.md`, this plan's Sections 19 and 25, the Phase 2 records, `STATUS.md`, `board.yaml` | Extraction — the check passes on the S22 commit; it fails (1) at part (a) on a committed change under `crates/` (or a manifest change outside the Charon table), and (2) at part (b) on a seeded translation patch that changes a Phase 2 body, with the translation regenerated |
| S23 | D2 | S21, S22 | review notes | Reviewers (≥ 2) + spec owner — Charon settings, the opaque `AuthorizationManager` type, the widened configuration and the placeholders reviewed and signed off |
| S24 | D2–3 | S20 | `Defs/JsonRpc.lean`, `Defs/IntParse.lean`, `Defs/Methods.lean`, `Defs/Tower.lean`, `Defs/Bytes.lean`, `formal/specs/Drafts/` | `mcp-spec` + ≥ 2 `mcp-review` + spec owner — M01–M14, T04–T08, C03, C05 and the Section 16.1 joint lemmas statements signed off |
| S25 | D2–4 | S20 | `Defs/Sse.lean`, `Defs/Net.lean`, `formal/specs/Drafts/` | Same — T01–T03, A01–A03, C01, C02, C04 signed off |
| S26 | D3–4 | S21 | `FunsExternal.lean`, `TypesExternal.lean` (strings, `Arc`, Option, Result, slices), `Proofs/External/{String,Std,Option}.lean`, `Specs/External.lean`, `evidence/README.md` | Extraction + reviewers + spec owner — models are definitions; laws proved; signed off |
| S27 | D3–5 | S21, S24 | Same files (`core::net`, integer parsing), `Proofs/External/{Net,IntParse}.lean` | Extraction + reviewers + spec owner — models and laws reviewed by ≥ 2 agents and signed off; laws proved; the `parseI64` law after S24 (human decisions 2026-11-23: the differential tests were dropped, Section 18 amendment) |
| S28 | D3–5 | S24, S26 | batch 1 proof files; `Specs/Model.lean`, `Specs/Model/Task.lean` | Lean — M01–M05, M08–M14, C03 and the Section 16.1 joint lemmas checked and restated |
| S29 | D4–6 | S24, S26, H2 | batch 2 proof files; `Specs/Transport/AsyncRw.lean`, `…/Tower.lean`; `native-axioms.lock` | Lean — T04–T08, C05 checked; 30 lock entries; `#guard_msgs` lists show them |
| S30 | D5–6 | S27, S28 | `Model/NumberOrString.lean`; `Specs/Model.lean` | Lean — M06, M07 checked |
| S31 | D4–8 | S21, S25 | `Transport/ClientSideSse.lean`; `Specs/…/ClientSideSse.lean` | Lean — T01–T03, C01, C02 checked (the loop invariant is the main proof effort of Phase 2) |
| S32 | D6–8 | S25, S26, S27 | `Transport/Auth.lean`; `Specs/Transport/Auth.lean` | Lean — A01–A03, C04 checked |
| S33 | D8–9 | S28–S32 | spec files | Lean + review — every Phase 2 theorem restated; each spec file's module docstring states the widened configuration |
| S34 | D2–9 | S21 | upstream-test map in `evidence/README.md`; patch 02 only if H3 | Review — each Section 22 boundary case is covered by an upstream test, a differential test or (H3) patch 02, and the tests pass |
| S35 | D9 | S22, S29 | throwaway branch | Lead — new CI checks shown to fail once: the linkage check (a change under `crates/`, and a seeded translation patch), a missing target, a removed native-lock entry |
| S36 | D9–10 | S35 | fresh clone | Review — install, translate, linkage check, `lake build`, `lean-guard.sh` all pass (S18 analog) |
| S37 | D10 | board state; no success required | `STATUS.md`, `formal/README.md` | Lead + human owner — Phase 2 results (Section 25), trusted-base delta, bugs found, open items, cost; Phase 3 scope (Section 23) |

S37 is mandatory even if every other step fails. Phase 1's S17 (first CI run on GitHub) should be done in the same pull request as S21, since S21 is the first PR that changes all three workflows' inputs.

**Notes for S31/S32 from the S25 reviews (2026-11-24; candidates, not signed-off statements).**
S31: the agreement `∀ cap ≥ 1, Defs.Sse.observe cap (init m) h = historyOutcome cap m h` (checked
only on finite cases in `Defs/Sse.lean`) is needed by a later "the stream rejects an oversize event"
lemma; a scratch proof of T03 rewrote with an auto-generated `match_….eq_…` equation, which trips
`linter.auxLemma` under `warningAsError`, so the prover needs another route. S32: a normal-form
lemma `ipv4Disallowed (ofBigEndianDigits 256 [a,b,c,d]) = decide (<octet conditions of A02>)` for
octets `< 256` keeps the A02 proof within about 2M heartbeats (one small `omega` fact per range; one
`omega` over the 11-way disjunction timed out). The C04 corollary needs only
`ipv4Disallowed w = true → w < 2^32` and evaluation of `embeddedIpv4` on the four forms. A01 and A03
were carried by a segment-level characterisation of `embeddedIpv4`, a segment normal form of
`ipv6DisallowedPrefixes.any`, mask lemmas (`s &&& 0xffc0 = 0xfe80 ↔ s / 64 = 1018`,
`s &&& 0xfe00 = 0xfc00 ↔ s / 512 = 126`) and `is_loopback`/`is_unspecified` rewritten to
`ok (decide …)`. Traps seen in the scratch proofs: `simp_all [UScalar.eq_equiv]` loops on
hypotheses `0#16#uscalar = s` (use `simp … at *`, then `omega`), `0#16#uscalar` needs a lemma
`(UScalar.mk (BitVec.ofNat 16 k)).val = k % 65536`, and in A01's 6to4 branch `step*` produced a
proof the kernel rejected, while a single `step` worked.

### Gates

- **G1 (end of D2):** S21 merged with all three CI workflows green and S22 passing; owner and budget named.
  - **Fallback:** a target that turns out not to translate, compile or link `ORIGINAL` in the real repository run is dropped, recorded in Section 16.5 with its blocker, and replaced from the measured reserve (Section 14). Before it enters, the reserve function gets the same `#print axioms` check as the 25.
  - No path leaves a target `BLOCKED` by translation, and no fallback patches Rust code.
- **G2 (D5):** S23, S26 and S27 signed off; batches 1–2 measured. Re-estimate S31/S32 from actual effort, and keep every target visible.
- **G3 (D10):** `STATUS.md` written. Report how many Phase 2 targets are verified on the original source (the goal is 25), proved with a translation patch (expected 0) or open.

The mandatory result mirrors Section 8:
- translation of all 25 (already demonstrated by the pilot);
- the not-taken functions reported with their blockers;
- whatever proofs are actually checked;
- an accurate status for the rest.

All 25 verified, plus C01–C05, is the goal.

### Human decisions

| ID | Decision | Recommendation |
|---|---|---|
| H1 | **Accepted 2026-11-23 (human).** One translated configuration with the widened feature list (Section 15), instead of a second configuration | Adopt: the Phase 1 output is byte-identical under it, and one configuration keeps one CI path |
| H2 | **Accepted 2026-11-23 (human).** Accept 30 more `toStr` native-code axioms (same class, locked, kernel-provable) for T05–T08 | Accept; alternative: replace T05–T08 with reserves (T08 calls T07), and C05 goes too |
| H3 | **Accepted 2026-11-23 (human)**, as recommended; the differential programs were later dropped (2026-11-23, Section 18 amendment). Boundary tests: existing upstream tests plus differential programs only, or also a test-only patch 02. A test-only patch is a process exception: VERIFICATION.md §4 defines translation patches as behaviour-preserving edits that make an item translate | Upstream + differential first; patch 02 only for a case S34 finds uncovered; if created, the exception is recorded in `formal/docs/STATUS.md`, "Documents", as a further deviation from VERIFICATION.md (which is kept verbatim) |
| H4 | **Accepted 2026-11-23 (human).** The `opaque` entry for the `AuthorizationManager` type (Section 15) | Accept: the type is not used by A01–A03 and does not appear in the generated files (S23 correction 2026-11-24: the reason is a Charon/hax failure on the `dyn` async-trait fields, see Section 15) |
| H5 | **Open (TBD, human 2026-11-23).** Project owner and budget for Phase 2 (and the open Phase 1 S01). The Phase 2 spec owner is Hoang Le Truong (named 2026-11-23) | — |
| H6 | **Decided 2026-11-24 (human, S24).** Source of the T05/T06 method lists in `Defs.Methods`: the union of the method names in the official `schema.ts` of the five versions in `ProtocolVersion::KNOWN_VERSIONS` (22 requests, 12 notifications), because the `2026-07-28` schema alone lacks `initialize` and `ping` | Union of the five versions (adopted). **Amended 2026-11-24 (human):** `notifications/elicitation/response` (rmcp core block, in no core schema) is out of scope too. Earlier amendment: the lists cover the core protocol only; extension schemas are kept separate. rmcp's Tasks-extension methods `tasks/update` and `notifications/tasks` are outside the core union by design, not a bug. The upstream schema versions are pinned (commit and sha256 in `Defs.Methods`); Lean regression checks pin the list contents, and the derivation from the schemas is reproduced by the command recorded in `Defs.Methods`. If Tasks-extension support is verified later, its method list is generated separately from the extension schema, with capability-dependent handling checked. Coverage claims say "core protocol" and never "full MCP" |
| H7 | **Decided 2026-11-24 (human, S24).** The Rust lists of T05/T06 (`async_rw.rs` 396–433) lack six names of the core union: `tasks/get`, `tasks/result`, `tasks/cancel`, `tasks/list`, `notifications/tasks/status`, `notifications/elicitation/complete` (`Defs.Methods.codeOmits`). The T05/T06 statements take the code form "in the core list and not in `codeOmits`", with the six names listed one by one; the gap is recorded in `STATUS.md`, "Bugs found" | Code form, bug recorded (adopted) |
| H8 | **Decided 2026-11-24 (human, S25).** A01–A03 address lists: (1) blocking the whole local-use NAT64 prefix `64:ff9b:1::/48` (RFC 8215), including addresses that carry a public IPv4 address, is intended conservative behaviour, not a bug; (2) `240.0.0.0/4` (reserved, except the broadcast address) is neither in the plan's A02 list nor blocked by rmcp: recorded as a bug in `STATUS.md`; (3) other special-purpose ranges outside the plan's lists (documentation, benchmarking and similar ranges, and `::ffff:0:0:0/96`, the IPv4-translated format of RFC 2765, obsoleted by RFC 6145 and not in the IANA registry) are a scope note: the plan's lists are the scope. The A01–A03 statements describe the code in every case | Adopted as decided |

## 22. Phase 2 acceptance and boundary cases

Section 7's per-step rule applies: each step's commit message and `STATUS.md` record the exact commands and exit status, the Aeneas tag, the commit translated, any model changes, the AI drafters and reviewers (tool and model), and the human decision. A failure is recorded in `STATUS.md`, "Open items", with a minimal reproducer, and the task stays `BLOCKED`.

Boundary cases each proof must cover, and the tests (upstream, differential or H3) must exercise:

| ID | Cases |
|---|---|
| M01–M05 | each of the four message kinds; `Error` with `id = None` |
| M06/M07 | `"0"`, `"+0"`, `"-0"`, `"007"`, `""`, `"+"`, `"-"`, `" 1"`, `"1 "`, `"9223372036854775807"`, `"9223372036854775808"`, `"-9223372036854775808"`, `"-9223372036854775809"`, `"١"` (Arabic-Indic digit); `Number 1` vs `String "1"` both ways; equal and unequal strings |
| M08 | each of the five statuses |
| M09–M12 | `Single`; `Multiple []`; `Multiple [x]`; `Multiple [x, y]` |
| M13/M14 | both variants |
| T01/T02 | sum exactly at, one above and saturating past `max`; empty line; comment line; non-comment line |
| T03/C01/C02 | LF, CR, CRLF endings; CRLF split across chunks; comment that resets nothing; blank line resetting; event exactly at the limit; oversize split across many chunks; empty chunk; error at a CR byte (state afterwards) |
| T04 | empty; `"\r"`; `"a\r"`; `"a\r\r"`; `"a"` |
| T05/T06/C05 | every listed name; prefix and suffix of a name; case variant; `notifications/unknown`; empty |
| T07/T08 | `"http"`, `"https"`, `"HTTP"`, `"ftp"`; `Any`/`Unspecified`; `Exact 443` with `None` and `https`; `Exact 80` with `Some 8080` |
| A01 | `::ffff:a.b.c.d`; `64:ff9b::a.b.c.d`; `::a.b.c.d`; `::`; `::1`; `2002:abcd:ef01::`; `64:ff9b:1::1` (local-use NAT64: not embedded) |
| A02 | first and last address of each listed range, and the addresses just outside each; a public address |
| A03/C04 | each listed prefix boundary; an embedded blocked IPv4 in each of the four forms; a public IPv6 address |

**Bugs found.** Any disagreement between an independent specification and the code is recorded in `STATUS.md`, "Bugs found", and reported to the owner. It is never resolved by weakening the specification (Section 8, "What sends work back"). Candidates the drafters must check: whether the core MCP method lists (union of the five known versions, H6) include methods missing from T05/T06 (found at S24: `tasks/get`, `tasks/result`, `tasks/cancel`, `tasks/list`, `notifications/tasks/status`, `notifications/elicitation/complete`, recorded as a bug, H7; names in no core schema, such as `tasks/update`, `notifications/tasks` and `notifications/elicitation/response`, are out of scope by H6); and whether `64:ff9b:1::/48` addresses that embed a public IPv4 address should be allowed (decided at S25: blocking is intended, H8; `240.0.0.0/4` recorded as a bug).

## 23. Reuse map: what Phase 2 unlocks

Each Phase 2 theorem is a lemma for a larger function. That is how this phase prepares the next.

| Phase 3 candidate | Uses | Blocked today by | Becomes possible when |
|---|---|---|---|
| `origin_is_allowed`, `parse_allowed_origin` (DNS-rebinding Origin check) | T07, T08 | B2 (`trim_matches`, `strip_suffix`, seen in the pilot); `http::Uri` parsing | `str` pattern support or models; URI parsing kept opaque, as in `verification/host_origin/` |
| `host_is_allowed` | (string equality model of S26) | B2 (`trim_matches`) | As above |
| `AddressClass::of`, `MetadataAddressResolver::{is_allowed, allows_url}` (SSRF guard) | A01–A03, C04 | B16 (constructor as function value), B7 (`class`) | Aeneas bump to `nightly-2026.11.22-2e3d448` or later (fixes B7) plus a B16 fix |
| `is_allowed_metadata_url` | A02, A03 | `url::Url` and `Host` (opaque crate); B16 through `AddressClass::of` (`auth.rs:1426`); B2 (`trim_end_matches`, `ends_with`) | A `Url::host` model, the B16 fix and `str` pattern support |
| `should_ignore_notification`, `try_parse_with_compatibility` | T04–T06 | `serde_json::Value` inspection | A `Value` model (partial: `get("id")`) |
| `bounded_sse_stream` / `BoundedSseByteStream::poll_next` | T01–T03, C01, C02 | `async`/`Pin` | Out of the Aeneas scope; the C01/C02 statements are the contract a wrapper argument cites |
| Client response routing (`service/client.rs`) | M01–M07, C03 | `async`, channels | The pure classification core can be split out by a translation patch, if allowed then |
| Task manager terminal-state transitions | M08 | `tokio` | As above |
| `CreateMessageRequestParams::validate` (sampling) | M09–M12 | B21 (`continue` to an outer loop) | Aeneas fix |
| `CompletionInfo::{new, with_all_values}`, `ExponentialBackoff::retry` | — | B19 (`Formatter` axiom) | An Aeneas `fmt` model without the axiom |

The Phase 2 external models (`core::net`, integer parsing, `str` and `Arc` equality, `Option` combinators) are reusable for every later phase. They are candidates for upstreaming to the Aeneas library (Section 12), which would remove them from this project's trusted base.

**Phase 3 entry criterion.** A measured pilot (as in Section 14) on the then-current Aeneas release, re-run against this table, before any Phase 3 target is committed to.

## 24. Phase 2 risks

| Risk | Effect | Mitigation |
|---|---|---|
| The widened features change the Phase 1 translation in a future upstream commit | Phase 1 proofs break | The stale-translation CI shows the diff; every Phase 1 block is checked byte-identical in S21; the pilot measured no change at `7caec76` |
| A `_` glob matches a new upstream method | Extra or different target translated | Target-presence check in `aeneas-translate.sh` (Section 15, rule 3) |
| A model of `core::net` or `i64::from_str` does not match the pinned `std` | A02/A03/M06 theorems describe the model, not Rust | Proved laws of each model (S26/S27) checked against the cited `rust-src`; two reviews and human sign-off per model; the differential tests planned here were dropped (Section 18 amendment) |
| T03's loop proof is harder than estimated | S31 slips | Batch 4 has no external dependency and can start at S25; C01 can be proved on `Defs` first; G2 re-estimates |
| 30 more native-code axioms | Larger trusted base | Same accepted class, locked, kernel-provable; H2 alternative |
| Build size of the widened configuration (about 17 GB locally) | Slower CI, runner disk limits | CI caches `.aeneas/` only, as today; S21 measures the CI time and disk use on the GitHub runner |
| The macOS bundle's Nix `libiconv` path | Local runs abort | `DYLD_FALLBACK_LIBRARY_PATH=/usr/lib` (Section 14), documented in `formal/README.md` |
| Patch 01 changes `model.rs` line numbers in docstrings | Cosmetic mismatch with upstream line numbers | The linkage check normalises `Source:` lines; records cite `7caec76` line numbers |

## 25. Phase 2 results template and deferred items

To be filled in only with actual results, in a Phase 2 results section of `formal/docs/STATUS.md`:

> At upstream SDK commit `7caec762799bece6fba38e4298b8ca7db8bac12c`, unmodified (the translation of these functions does not depend on any translation patch and `crates/rmcp/src` is the pinned upstream tree; checked by `scripts/check-original-linkage.sh`), translated for `x86_64-unknown-linux-gnu` with `--no-default-features --features request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth` (and the Charon settings in `crates/rmcp/Cargo.toml`), the following existing SDK functions are verified against the Aeneas translation (`nightly-2026.08.20-5d08da4`): `[list of M/T/A IDs and symbols]`, together with the composition theorems `[C list]`. These results rest on the trusted base listed in `formal/README.md` and `STATUS.md`: Charon, Aeneas and Lean; the translated configuration; the standard-library, `core::net` and integer-parsing models in `formal/trusted/` (definitions, structures and `opaque` constants; no trusted axiom); the `toStr` native-code axioms in `formal/trusted/native-axioms.lock`; the statements in `formal/specs/`; and the functions not taken (Section 16.5). They do not establish the correctness of the functions that call these targets, of URL or HTTP parsing, of `async` code, or of DNS resolution. Functions not listed are open for the reasons given below.

D10 count for Phase 2: verified on original code `[n]`, proved with a translation patch `[n]`, open `[n]`.

**Deferred beyond Phase 2:**
- Phase C proof refinement for both phases (Section 12, first item).
- The Aeneas bump. It would fix B6/B7 and may fix others; it unlocks `MetadataAddressResolver::is_allowed` and is the Phase 3 entry pilot (Section 23).
- The Phase 3 candidates of Section 23.
- Upstreaming the Phase 2 models.
- Specifications for the translatable non-targets of Phase 1 (`open`, `open_with`, `new`, `try_new`).

## 26. Amendment (2026-11-24): Aeneas upgrade to `nightly-2026.11.24-fb44cb4`

**Amendment (human decision 2026-11-24, "full migration"; reviewed and re-signed by the spec owner 2026-11-24).** This section amends earlier sections without rewriting them; where they
disagree, this section is current. Details and counts: `formal/docs/STATUS.md`, "Aeneas upgrade
(2026-11-24)".

- **Toolchain (amends Sections 5 and 15, the pilot environment of Section 14 stays as
  recorded).** Aeneas `nightly-2026.11.24-fb44cb4` (commit `fb44cb40`), Charon `0.1.324`, Lean
  and Mathlib `v4.36.0`, Rust `nightly-2026-09-17`; until 2026-11-24 Aeneas
  `nightly-2026.08.20-5d08da4`, Charon `0.1.235`, Lean `4.31.0`, Rust `nightly-2026-06-01`. The
  build gate is `lake build --wfail` again (Section 5): the new Aeneas library has none of the
  four `sorry` warnings, and the build-log allowlist is empty (lead decision N10).
- **Native-code axioms (amends Sections 4 and 18, H2).** The new Aeneas `toStr` proves the
  length side condition of a string literal in the kernel, so the translation declares no
  native-code axiom; `formal/trusted/native-axioms.lock` is empty (lead decision N5; it held 35
  entries, 5 Phase 1 and 30 Phase 2). The rules of Section 4 for native-code axioms stay in force
  for any that appears again. Every `#print axioms` list is now within `propext`,
  `Classical.choice`, `Quot.sound`. One-time exception (human decision 2026-11-24): lists may gain
  only these three standard axioms in this upgrade; all changed lists are re-signed as one batch.
  The shrink-only rule applies again afterwards.
- **Aeneas library axiom `core.fmt.Formatter` (amends B19, Sections 16.5 and 24).** In the new
  library `core.fmt.Formatter` is an `opaque` type, not an axiom. Whether the B19 items become
  translatable is a separate question for after the migration (lead decision N15).
- **External models (amends Section 18).** Four models moved into the Aeneas library and were
  removed from `formal/trusted/Rmcp/FunsExternal.lean`: `core::borrow::Borrow` (blanket
  `borrow`), `Option::ok_or`, `Result::map_err` and `Vec::is_empty` (lead decision N8). The model
  of `RangeInclusive::contains` follows `nightly-2026-09-17` (an exhausted range has end bound
  `Excluded(start)`, so it contains nothing; human decision 2026-11-24; one fresh review of the
  model and laws: model exact, one blocking finding (a dropped restatement) fixed); all 39 model citations are to be re-checked against the `nightly-2026-09-17`
  `rust-src` (lead decision N9, model review).
- **Statements.** Forced restatements only (human decision 2026-11-24, name-only batch
  re-sign): the `Borrow` rename, the arity of `Vec.is_empty_spec`, the `Slice.from` constructor
  form in `hash_eq`, and their restatements; the `RangeInclusive` laws `contains_u8_spec` and
  `contains_eq_match_le` (and restatements) restated exactly for the new model (exhausted branch
  `item < start`); `new_contains_u8_spec` unchanged. Also named explicitly: the `Defs` change
  `Defs.CodecState.KeyTable` (allocator `Global` → `alloc.alloc.Global`, name-only) and the helper
  lemma `Proofs.ClientSideSse.from_residual_eq` (translated instance renamed to
  `CoreOpsTry_traitFromResidualResult`; same Rust impl, same body).
- **Translation and CI (amends Sections 5, 15 and 19).** Charon `0.1.324` no longer records its
  options in the LLBC; the check of the Charon settings runs on the translated items instead
  (lead decision N1); both cargo build-script output layouts are accepted (N2). Two exact
  `lean-guard.sh sources` exemptions (human decision 2026-11-24): the Aeneas phrase "this code is
  generated from a macro invocation at:" in generated docstrings, and one
  `set_option linter.dupNamespace false in` on `zeroize.Zeroize.Blanket.zeroize`; the
  macro-site paths are checked against the allowed sources (N13). The kernel replay of the axiom
  audit uses `Lean.Kernel.Environment.replay` (N11). The project Lean files are modules (N12;
  header and visibility only, no statement change).
- **Deferred (amends Section 25).** "The Aeneas bump" is done by this amendment; re-adding
  excluded items (for example `new_with_keyring`, R15) happens after the
  migration as separate steps (N15). Patch 03 (R09–R12) is parked until the upgrade is accepted.
  (Update 2026-11-24: after the upgrade commit the parked patch 03 is superseded by patch 03 v2,
  targets R09–R15 including `new_with_keyring`; see the Section 2.3 and Section 9 amendments.)
