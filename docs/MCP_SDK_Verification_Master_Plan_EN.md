# MCP SDK Verification — Master Plan

Date: 22 November 2026. This is the single current plan.

**Current state:** three extraction runs were done before this plan, with all outputs outside the repository in `/tmp`: run 1 compiled the repository's own `crates/rmcp` (except its `e04`/`e04c` attempts, which used scratch sources), and runs 2 and 3 used scratch copies (Section 8, "Pilot results").
- **Run 1, unchanged source:** most targets cannot be extracted.
- **Run 2, private adapter shims:** all targets extract, but HMAC, `str::split` and Base64 stay hidden behind ad-hoc private modules.
- **Run 3, public `request_state_wire` API (this plan):** the codec is refactored onto fifteen public, pure functions plus four opaque primitives. Tokens and 162 `open` results are byte-identical to the original code. The pilot's claim that the existing request-state tests, `clippy` and `rustfmt` passed is not recorded (no log survives); S04a re-ran them on the refactor in the working tree (not yet landed): 265 library tests pass, including 39 in `request_state.rs` and 28 in `request_state_wire.rs`, and `clippy` and `rustfmt` are clean (the S04a evidence (git history at 01bdc9b)).
- **Excluded functions:** every function that cannot be translated with the pinned toolchain is excluded from translation and from the project's claims (Section 2.3). After that, the Aeneas log has no error, and the generated Lean compiles with 0 errors and no `sorry` anywhere, with no hand edit.
- **Process:** the plan follows the Aeneas verification process guide, [`VERIFICATION.md`](VERIFICATION.md): one `formal/` folder split into `trusted/`, `specs/`, `translation/` and `proofs/`; Charon settings in `Cargo.toml`; Aeneas pinned by one release tag; three CI workflows.
- **Status (2026-11-23):** all 25 targets and the composition theorems are specified, signed off by the spec owner and proved; steps S05–S16, S18 and S19 are accepted (`formal/docs/board.yaml`; results in `formal/docs/STATUS.md`, "Results"). The results are about upstream `origin/main` `7caec76` plus translation patch `formal/trusted/patches/01-request-state-wire.patch` (D2 fallback, human decision 2026-11-23): every SDK `*.rs` file is byte-identical to `7caec76`, the refactor and its tests exist only in the patched copy, and every target's linkage is `patch-01` (proved on upstream `7caec76` plus translation patch 01) (D10: 0 verified on original code, 25 proved with translation patch 01, 0 open). The translation (committed at `46cfb02`) is reproduced byte for byte through the patch path, so no proof changed.
- **Waiting on the human owner:** naming the project owner and budget (S01); (the D2 fallback is in use: patch 01 was reviewed by two agents and signed off by the human on 2026-11-23, S04a); running the three CI workflows on GitHub for the first time (needs a pull request), and S17 (all three exist; none has run on GitHub yet). See `formal/docs/STATUS.md`, "Open items".

## Fixed requirements

| Requirement | Section |
|---|---|
| Verify existing SDK functions, and the new public `request_state_wire` functions they are built on (since the D2 fallback, 2026-11-23: in the patched copy); no replacement of the `hmac`, `sha2` or `base64` crates | 1, 2 |
| Every target is a concrete function in the pinned source, with an independent specification | 2, 3 |
| New functions are public, foundational (pure byte/integer logic, no I/O) and reusable outside the codec | 2 |
| Every target translates with the pinned toolchain; no target may depend on an unresolved blocker | 2, 9 |
| Functions that cannot be translated with the pinned toolchain are excluded from the project, not deferred | 2.3, 9 |
| Layout and process of `VERIFICATION.md`: a single `formal/` folder, one translated configuration, spec files restating each theorem (as `theorem Theorems.…`) with `#print axioms` checks | 5, 9 |
| Aeneas pinned by one GitHub release tag in `formal/lakefile.toml`, read by both scripts | 5 |
| Patches, axioms and spec statements are reviewed by multiple independent agents, then signed off by a human | 4, 6, 10 |
| CI checks that the translation is current, the Lean project builds, and the patched copy passes the crate's tests | 5, 8 |
| Process: crate-wide translation and review once, then a per-function spec → review → sign-off → proof pipeline, then proof refinement once at the end | 8 |
| Two-week sprint with measured feasibility gates | 8 |
| Operational Claude agent stack | 10 |
| Ordered steps with exact files, timing and ownership | 8 |
| Explicit status and acceptance evidence per function | 6, 7 |
| Stated security scope, trusted base and reproducibility | 1, 4, 11 |
| AI may draft specifications; a named human spec owner accepts every one | 6, 10 |

**Requirement changes (22 November 2026, by the user).**
1. The plan previously verified only existing functions, with no new runtime code. The user extended it to new public functions that Aeneas supports, and asked for every unresolvable blocker to be removed from the plan (third and fourth rows).
2. The user asked for every function that cannot resolve its blockers to be removed from the project (fifth row). Under the process guide, "removed" means listed in Charon's `exclude` setting (Section 2.3).
3. The user adopted `VERIFICATION.md` as the process. It replaces the earlier crate-local `crates/rmcp/lean/` project with `Specs`/`Theorems`/`Proofs`/`Checks` libraries, the hand-written extraction command, `verification/manifest.yaml` and `verification/assumptions.yaml` (rows six to nine).

Change a requirement only when the user changes it, or a documented technical incompatibility forces an explicit decision.

**Governing guides.** `VERIFICATION.md` defines the process: layout, scripts, Charon settings, patches, axioms, spec files and CI. This plan defines scope, targets, steps and status for the request-state work. Four further guides under `docs/` define how work is written, submitted and reviewed. If any two disagree, fix whichever is wrong in the same PR.

| Guide | Covers |
|---|---|
| [`VERIFICATION.md`](VERIFICATION.md) | The Aeneas process: `formal/` layout, install and translate scripts, Charon settings, patches, external axioms, spec files, proofs, CI |
| [`WORKFLOW_AND_PR_GUIDE.md`](WORKFLOW_AND_PR_GUIDE.md) | Generated files, translation, status records, PR format, trust rules, AI contributions |
| [`STYLE_GUIDE.md`](STYLE_GUIDE.md) | Lean headers, tactics, library layering, `Defs` definitions, spec file layout |
| [`REVIEWER_GUIDE.md`](REVIEWER_GUIDE.md) | Review criteria and steps, including review of AI-drafted specifications |
| [`AI_PR_REVIEW_QUESTIONS.md`](AI_PR_REVIEW_QUESTIONS.md) | Checklist and report format for AI-assisted PR review |

> The four `docs/` guides were aligned with this plan on 22 November 2026 (`formal/` layout, the Lean build gate, spec files with `#guard_msgs`, `STATUS.md`, independent agent reviews, phases A–C). `docs/VERIFICATION.md` itself is still to be committed (S02).

---

## 1. Source baseline and scope

- **Repository:** https://github.com/truonghoangle/rust-sdk (the user's fork of the Rust MCP SDK).
- **Base commit:** `0e2396f73a88617141b31f645de6f1171ed5f993`. The current `main` (`7caec76`) adds only `verification/host_origin/`, and `crates/rmcp/src/model/request_state.rs` is byte-identical between the two (SHA-256 `41e69cad94869be4b93120f3cd39a10fad4a3730585240b712c2ada1b311b416`).
- **Pinned commit:** the fork commit that lands the `request_state_wire` refactor (S04a). Record it in `formal/docs/STATUS.md`. **D2 fallback (human decision 2026-11-23).** The refactor was not landed; the pinned commit is upstream `origin/main` `7caec76`, every SDK `*.rs` file is byte-identical to it, and the refactor is translation patch 01 (Section 9, "Refactor"). From then on, the translation CI (Section 5) guarantees that the committed translation matches the Rust source in the repository (since the D2 fallback: that source with patch 01 applied), so no separate hash check is needed.
- **Target files** (since the D2 fallback, in the patched copy `.llbc/work/` only; line numbers refer to it):
  - `crates/rmcp/src/model/request_state_wire.rs` (new, public; created by patch 01)
  - `crates/rmcp/src/model/request_state.rs` (refactored onto it by patch 01)
- **Feature:** both files compile only with the `request-state` feature (`crates/rmcp/Cargo.toml`, `request-state = ["dep:hmac", "dep:zeroize", "base64"]`).
- **Translated configuration (single target):** `--target x86_64-unknown-linux-gnu --no-default-features --features request-state --lib`, fixed in `scripts/aeneas-translate.sh`, with overflow checks and debug assertions pinned on: every cargo call (also through Charon) gets `--config profile.dev.overflow-checks=true --config profile.dev.debug-assertions=true`, so arithmetic panics on overflow, which is what Aeneas models as failure. Nothing else may change the build: the script refuses environment variables that change how cargo or rustc build (`RUSTFLAGS`, `RUSTC*`, `RUSTDOC*`, `CHARON_*`, `AENEAS_*`, every `CARGO_*` outside a short allowlist, and every `RUSTUP_*` except `RUSTUP_TOOLCHAIN` and `RUSTUP_HOME`), a selected `rustc` whose `rustc -vV` is not the pinned nightly, a `.cargo/config` or `.cargo/config.toml` in the source, the work copy or any ancestor of it, and `[profile]`, `[patch]`, `[replace]` or `cargo-features` in the workspace or `crates/rmcp` manifest; it runs cargo with an isolated `CARGO_HOME`, requires every dependency of `rmcp` in this configuration to come from crates.io at the pinned versions (Section 4), and requires the build script to be `crates/rmcp/build.rs` with the sha256 pinned in the script (`BUILD_RS_SHA256`) and an empty output (exact lists: `formal/README.md`, "Translated configuration"). **The proofs hold only for this configuration.** It is stated in `formal/README.md` and in the module docstring of each spec file. The pilot ran on macOS aarch64 without `--target`; S03 records whether the output differs.

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

The public types `KidError`, `Version`, `FrameError`, `Rs1Parts` and `Rs2Parts` are `#[non_exhaustive]`. The public constants are `VERSION_V1/V2`, `DOMAIN_V1/V2`, `EXPIRY_LEN`, `MIN_KEY_LENGTH`, `MAX_KID_LEN`, `MAX_ENCODED_KID_LEN` and `TAG_LEN`. The codec takes its constants from this module, so each value is defined in exactly one place, with four recorded exceptions, each with its own reason: (1) the codec keeps `VERSION_V1`/`VERSION_V2` as `&str` constants (`"rs1"`, `"rs2"`) next to `wire::VERSION_V1`/`V2: &[u8]`, because deriving them with a `const` `str::from_utf8(wire::VERSION_V1)` initializer would give Charon a global whose body can panic (the `Result` has to be unwrapped; not tried on this tree); (2) the "255" inside the E04 message constant `KID_TOO_LONG_MSG` stays a literal, because E04 (Section 2.2, B4) must keep its `InvalidKeyring` messages as `&'static str` constants with the base text, and a `const` formatter would face the same panicking-global problem; (3) the private alias `MAX_ENCODED_KID_LEN = wire::MAX_ENCODED_KID_LEN` is an alias, not a second literal; (4) `prim::hmac_sha256` returns `[u8; 32]` rather than `[u8; TAG_LEN]`, so that the S08 axioms are stated against a stable signature. The test `codec_constants_agree_with_wire` (and, for (4), tag-length checks on `wire::TAG_LEN`) checks that they agree with the wire constants (the S04a evidence (git history at 01bdc9b), "Deviation from plan §2.1/§9 'defined once'").

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
- `open`, `open_with`, `new` and `try_new` do translate. They stay in the source and in the generated Lean, but are not targets.

## 3. Source behaviour that the specifications must capture

**What a spec means (VERIFICATION.md §6).** Aeneas translates each function into the `Result` monad, where panics, arithmetic overflow and out-of-bounds indexing become failure. A spec `f x ⦃ r => P r ⦄` therefore says that `f x` terminates without panicking and that its result satisfies `P`. Preconditions state when the function is guaranteed not to panic; a weaker precondition is a stronger result.

**W14/E01 — expiry.** `now_ms == expiry` is accepted. A negative nonzero expiry is compared as a signed value like any other. E01 performs no authentication; its theorem is about byte handling only.

**W01 and the seal capacities — arithmetic.** The workspace sets no `overflow-checks`, so debug builds panic on overflow and release builds wrap. Aeneas models overflow as failure, which matches debug builds only; the translation pins `overflow-checks=true` (Section 1). (W15 has no arithmetic: it builds its output with `Vec::new` and `extend_from_slice`, without `with_capacity`.) Every arithmetic theorem (W01, and the `with_capacity` sums in E07/E08) is therefore stated on the domain where no overflow occurs, and that domain is written into the theorem as a precondition. W01 also carries the lemma `b64_len n = (n.div_ceil 3) * 4` on that domain, which ties it to the original definition. Allocation failure is an explicit assumption, not a no-panic claim.

**Lean-model domains (notes for the S05 drafters; the spec owner decides at S05).** Some preconditions are needed only because the Lean model is more general than Rust:
- W06 `component_count` (and through it W08, W09, E09 and E10) needs `s.length < Usize.max` in Lean, stated as fewer than `Usize.max` `.` bytes: its counter `n` starts at 1 and `n + 1` can overflow on a slice of `Usize.max` bytes, which cannot exist in Rust (slices are at most `isize::MAX` bytes). E11 needs no such premise: it calls W08/W09 only on tokens whose first component is `"rs1"` or `"rs2"`, which therefore contain a byte other than `.` (spec-owner decision 2026-11-23, the S05 evidence (git history at 01bdc9b) open question (j)).
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

**Decision (human, 2026-11-23): no axioms in the trusted base.** Every external is a Lean definition (functions) or `structure` (types) with the generated name and signature; what a model cannot compute is an `opaque` constant, which adds no axiom (`#print axioms` does not list it). The four opaque constants are `ExtModel.hmacSha256`, `ExtModel.sipHash13`, `ExtModel.nowMs` and the type `ExtModel.SerdeJsonErrorImpl`. The laws the earlier design stated as axioms (Base64 round trip, `HashMap::get`) are theorems in `formal/proofs/Proofs/External/`. What remains trusted is that each definition describes its Rust function, with the stated exceptions in its docstring (evidence: `formal/trusted/evidence/README.md`).

| Contract | Model | Not established |
|---|---|---|
| **HMAC** (`prim.hmac_sha256`, `prim.hmac_sha256_verify`) | `opaque hmacSha256 : List U8 → List U8 → Array U8 32#usize` is the reference function. `def hmac_sha256 k m := ok (hmacSha256 k m)`. `def hmac_sha256_verify k m t := ok (t = hmacSha256 k m)` (as byte lists, so a wrong-length tag is rejected). Both always succeed (HMAC accepts keys of any length). Stated exception: the SHA-256 bit-length counter (`sha2-0.11.1/src/block_api.rs` line 66) overflows (a panic under overflow checks) for a message of at least `2^61 − 64` bytes or a key of at least `2^61` bytes (a long key is hashed by `get_der_key`); not modelled, as it lies outside the size convention of `FunsExternal.lean` (no claim about inputs of at least `2^61` bytes, which cannot exist on `x86_64`, whose address space is at most `2^57` bytes). | Cryptographic security; correctness of the `hmac`/`sha2` crates; constant time |
| **Base64url, no padding** (`prim.b64_encode_into`, `prim.b64_decode`) | `b64 : List U8 → List U8` and `b64Decode : List U8 → Option (List U8)` are **definitions** (RFC 4648 Section 5 alphabet, no padding, strict decoding), matching the `URL_SAFE_NO_PAD` engine: the decoder rejects padding, foreign bytes, length `≡ 1 (mod 4)` and non-canonical trailing bits. `b64_encode_into x out` appends `b64 x` to `out`; `b64_decode x = ok (b64Decode x)`. Theorems (`Proofs/External/Base64.lean`): `b64Decode (b64 x) = some x`; `b64Decode s = some y ↔ b64 y = s`; every output byte is in the URL-safe alphabet (no `.`); `(b64 x).length = (4n + 2) / 3`. Differential check against `base64 0.23.1` (`formal/trusted/evidence/differential/`). | Correctness of the `base64` crate beyond the tested inputs |
| **Standard library** | Value semantics for the operations in the target closure. Provided by the Aeneas library: `Vec::{with_capacity, extend_from_slice, push}`, `to_be_bytes`, `U64.from_be_bytes`, slice ranges, `Slice.to_vec`. Hand-written models, all **definitions**: `str::len`, `str::as_bytes`, `String::{with_capacity, push_str, push, as_bytes, from_utf8}`, `Option::ok_or`, `Result::{is_err, map_err}`, `Zeroizing` deref (identity on the wrapped value). `HashMap` is a structure holding an association list; `HashMap::get` is a definition (first entry with an equal key, no hashing); `RandomState`/`DefaultHasher` are structures with the opaque `sipHash13`. `ok` from a `String` model means "returns, or aborts or panics for memory reasons" (out of memory; amortized growth past `isize::MAX`). | Unlimited memory; hashing behaviour; zeroisation on drop |
| **Clock** (`now_ms`, opaque: reads the system clock) | `ok nowMs` with `opaque nowMs : I64`. Environmental assumption (not modelled): `chrono::Utc::now` panics if the system clock is before 1970 or outside chrono's range. One constant makes every reader of the clock pure, so **no spec statement mentions the functions `rmcp.model.request_state.RequestStateCodec.now_ms`, `…RequestStateCodec.open` or `…RequestStateCodec.open_with`** (review rule; a variable named `now_ms`, such as the time parameter of E01 `open_authenticated_body`, is not covered); `open`/`open_with` are translated but not targets, `seal_with` is excluded. | Two readings differ; clock correctness |
| **Codec state** | For a keyring codec: the key ids are pairwise distinct; every id in `rs1_fallbacks` and the `seal_mode` key id are keys of `keys`; every key is at least 32 bytes; every kid passes E04. The keyring constructors enforce these (`new_with_keyring`, `with_rs1_signing`, `with_rs1_fallback`). A single-key codec is unconstrained: `new_unchecked` and the deprecated `new` accept a key of any length (only `try_new` checks it). Stated as the `Defs` definition `CodecValid` (`Defs/CodecState.lean`), never as an axiom. Each opening statement takes only the clauses it needs: E09 and E11 that every rs1 fallback is a key id (so `keys.get(kid).expect(..)` cannot panic), E09a the same for its arguments, E10 none (its lookup returns an `Option`, and HMAC accepts keys of any length). The round trips may assume `CodecValid`, which implies these (spec-owner decisions 2026-11-23). | Correctness of the constructors (excluded, Section 2.3) |

**Rules for externals and axioms** (VERIFICATION.md §5):
- **No `axiom` in `trusted/`** (human decision 2026-11-23): use definitions, structures, `opaque` constants and hypotheses on the specs; `trusted/axioms.lock` stays empty. Adding an axiom again needs a human decision, a justification docstring, backing Rust tests, a lock line and a consistency model (below).
- **Never leave a bare `axiom f : … → Result T`.** Give an exact model or `ok` of an opaque value, as in the table; a bare `Result` axiom asserts nothing returns, so proofs through it get stuck.
- **Do not axiomatise a function whose Lean type merges distinct Rust types** (for example `size_of`); state the fact as a hypothesis on the spec instead.
- **Pin the dependency versions the models rely on** (in `PINNED_DEPS` of `scripts/aeneas-translate.sh`: `hmac 0.13.0`, `sha2 0.11.1`, `base64 0.23.1`, recorded at S03; `digest 0.11.3`, `zeroize 1.9.2`, `chrono 0.4.45`, `serde_json 1.0.154`, added at S08–S09 because the models cite them). `Cargo.lock` is git-ignored in this repository and never copied into `.llbc/work/`, so the dependencies are resolved afresh on every run. The script runs one `cargo tree` over the whole dependency tree of `rmcp` in the translated configuration (same `--config`, `--target` and feature arguments, normal edges) and fails if any dependency does not come from crates.io (a path, git or other-registry source) or if a pinned crate resolves to a version other than the pinned one.
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
- **Statements:** the definitions in `formal/specs/Defs/` and the statements in `formal/specs/Specs/` say what we mean.
- **Exclusions:** excluded items (Section 2.3) are not verified at all, and neither is anything outside the scope of Section 1.

The proofs and the generated translation do not need to be read: Lean checks the former and CI regenerates the latter. An auditor reads all of `formal/trusted/` and `formal/specs/`.

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

There is one spec file per Rust source file (VERIFICATION.md §7): `Specs/Model/RequestStateWire.lean` and `Specs/Model/RequestState.lean`. Each lists its file's targets in source order. Each statement is restated as a `theorem` in the `Theorems` namespace (as in the curve25519-dalek fork's `ForHumans/Theorems`; human decision 2026-11-23), proved by the spec theorem it restates, so Lean checks the restated type against the proved one. It is followed by the axioms that proof depends on, checked by `#print axioms`:

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
- **Lean project builds** (`lean-build.yml`). Runs when anything under `formal/`, `scripts/lean-guard.sh`, `scripts/lean_guard.py`, `scripts/lean-axiom-audit.lean`, `scripts/aeneas-install.sh` or the workflow itself changes. The build gate (human decision, S03): every `[[lean_lib]]` sets `leanOptions = { warningAsError = true }`, so a plain `lake build` fails on any warning in this project's modules, including `sorry`, and runs every `#guard_msgs` axiom check. `lake build --wfail` is not used: the pinned Aeneas Lean library has four `sorry` warnings (`Aeneas/Std/Slice.lean:363,586`, `Aeneas/Std/StringIter.lean:12,15`) that Lake replays on every build, and `--wfail` fails on them (the S03 evidence (git history at 01bdc9b)). The gate can return to `--wfail` once an Aeneas bump removes them. The workflow has two jobs, because `lake build` elaborates the project, and elaboration runs code that could rewrite files of the runner (a `#eval` rewriting `scripts/lean-guard.sh`, say) before a later step of the same job:
  - Job `build` (`working-directory: formal`): checkout without persisted credentials; a pinned elan binary checked by sha256; `scripts/lean-guard.sh sources` before any Lean code of the project runs; restore of the `formal/.lake/packages` cache (keyed on `formal/lean-toolchain` and `formal/lake-manifest.json`; only this job uses it, and `formal/.lake/build` is never cached); `lake exe cache get`; `lake build` with `pipefail`, output tee'd to `.lake/build.log`; then `.lake/build` and the log packed as one tar file and uploaded as the artifact.
  - Job `check` (`needs: build`): a fresh runner and a fresh checkout, so the scripts come from git and not from job `build`; the pinned elan installed afresh; `sources` again; Mathlib cache and the Aeneas release archive fetched afresh with no cache (`lake exe cache get`, `lake build Aeneas`, which builds nothing of this project), then `aeneas-archive`; then the artifact is downloaded and unpacked with `scripts/lean-guard.sh unpack-build` (only `build/` and `build.log`, no absolute or `..` paths, no links or devices, no existing build); then `build-log` and `axioms`. No Lake command runs after the unpack, and the audit runs no code from the `.olean` files, so no project code runs in this job.

  Because a file can switch `warningAsError` off, hide messages, add declarations without a kernel check or run code during the build, the guard (`scripts/lean-guard.sh`; checks in `scripts/lean_guard.py`, run with `python3 -I`, Python 3.11 or later, and `scripts/lean-axiom-audit.lean`) has these subcommands:
  - `sources`: (1) `formal/lakefile.toml`, parsed as TOML, has exactly the five libraries of "Lean libraries" below with their fixed `srcDir` and roots, each with exactly the keys `name`, `srcDir`, `roots`, `leanOptions` and `leanOptions` exactly `{ warningAsError = true }`; the package has only `name`, `defaultTargets` (including `Defs`, `Proofs`, `Specs`), one `[[require]]` (aeneas) and the libraries; no `formal/lakefile.lean` exists. (2) `formal/lake-manifest.json` lists exactly the ten recorded packages at their recorded commits (`MANIFEST_PACKAGES` in `scripts/lean_guard.py`): Aeneas at `5d08da45a405913bbee6fd544e01debf8154ac9d` with `url`, `inputRev` and `subDir` equal to the lakefile's `git`, `rev` and `subDir`, Mathlib at `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (`v4.31.0`), and the eight packages Mathlib brings in; a PR that bumps the Aeneas rev updates this list. (3) Every hand-written `.lean` file under `formal/` (everything except `.lake/`, `specs/Drafts/` and `translation/`) fails on the whole words `warningAsError`, `sorry`, `sorryAx`, `admit`, `native_decide`, `bv_decide`, `skipKernelTC`, `proofAsSorry`, `implemented_by`, `extern`, `unsafe`, `ofReduceBool`, `ofReduceNat` and `trustCompiler`, on the `native` option of `decide` (`+native`, `-native`, `native :=`), on `set_option linter.<name> false` (in `trusted/` too), and, outside `trusted/`, on `axiom`. It also fails, in `proofs/`, `specs/` and `trusted/` alike, on anything that runs or registers a metaprogram during the build: `#eval`, `#exit`, `run_cmd`, `run_tac`, `run_elab`, `run_meta`, `elab`, `elab_rules`, `initialize`, `builtin_initialize`, `macro`, `macro_rules`, `syntax`, `simproc`, `dsimproc`, `simproc_decl`, `builtin_simproc`, `register_option`, `register_simp_attr`, `declare_syntax_cat`, `addDecl`, `addAndCompile`, `modifyEnv`, `setEnv`, `withOptions`, the metaprogramming types (`IO`, `EIO`, `BaseIO`, `CoreM`, `MetaM`, `TermElabM`, `TacticM`, `CommandElabM`, `MacroM`, `SimpM`, `DelabM`, `CommandElab`, `TermElab`), the namespace `Lean.Elab`, any `debug.` option, and the attributes that register a metaprogram (`command_elab`, `term_elab`, `tactic`, `init`, `builtin_*`, `delab`, `app_delab`, `simproc`, `env_linter`, code actions, `widget_module`). `macro` and `syntax` are banned because a macro can produce any command without writing its keyword; `notation`, `infix`, local instances and attributes such as `simp` are allowed. A proof that needs a custom tactic writes it out inline; a reviewed tactic module with its own rules would be a separate human decision (lead decision 2026-11-22: the ban stays everywhere). The list is defence in depth, not complete (an Aesop rule that runs a tactic definition is not covered), so reviewers check for metaprogramming. The check is textual, so comments and docstrings count. `#guard_msgs` is allowed only in `specs/Specs.lean` and `specs/Specs/`, and there only as a bare `#guard_msgs in` followed, on the same or the next line, by exactly one `#print axioms <name>` that ends the line (no options such as `(drop all)` or `(whitespace := lax)`); written in backticks on both sides (`` `#guard_msgs` ``) it is prose and skipped. This backtick exemption applies only to `#guard_msgs`, not to the banned words. Generated files in `translation/` get the same word, `native` and metaprogramming rules; `#guard_msgs` is banned there, Aeneas's `set_option linter.* false` is allowed, and `axiom` is banned except in the unbuilt `*_Template.lean` files, which are exempt. Symlinks under `formal/` fail.
  - `build-log`: an exact allowlist. The log must contain a `Build completed successfully` line, and every line containing `warning:` or `error:` must be exactly one of the four lines `` warning: Aeneas/Std/Slice.lean:363:4: declaration uses `sorry` ``, `…/Slice.lean:586:8: …`, `…/StringIter.lean:12:4: …` and `…/StringIter.lean:15:4: …`.
  - `axioms` (only after a successful build): fails if `formal/.lake/build/lib/lean` holds anything but modules named `Rmcp`, `Defs`, `Proofs`, `Specs` or below them, or a symlink. It then runs `lean-axiom-audit.lean` with the toolchain's own `lean` (`lean --run`, not `lake env`, which would put `formal/.lake/build/bin` first on `PATH` and `formal/.lake/build/lib` on the shared-library path), with an explicit `LEAN_PATH` (toolchain library, then the manifest's packages, then the project build, so no project `.olean` can shadow `Init`, `Lean`, `Lake` or a package module) and no dynamic-loader variables. The audit imports the roots of the default-target libraries with `loadExts := false`, so no code of an imported module runs, and fails if (a) a project `.olean` is stale: the source hash in its Lake `.trace` file differs from the hash of the current source; (b) the constants declared in project modules that the roots reach reach (one order-independent walk over all of them, through types, values and whole inductive blocks) an axiom other than `propext`, `Classical.choice`, `Quot.sound`, the axioms declared in the `RmcpExternal` roots (`Rmcp.TypesExternal`, `Rmcp.FunsExternal`) and the native-code axioms that are the Aeneas `toStr` side condition of a string literal and are declared in `Rmcp.Types` or `Rmcp.Funs` (nothing else native), which catches `sorryAx` (also when inherited from the Aeneas library or hidden from the build log) and the `<decl>._native.*` axioms (`native_decide`, `decide +native`); or (c) the kernel rejects a project constant when every project constant is replayed (`Lean.Environment.replay`, the check `leanchecker` runs) onto the non-project modules they import, which catches declarations added without a kernel check (for example through `debug.skipKernelTC` set from a metaprogram) and altered `.olean` files; or (d) an `RmcpExternal` root declares a constant in the namespace `rmcp` or adds an alias (`export`), which would take precedence over the names the generated `namespace rmcp` code means (`sources` checks the same textually in `trusted/`). `leanchecker` is not run separately (it uses the same replay). Then (e) the locks, with the audit scope of the human decision of 2026-11-23 (for `axioms.lock`; the lead applied the same rule to `native-axioms.lock`): every trusted axiom (declared in the `RmcpExternal` roots) and every native-code axiom reachable from some constant declared in a `Defs`, `Proofs` or `Specs` module (every constant of such a module counts, including private helpers, instances and auxiliary declarations), transitively through any constant including the generated `Rmcp.Types`/`Rmcp.Funs` definitions (one walk with a single visited set over types, values and whole inductive blocks, independent of the order of the constants; a superset of what `#print axioms` reports), must be in `formal/trusted/axioms.lock` (`lean_guard.py axiom-lock`) or `formal/trusted/native-axioms.lock` (`lean_guard.py native-lock`, also with its module) with the sha256 of its canonical statement; axioms that no such constant depends on are listed for information and need no entry (so importing `Rmcp.Funs` into a proof does not require locking every placeholder external); an entry for a declared but unused axiom is reported as "unused (allowed)", so S08–S09 can lock reviewed models early; an entry for an axiom no longer declared, or with another statement hash, fails. The statement of a declared axiom that is neither locked nor used (none since S08–S09, which replaced the 41 placeholder externals by definitions) is not checked and can change or vanish in any PR, ordinary or forged, without CI failing; review of `trusted/` is the barrier for such axioms. (a)–(d) and the `toStr`-form and module restrictions on native-code axioms cover every project constant regardless of this scope. Only the import closure of the default-target roots is audited, so (d) and (e) cover `Rmcp`/`RmcpExternal` once a `Defs`/`Proofs`/`Specs` module imports `Rmcp.Funs` (S06) or they become default targets (a lakefile change by the lead; unused placeholders no longer block it, evidence S03 D1).
  - `aeneas-archive`: every Lake-fetched Aeneas Lean-library archive matches `formal/trusted/aeneas-bundle.sha256`, and the installed Aeneas build and the archive hold the same regular files with the same bytes (every file except `*.hash` and `*.trace`); a build without an archive fails unless `LEAN_GUARD_AENEAS_FROM_SOURCE=1` marks a build from the pinned sources.
  - `unpack-build TAR`: job `check` only, as above.

  Limits: the `sources` rules are textual, not semantic; only the axioms declared in the `RmcpExternal` roots (`Rmcp.TypesExternal`, `Rmcp.FunsExternal`) are trusted by the audit, so those files still have to be read and reviewed; a module that no root imports is neither built nor audited; unlike `#print axioms`, the audit does not lose axioms on inductive/constructor cycles: it follows types, values and whole inductive blocks with one visited set (an over-approximation). Residual risks of the two-job design (`formal/README.md`, "What CI checks"): (1) the artifact is attacker-controlled data if the build ran malicious code; job `check` replays it in the kernel and audits its axioms, but cannot tell whether it was compiled from these sources, since a build that runs code could upload output of a different (or empty) project, and the only barrier is that the build runs no project code: the metaprogramming bans of `sources`, checked in job `build` before the build, and review (a ban that misses a way to run code is a hole in this barrier, not only in the textual check); (2) `.olean` files are memory images that Lean maps without validating them, so a crafted file could crash the audit or worse (job `check` has read-only repository permissions and no secrets, so the worst outcome is a wrong check result); (3) the Mathlib oleans of job `check` come from Mathlib's cache server and are not checked against a committed digest (open scope question for the human). On the translation side, a fake `rustc` that prints exactly the pinned `rustc -vV` lines is not caught by asking it (`charon-driver` would then not find its `librustc_driver`).
- **Patched copy passes the crate's tests** (`patched-tests.yml`). Same paths as the translation check (including `crates/rmcp/build.rs` and the root `Cargo.toml`). Installs the pinned nightly, runs `scripts/apply-patches.sh`, and runs `cargo test --no-default-features --features request-state --lib` in `.llbc/work/crates/rmcp`. With no patches this is the plain test suite; it becomes evidence for the patches if the D2 fallback is used, which it is since 2026-11-23 (patch 01 carries the refactor's tests, so the run is evidence for patch 01).

## 6. Status model

One vocabulary is used everywhere.

**Task state** (in `formal/docs/board.yaml`): `NOT_STARTED` → `IN_PROGRESS` → `ACCEPTED`, or `BLOCKED` / `DEFERRED`. Only `ACCEPTED` is complete. An accepted blocker report closes the *task of reporting*, never the function's proof.

**Function status** (in `formal/docs/functions/<ID>.yaml`), four independent fields:

| Field | Values |
|---|---|
| `translation` | `NOT_TRIED`, `LLBC_OK` (Charon), `LEAN_OK` (Aeneas output compiles), `BLOCKED` |
| `spec` | `DRAFT`, `REVIEWED` |
| `linkage` | `ORIGINAL` (pinned source, no patch touches it), `patch-NN` (its translation depends on translation patch NN in `formal/trusted/patches/`, e.g. `patch-01`). Since the D2 fallback (2026-11-23) all 25 targets are `patch-01` (patch 01); a target whose proof is about a patched copy is reported as proved with translation patch 01, not verified (D10) |
| `proof` | `OPEN`, `CHECKED` |

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

(The per-step evidence files of S01–S19 were removed from the working tree on 2026-11-23 by human decision; they remain in git history at commit `01bdc9b`, and `formal/docs/STATUS.md` keeps the results. A later step records the same content in its commit message and in `STATUS.md`.)

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
- **Rust checks:** the pilot claimed that `cargo clippy --lib -- -D warnings` was clean in both the normal and the test profile, that nightly `rustfmt` reported no diff, and that 39 request-state tests passed (36 in `request_state.rs`'s `mod tests`, plus 3 in `mrtr.rs` selected by the `request_state` name filter; inferred). None of this is recorded: no log survives, only partial Cargo fingerprints (the pilot record (removed from git history on 2026-11-23), disagreement 5). S04a re-ran the checks on the refactor: 265 library tests pass, including 39 in `request_state.rs` and 28 in `request_state_wire.rs`, and `clippy` (both profiles) and `rustfmt` are clean (the S04a evidence (git history at 01bdc9b)).
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

**Phase C: refinement.** Phase C starts only once every target is `CHECKED` or definitively `OPEN`. It shortens proofs, makes them robust to translation changes and Aeneas upgrades, and factors out shared lemmas. Spec statements and `#guard_msgs` lists must not change during it. It is out of scope for this sprint (Section 12).

### Steps

| Step | Day | Depends on | Files | Owner — acceptance |
|---|---|---|---|---|
| S01 | D1 | — | `formal/docs/STATUS.md`, `board.yaml`, `functions/*.yaml` | Lead — base commit, scope decision (Section 1), named human owners and budget recorded; 25 function records |
| S02 | D1 | S01 | `CLAUDE.md`, `.claude/agents/*.md`, `docs/VERIFICATION.md`, the four `docs/` guides | Lead — roles and edit permissions defined; `CLAUDE.md` points to the guides; the guides describe the `formal/` layout, the Lean build gate (Section 5, CI), spec files with `#guard_msgs` and `STATUS.md` instead of the old layout |
| S03 | D1 | S01 | `formal/lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `formal/README.md`, `formal/trusted/aeneas-bundle.sha256`, `scripts/aeneas-*.sh`, `scripts/apply-patches.sh`, `scripts/lean-guard.sh`, `scripts/lean_guard.py`, `scripts/lean-axiom-audit.lean`, `scripts/llbc-dir-guard.sh`, `crates/rmcp/Cargo.toml`, `.gitignore`, `lean-build.yml` | Extraction — `aeneas-install.sh` installs `nightly-2026.08.20-5d08da4` and is a no-op on rerun; bundle versions match Section 5; the pinned Charon reads `[package.metadata.charon]` (otherwise the script passes the same lists as flags, recorded in the evidence); the empty project builds in CI (B10); `aeneas-translate.sh` fails on a nonzero Aeneas exit, a missing target, any `sorry`, or a dependency version mismatch; output on the fixed Linux target compared with the run-3 output |
| S04 | D1 | S01 | pilot record and S04 evidence (removed 2026-11-23; git history at 01bdc9b) | Extraction — runs 1–3 artifacts (refactor patch, Charon arguments, scripts, logs, token harness) copied from scratch |
| S04a | D1–2 | S03, S04 | `request_state_wire.rs`, `request_state.rs`, `model.rs` (since the D2 fallback, 2026-11-23: `formal/trusted/patches/01-request-state-wire.patch`); `formal/translation/**`; `formal/trusted/Rmcp/*External.lean`; `aeneas-translation.yml`, `patched-tests.yml` | Extraction + reviewer — two PRs, as the workflow guide requires: (1) the refactor, with the checklist of Section 9 passing, landed in the fork and the pinned commit recorded; (2) the translation, where all three CI workflows pass and every target is present in `Funs.lean` with a real body |
| S05 | D2 | S01 | `Defs.lean`, `Defs/Wire.lean`, `Defs/RequestState.lean`, `formal/specs/Drafts/`, `Specs.lean`, `Proofs.lean` | Spec drafter (`mcp-spec` or a person) + independent agent reviewers + spec owner — W01–W15 and E01–E04 statements reviewed by ≥ 2 independent agents, then signed off |
| S06 | D2–4 | S04a, S05 | W01–W06, W12–W15 proof files; `Specs/Model/RequestStateWire.lean` | Lean — W01–W06, W12–W15 checked and restated in the spec file; W01 overflow domain explicit |
| S07 | D3–4 | S06 | E01–E04 proof files; `Specs/Model/RequestState.lean` | Lean — E01–E04 checked using only W theorems |
| S08 | D3–4 | S04a | `formal/trusted/Rmcp/FunsExternal.lean` (model functions, HMAC, Base64), `Proofs/External/Base64.lean`, `Proofs/External/String.lean`, `Proofs/External/Prim.lean`, `formal/specs/Drafts/External.lean` and `Drafts/Staged/External.lean` (shared with S09), `formal/trusted/evidence/README.md`, `formal/trusted/evidence/differential/`, the S08 evidence (git history at 01bdc9b) | Extraction + reviewers + spec owner — `prim` models (definitions, opaque `hmacSha256`; no axiom, decision 2026-11-23) and their statements reviewed by ≥ 2 independent agents, then signed off; Base64 laws proved; RFC 4231 and Base64 vectors pass through `prim` in Rust tests; the differential check passes |
| S09 | D3–4 | S04a | `formal/trusted/Rmcp/FunsExternal.lean` (standard library, `HashMap`, `zeroize`, clock), `TypesExternal.lean`, `Proofs/External/Std.lean`, `formal/specs/Drafts/External.lean` and `Drafts/Staged/External.lean` (shared with S08), `formal/trusted/evidence/README.md`, the S09 evidence (git history at 01bdc9b), the `#guard_msgs` update of `formal/specs/Drafts/Staged/RequestState.lean` | Extraction + reviewers + spec owner — standard-library, `HashMap`, `zeroize` and clock models (definitions and structures; opaque `sipHash13`, `nowMs`, `SerdeJsonErrorImpl`; no axiom) and their statements reviewed by ≥ 2 independent agents, then signed off; the Rust tests named in the evidence pass |
| S10 | D4–5 | S06 | W07–W11 proof files | Lean — W07–W11 checked against `List.splitOn` and the transcript specs |
| S11 | D5–6 | S07, S08, S09, S10 | `SealRs1.lean`, `SealRs2.lean` | Lean — E07/E08 output-format theorems checked on the no-overflow domain |
| S12 | D5 | S05 | `Defs/CodecState.lean` | Spec drafter + reviewers + spec owner — codec-state invariant reviewed against the constructors |
| S13 | D6–8 | S07, S08, S09, S10, S12 | `Rs1FallbacksVerify.lean`, `OpenRs1At.lean`, `OpenRs2At.lean`, `Proofs/External/Iter.lean` (slice-iterator helper) | Lean — E09a, E09, E10 checked with full error order |
| S14 | D8 | S10, S13 | `OpenAt.lean` | Lean — E11 dispatch theorem checked |
| S15 | D8–9 | S11, S13, S14 | `Roundtrip.lean`; end of `Specs/Model/RequestState.lean` | Lean — each round-trip theorem accepted on its own; missing ones listed `OPEN` |
| S16 | D2–9 | S04a onward | `mod tests` in both target files (since the D2 fallback, 2026-11-23: in patch 01) | Review — Section 7 boundary cases and contract test vectors pass under `cargo test --features request-state` |
| S17 | D9 | accepted results | the three workflows | Lead — each CI check shown to fail once on a throwaway branch: a hand edit to `Funs.lean`, a new axiom (`#guard_msgs` diff), a `sorry`, and a failing test on the patched copy |
| S18 | D9–10 | S17 | the S18 evidence (git history at 01bdc9b) | Review — fresh clone: install, translate, `git status` clean, `lake build` and the `scripts/lean-guard.sh` checks pass |
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

### Refactor (replaces the run-2 adapter)

The refactor is a real change to the SDK source, landed in the fork, not a translation patch: it adds public API that the user asked for (Section 1). Translation patches (VERIFICATION.md §4) are reserved for behaviour-preserving workarounds applied only to the copy in `.llbc/work/`; none are planned.

**D2 fallback (human decision 2026-11-23).** The refactor was not landed, so the paragraph above no longer holds: the D2 fallback (Section 8) is in use. The refactor and all its tests (S04a, S16) are `formal/trusted/patches/01-request-state-wire.patch` on upstream `7caec76`, applied only to `.llbc/work/` by `scripts/apply-patches.sh`; the SDK `*.rs` files are byte-identical to `7caec76`, and every target's linkage is `patch-01` (proved on upstream `7caec76` plus translation patch 01). The behaviour argument below is the patch's argument; its link to upstream behaviour is the byte-identity regression tests and the S04a differential check (argued and tested, not proved). Landing the refactor upstream would let the patch be deleted and the targets become `ORIGINAL`.

| Change | Behaviour argument for review |
|---|---|
| New public module `request_state_wire` (Section 2.1) | Pure functions; the only consumer in the SDK is the codec |
| Codec constants come from `wire` | Same values; each is defined once, except the four recorded items of Section 2.1, each with its own reason: the `&str` `VERSION_V1`/`V2` (a `const` `from_utf8` derivation would give Charon a panicking global; not tried on this tree), the "255" in the E04 message (E04 keeps `&'static str` messages with the base text), the `MAX_ENCODED_KID_LEN` alias (an alias, not a literal), and `prim::hmac_sha256` returning `[u8; 32]` rather than `[u8; TAG_LEN]` (a stable signature for the S08 axioms); checked by the test `codec_constants_agree_with_wire` and tag-length checks against `wire::TAG_LEN` (the S04a evidence (git history at 01bdc9b), "Deviation from plan §2.1/§9 'defined once'") |
| `open_at` uses W07 | First `.`-component comparison, as before |
| `open_rs1_at`/`open_rs2_at` use W08/W09 | `None` exactly when the original part checks returned `MalformedFormat`; component equality argued in Section 3 |
| `mac_v1`/`mac_v2` deleted; seal/open use `prim::hmac_sha256(_verify)` on W10/W11 | Same bytes are MACed (Section 3); `verify` still uses `hmac`'s constant-time comparison; errors are returned in the same order |
| `URL_SAFE_NO_PAD` calls replaced by `prim::b64_*` | Same engine and calls; decode errors still map to `InvalidEncoding` |
| `open_authenticated_body` uses W14; `seal_at` uses W15 (`seal_at` itself is excluded, Section 2.3; W15 stays a public target with the `frame_roundtrip` lemma) | Same framing and expiry comparison; W12 is bit-identical to `i64::from_be_bytes` |
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

**Open item for the S04a translation PR (part 2): axiom audit of the translation (human decision 2026-11-22; the S04a evidence (git history at 01bdc9b)).** The first S04a translation failed `scripts/lean-guard.sh axioms` (with `Rmcp` as a default target) through the derived `Debug` impls: their `Debug::fmt` bodies depend on the Aeneas library axiom `Aeneas.Std.core.fmt.Formatter` and on `_native.decide.ax_*` axioms that Aeneas's `toStr` leaves for every string literal (`by decide +native`). Decided: (1) the seven derived `Debug` impls (`KidError`, `Version`, `FrameError`, `Rs1Parts`, `Rs2Parts`, `SealMode`, `SealOptions`) are excluded in the Charon settings of `crates/rmcp/Cargo.toml` (shown in the block above); no target uses them, and the regenerated translation keeps all 25 targets; (2) native-code axioms are a separately classified trust item, as in the SPQR project: the audit accepts one only if its statement is the `toStr` side condition `decide ("…".toByteArray.size ≤ Aeneas.Std.U32.max) = true` of a string literal and it is listed with its statement hash in `formal/trusted/native-axioms.lock`, which holds the five literals of target code (`VERSION_V1`, `VERSION_V2`, `KID_EMPTY_MSG`, `KID_TOO_LONG_MSG`, the `expect` message of `rs1_fallbacks_verify`). These side conditions have a kernel proof (`simp only [U32.max, U32.numBits, UScalarTy.numBits]; decide`), so an upstream Aeneas `toStr` fix and a rev bump would remove the five axioms (open, preferred to a local replacement). The placeholder externals are replaced at S08–S09 by definitions, structures and `opaque` constants, so no trusted axiom remains and `axioms.lock` stays empty (human decision 2026-11-23, Section 4).

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

- The proof improvement phase (VERIFICATION.md §8): shorter, more robust, better factored proofs, with spec statements unchanged.
- Specifications for the translatable non-targets `open`, `open_with`, `new` and `try_new`.
- Upgrading the Aeneas `rev` (and then deleting any patch an upgrade makes unnecessary).
- Upstreaming the standard-library models of Section 4 to the Aeneas library.
- Proposing `request_state_wire` to the upstream SDK.
- A coverage audit with negative test files, and mutation testing.
- Per-claim cards and per-run agent provenance records, beyond the tool-and-model line that evidence files and function records already require.
- Moving `verification/host_origin/` into `formal/`.
