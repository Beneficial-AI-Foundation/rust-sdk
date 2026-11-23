# Request-State Verification — Status

Plan: [`docs/MCP_SDK_Verification_Master_Plan_EN.md`](../../docs/MCP_SDK_Verification_Master_Plan_EN.md).
Task state: [`board.yaml`](board.yaml) (authoritative). Per-function records:
[`functions/`](functions/). Step evidence: [`evidence/`](evidence/).

Last updated 2026-11-22 (Phase A final records pass; S01, S02, S03, S04, S04a in progress). Nothing in this file has been accepted by a human yet.

## Source baseline

| Item | Value |
|---|---|
| Repository | https://github.com/truonghoangle/rust-sdk (fork of the Rust MCP SDK) |
| Base commit | `0e2396f73a88617141b31f645de6f1171ed5f993` |
| SHA-256 of `crates/rmcp/src/model/request_state.rs` at base | `41e69cad94869be4b93120f3cd39a10fad4a3730585240b712c2ada1b311b416` |
| Pinned commit | not yet (S04a) |
| Aeneas | release tag `nightly-2026.08.20-5d08da4`, installed and verified at S03 (see [`evidence/S03.md`](evidence/S03.md)) |

The SHA-256 above was recomputed at S01 and matches the plan (Section 1). The file is
byte-identical at the base commit and at the current `main` (`7caec76`); see
[`evidence/S01.md`](evidence/S01.md).

Target files:
- `crates/rmcp/src/model/request_state_wire.rs` (new, public; added by the S04a refactor)
- `crates/rmcp/src/model/request_state.rs` (refactored onto it at S04a)

Both compile only with the `request-state` feature.

## Translated configuration

Single target, fixed in `scripts/aeneas-translate.sh` (S03):

```
--target x86_64-unknown-linux-gnu --no-default-features --features request-state --lib
```

The proofs hold only for this configuration.

## Scope decision (plan Section 1)

Aeneas handles pure, sequential, safe Rust well, and the request-state codec is mostly that:
framing, parsing, length checks and byte transcripts. The parts that are not (HMAC and Base64
crate internals, the system clock, `serde` JSON wrappers, formatting impls) are either behind
four opaque primitives with axioms (plan Section 4) or excluded (plan Section 2.3). The
verification concentrates on the byte logic underneath them.

**Objective.** Implementation-linked correctness of the request-state codec — framing,
configuration checks, version dispatch, token parsing, MAC transcripts, expiry, and seal/open
round-trip — under explicitly named contracts for HMAC-SHA256, Base64url and the
standard-library operations the code uses. Most of it is to be proved once, on the public wire
functions, and reused by the codec.

**Not claimed:**
- HMAC unforgeability or any other cryptographic security property;
- constant-time behaviour of the compiled code;
- correctness of the `hmac`, `sha2`, `base64` or `zeroize` crates;
- any excluded function (see "Excluded functions" below);
- the translatable public wrappers `open`, `open_with`, `new` and `try_new`, which are not
  targets;
- any configuration other than the one above;
- full MCP protocol verification.

Claims apply to the pinned commit and configuration only, not to upstream releases.

## Owners and budget

| Role | Name |
|---|---|
| Project owner | TBD — to be named by a human (S01 cannot be accepted until a human names them) |
| Spec owner(s) | TBD — to be named by a human (S01 cannot be accepted until a human names them) |
| Budget (people, time, compute) | TBD — to be named by a human (S01 cannot be accepted until a human names them) |

Only the named human spec owner may set `spec: REVIEWED`, and only a human may move a task to
`ACCEPTED` (plan Section 6). The D2 gate requires the project owner to confirm that people and
budget are allocated.

**Planned schedule:** the plan's two-week sprint, relative working days D1–D10 (plan Section 8,
"Steps"). Gates at D2, D5 and D10.

## Per-function status

All values are the S01 initial values. Line numbers for E targets are at the base commit and
are refreshed at the S04a pinned commit; W targets and E09a do not exist until S04a.

| ID | Rust symbol | translation | spec | linkage | proof |
|---|---|---|---|---|---|
| W01 | `request_state_wire::b64_len` | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| W02 | `request_state_wire::key_length_ok` | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| W03 | `request_state_wire::check_kid_len` | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| W04 | `request_state_wire::bytes_eq` | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| W05 | `request_state_wire::next_dot` | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| W06 | `request_state_wire::component_count` | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| W07 | `request_state_wire::version_of` | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| W08 | `request_state_wire::parse_rs1` | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| W09 | `request_state_wire::parse_rs2` | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| W10 | `request_state_wire::transcript_v1` | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| W11 | `request_state_wire::transcript_v2` | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| W12 | `request_state_wire::decode_expiry` | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| W13 | `request_state_wire::is_expired` | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| W14 | `request_state_wire::open_frame` | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| W15 | `request_state_wire::frame` | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| E01 | `RequestStateCodec::open_authenticated_body` (l. 722) | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| E02 | `RequestStateCodec::b64_len` (l. 780) | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| E03 | `RequestStateCodec::validate_key_length` (l. 755) | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| E04 | `RequestStateCodec::validate_config_kid` (l. 765) | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| E07 | `RequestStateCodec::seal_rs1` (l. 584) | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| E08 | `RequestStateCodec::seal_rs2` (l. 599) | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| E09 | `RequestStateCodec::open_rs1_at` (l. 620) | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| E09a | `RequestStateCodec::rs1_fallbacks_verify` (private helper) | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| E10 | `RequestStateCodec::open_rs2_at` (l. 676) | NOT_TRIED | DRAFT | ORIGINAL | OPEN |
| E11 | `RequestStateCodec::open_at` (l. 571) | NOT_TRIED | DRAFT | ORIGINAL | OPEN |

Total: 25 records (W01–W15, E01–E04, E07–E11, E09a). No specification has been drafted yet;
`spec: DRAFT` is the initial value of the status vocabulary, not a drafted statement.

**E05 and E06 are unassigned.** They belonged to `mac_v1`/`mac_v2`, which the S04a refactor
deletes (plan Section 2.2 and 2.3). The IDs are not renumbered, so the guides' references stay
valid, and they have no function record.

## Excluded functions (plan Section 2.3)

Excluded, not deferred: no function record, no specification, no proof. Each item below
except `mac_v1`/`mac_v2` (deleted from the source by the S04a refactor) and
`any_key_verifies` (never added) is in the Charon `exclude` list of
`[package.metadata.charon]` in `crates/rmcp/Cargo.toml`, with its blocker in a comment. That
table is **present in the working tree (S03), awaiting human sign-off**: uncommitted and not
accepted. That no target calls an excluded item is checked after the S04a translation; it is
not yet checked.

| Function | Blocker with the pinned toolchain (plan Section 9) | How it leaves the project |
|---|---|---|
| `mac_v1`, `mac_v2` (were E05, E06) | B1: HMAC types in the return type | Deleted by the refactor; replaced by W10/W11 and `prim` |
| `any_key_verifies` (proposed wire function) | B11: nested borrows in `&[&[u8]]` | Never added to the source |
| `seal_at` | B13: Aeneas "Unreachable" error on the TTL computation | `exclude` |
| `seal_with`, `seal` | B13: call `seal_at` | `exclude` |
| `new_with_keyring` | B13: Aeneas internal error | `exclude` |
| `with_rs1_signing`, `with_rs1_fallback` | B4: "no bottoms in the value" | `exclude` |
| `Debug`/`Display` for `RequestStateError`, `Debug` for `RequestStateCodec` | B13: Aeneas type assertion and internal error | `exclude` |
| derived `Debug` for `KidError`, `Version`, `FrameError`, `Rs1Parts`, `Rs2Parts`, `SealMode`, `SealOptions` | not a blocker: depend on the Aeneas axiom `Aeneas.Std.core.fmt.Formatter` and native-code string axioms; no target uses them (human decision 2026-11-22, S04a part 2, working tree) | `exclude` |
| `seal_json`, `seal_json_with`, `open_json`, `open_json_with`, `Error` for `RequestStateError` | B9: `serde` signatures; `Error::source` not modelled | `exclude` |
| crates `serde`, `serde_core` (crate-level) | B9: `serde` is out of scope; only the excluded JSON wrappers use it | `exclude` |

Consequences (plan Section 2.3): the round-trip theorems compose E07/E08 with E09–E11
directly, with no seal wrapper verified; the codec-state invariant is permanently a hypothesis;
`open`, `open_with`, `new` and `try_new` translate but are not targets.

## Trusted base

The toolchain (Charon, Aeneas, Lean, Mathlib) is installed and pinned since S03 (`formal/docs/evidence/S03.md`). The Charon `exclude`/`opaque` settings are present in the working tree (S03, extended at S04a part 2), awaiting human sign-off. No patch and no reviewed axiom or external model exists: `formal/trusted/Rmcp/` holds 41 unreviewed placeholder axioms (7 opaque types, 34 bare `Result` function/value axioms) started from the Aeneas templates at S04a part 2, not built by default (`Rmcp`/`RmcpExternal` are not default targets) and not in `axioms.lock`; every contract below is **planned, not yet written (S08–S09)** unless noted (inventory: [`evidence/S04a.md`](evidence/S04a.md)).

**Tools:** Charon and Aeneas (`nightly-2026.08.20-5d08da4`), Lean's kernel.
**Configuration:** the translated configuration above.
**Translation patches:** none planned (only if the D2 fallback is used).
**Exclusions:** the table above (Charon `exclude`, present in the working tree (S03), awaiting
human sign-off).

Planned external contracts (plan Section 4), to live in `formal/trusted/Rmcp/FunsExternal.lean`
and `TypesExternal.lean`:

| Contract | Planned model (summary of plan Section 4) | Status |
|---|---|---|
| HMAC (`prim.hmac_sha256`, `prim.hmac_sha256_verify`) | opaque `hmacSha256`; both functions always succeed | planned, not yet written (S08–S09) |
| Base64url, no padding (`prim.b64_encode_into`, `prim.b64_decode`) | opaque `b64`, `b64Decode`; law `b64Decode (b64 x) = some x` | planned, not yet written (S08–S09) |
| Standard library | value semantics; hand-written models as definitions where possible; one `HashMap::get` law | planned, not yet written (S08–S09) |
| Clock (`now_ms`, opaque) | opaque `ok` value; no target depends on it | planned, not yet written (S08–S09) |
| Codec state | a `Defs` hypothesis of E09/E10 and the round trips, not an axiom | planned, not yet written (S12) |

Opaque items (Charon `opaque` setting in `crates/rmcp/Cargo.toml`, plan Section 9), present in
the working tree (S03), awaiting human sign-off:
- `rmcp::model::request_state_wire::prim`: wraps the HMAC and base64 `Engine` types that cannot
  be translated (B1, B3); no Rust model; its axioms are planned (S08–S09).
- `rmcp::model::request_state::_::now_ms`: reads the system clock (I/O); no Rust model; used
  only by non-target wrappers.
- external crates `zeroize`, `base64`, `hmac`, `sha2`, `thiserror`, `chrono`, `serde_json`: only
  signatures are needed; their behaviour reaches targets only through `prim`.

Marking an item opaque only makes Charon keep its signature; the contracts it needs are the
planned axioms and models in the table above.

Axioms in force: none accepted. Native-code axioms (separate trust class, human decision
2026-11-22): the five `toStr` side conditions of the string literals in target code
(`VERSION_V1`, `VERSION_V2`, `KID_EMPTY_MSG`, `KID_TOO_LONG_MSG`, the `expect` message of
`rs1_fallbacks_verify`), listed with statement hashes in `formal/trusted/native-axioms.lock`
(working tree, awaiting review); the `axioms` audit accepts no other native-code axiom (none
declared outside `Rmcp.Types`/`Rmcp.Funs`), and enforces the lock once `Rmcp` is a default
target (S08–S09). Each
has a kernel proof, so an upstream Aeneas `toStr` fix would remove them (open item).

## Bugs found

None recorded.

## Open items

- `docs/VERIFICATION.md` (the Aeneas process guide, added 2026-11-22 verbatim) differs from this
  project's decided design in six places, kept as documented deviations: (1) it uses
  `lake build --wfail`; the project uses `warningAsError` per library plus the lean-guard checks
  (human decision: the pinned Aeneas library replays 4 `sorry` warnings); (2) its spec-file
  example uses `#guard_msgs (whitespace := lax, substring := true)`; the guard accepts only a bare
  `#guard_msgs in` before `#print axioms`; (3) it lists a generated `translation/<Crate>.lean`
  root module; Aeneas generates none and the `Rmcp` roots are `Rmcp.Types`, `Rmcp.Funs`; (4) it
  says `proofs/` need not be read; after S03 reviewers must read proofs for metaprogramming;
  (5) it gives every `[[lean_lib]]` a `globs` list; the project uses explicit `roots` only, and
  the guard allows exactly the keys `name`, `srcDir`, `roots`, `leanOptions` per library;
  (6) it allows no native-code axiom (`native_decide`/`bv_decide` never in a final proof); the
  project accepts the Aeneas `toStr` side conditions of string literals declared in
  `Rmcp.Types`/`Rmcp.Funs` and locked in `formal/trusted/native-axioms.lock` (human decision
  2026-11-22), and no other.
- S08–S09 (externals rewrite), open by human decision 2026-11-23 (S04a review R3a-1, R3a-2):
  (1) a shadowing `rmcp.<x>` declared in a project module that a trusted root imports passes all
  gates — enforce plan Section 5's rule that `RmcpExternal` imports only Aeneas and `Rmcp.Types`;
  (2) global `notation`/`infix` or a high-priority `instance` in `trusted/` can redirect generated
  code — ban them in `trusted/` or review them explicitly; (3) the `trusted/` text check does not
  lex `«…»` names (audit check 5 is authoritative). See `formal/README.md` "Trusted base".
- S08–S09 (externals rewrite): a root-level name declared in `trusted/` (e.g. `def toStr`) could
  make a name in the generated code ambiguous with an opened Aeneas name (Lean then picks the
  candidate that elaborates); not checked mechanically — reviewers check root-level names of the
  rewritten externals against names the generated code uses.
- Upstream: file an Aeneas issue for `toStr` (`Aeneas/Std/String.lean`), whose `decide +native`
  side condition has a kernel proof (`simp only [U32.max, U32.numBits, UScalarTy.numBits];
  decide`); after a fix and rev bump, `formal/trusted/native-axioms.lock` can be emptied. To be
  filed by a human.
- Resolved: plan discrepancy (W01/E02 dependencies). Plan Section 2.2 "Built on" listed W01
  for E07/E08, but `seal_rs1` and `seal_rs2` call the codec's own `Self::b64_len` (E02; base
  `0e2396f` lines 589 and 606–608), and the S04a refactor keeps that. Plan Section 2.2 now lists
  E02 for E07/E08 (working tree), matching the records (E02 `used_by: [E07, E08]`, W01
  `used_by: [E02]`).
- Owners and budget: TBD, to be named by a human (see "Owners and budget").
- The refactor PR (S04a part 1) awaits human approval and landing; the pinned commit is
  recorded only after it lands.
- `.github/workflows/lean-build.yml` has not yet run on GitHub/Linux (needs a push).
- Mathlib `.olean` files fetched by `lake exe cache get` are not digest-checked (human scope
  decision).
- Confirm the bare `#guard_msgs in` + `#print axioms` example against the first real spec file
  (S06).
- The copied pilot logs (`formal/docs/pilot/`) contain absolute local paths, including the
  macOS username; a human decides before any push.
- The pilot artifacts total about 1.2 MB; a human accepts the size.
- Lean-model domain notes for W06/W08/W09 and W10/W11/W15 (plan Section 3) are to be decided by
  the spec owner at S05.
- S05: `formal/specs/Defs.lean` imports the draft modules `Defs.Wire` and `Defs.RequestState`
  for drafting (lead decision); the spec owner signs them off, or they are removed from the root,
  before S05 lands (workflow guide, "Library roots"). See [`evidence/S05.md`](evidence/S05.md).
- S05 (a): E09–E11 and the round trips cannot discharge the W10/W11 `h_len` or W06/W08/W09
  `h_count` premises (`b64Decode` opaque and unbounded); those E specs need their own domain
  premise. See [`evidence/S05.md`](evidence/S05.md), "For later steps".
- S05 (b), for S08: a URL-safe alphabet law for `b64` (no `.` in the output) with Rust test
  vectors, needed by S15 to apply W08/W09 to sealed tokens. See
  [`evidence/S05.md`](evidence/S05.md), "For later steps".
- S03 R5a-1 (final review): the word bans, the `#`-command allowlist and the attribute allowlist
  of `lean-guard.sh sources` can be bypassed by gluing a banned token to a preceding literal or
  `)`; fix not applied in Phase A (human decision 2026-11-22). See
  [`evidence/S03.md`](evidence/S03.md), "Open items".
- S03 R5a-2 (final review): `formal/trusted/axioms.lock` locks the constants a trusted axiom's
  statement references by name only, not their bodies. See [`evidence/S03.md`](evidence/S03.md),
  "Open items".
- S03 X4: before S06 the human decides how spec statements are protected from `proofs/`-side
  instances and notation (`Specs` imports `Proofs`): re-elaborate the spec statements in job
  `check` without `Proofs`, or ban global instances and notation in `proofs/`. See
  [`evidence/S03.md`](evidence/S03.md), "Open items".
- S04a part 2 (working tree, awaiting review and human sign-off): the derived `Debug` impls are
  excluded per human decision (2026-11-22), which removes the `Aeneas.Std.core.fmt.Formatter`
  dependency; the native string-literal axioms of target code are handled via
  `formal/trusted/native-axioms.lock` (SPQR-style named baseline, checked by the `axioms`
  audit). Open: an upstream Aeneas `toStr` fix (kernel proof of the side condition) and rev bump
  to remove the five native axioms; the 41 placeholder externals (S08–S09) before `Rmcp` and
  `RmcpExternal` can become default targets. See [`evidence/S04a.md`](evidence/S04a.md).
- Docs-sync round 3: ten items left open by human decision (2026-11-22): (1) the claim that
  proofs need no trust review contradicts the X4 limit (plan Section 4, `WORKFLOW_AND_PR_GUIDE.md`,
  `REVIEWER_GUIDE.md`); (2) plan header and Section 9 say no blocker is open, despite the
  `Debug`-impl item above; (3) `WORKFLOW_AND_PR_GUIDE.md` "only pin" wording; (4) the Validation
  section of `AI_PR_REVIEW_QUESTIONS.md` lacks questions for the two CI jobs; (5) the guides do
  not mention that the kernel replay skips `unsafe`/`partial` constants; (6) `REVIEWER_GUIDE.md`
  custom-tactic wording; (7) `STYLE_GUIDE.md` says base64 `0.23.x`, the pin is `0.23.1`;
  (8) `AI_PR_REVIEW_QUESTIONS.md` writes `b64_decode` where `b64Decode` is meant; (9) the
  templates' file-wide `maxHeartbeats`/`maxRecDepth` options; (10) small format nits.
- The `docs/` guides do not yet describe the S03 fix-round-5 changes: the attribute allowlist,
  the `#`-command allowlist, `formal/trusted/axioms.lock`, the `lean-guard.sh fresh` step and the
  `lean-toolchain` pin.

## Incident

During the S03 fix-round-3 tests, an agent's test run started `rsync -a --delete` with `/` as
its destination; it ran for about three minutes before it was killed. Every unlink failed and
no deletion was found afterwards. The output-directory check now refuses `/`, a second guard
runs before `rsync --delete`, `RMCP_LLBC_DIR` is guarded (fix round 4, V3), and the agent role files
(`.claude/agents/*.md`, "Safety") restrict destructive commands to scratch directories. Details:
[`evidence/S03.md`](evidence/S03.md), "U6: output directory".

## Results

None. This section is filled in only with actual results, using the template of plan
Section 11.
