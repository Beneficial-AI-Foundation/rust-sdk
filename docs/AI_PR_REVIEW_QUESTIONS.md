# Questions for AI review of MCP SDK verification pull requests

Use these questions to review a verification PR in this fork of the Rust MCP SDK (`rmcp`). Answer
them from the current diff, the Rust source at the pinned commit, theorem statements, generated
Lean, external models and axioms, patches, Charon settings, status records, and validation results. Then report only the problems
found, grouped and tagged as described in [Reporting the review](#reporting-the-review). Ask the
author only when a material question remains unresolved after that inspection. A passing Lean
proof establishes its formal statement under its assumptions; review must also assess whether
those assumptions and that statement describe the pinned Rust implementation.

This guide supplements the [reviewer guide](REVIEWER_GUIDE.md), [style guide](STYLE_GUIDE.md),
and [workflow guide](WORKFLOW_AND_PR_GUIDE.md), which in turn build on the process guide
[`VERIFICATION.md`](VERIFICATION.md) and the
[master plan](MCP_SDK_Verification_Master_Plan_EN.md): its scope (Section 1), source behaviour
(Section 3), external axioms and trusted base (Section 4), layout, libraries, spec files and CI
(Section 5), status model (Section 6), acceptance evidence (Section 7), process (Section 8), and
agent rules (Section 10). Recheck those policies when reviewing future changes. The workflow
permits AI-drafted specifications and proofs, under disclosure and human responsibility.
Specifications, axioms, patches, and Charon setting changes each get at least two independent
agent reviews — this checklist is what each of those reviews follows — and then a human sign-off.
Run each review in its own session, without reading the other reviews first; agreement between
agents never accepts anything. This checklist supports review; it does not accept
specifications or substitute for human approval. The limits on what an AI review may propose are
stated in [Reporting the review](#reporting-the-review).

The principles in each section are meant to stay valid as the project evolves. The
[appendix](#appendix-historical-examples) ties them to the Host/Origin extraction and the
request-state pilot, as read on 2026-11-22. Extend the checks when new evidence exposes a gap, and
keep revision-specific examples in the appendix.

Paths below are relative to the repository root; the Lean project is `formal/`. Some files named
in the plan do not exist yet (for example the scripts and CI workflows arrive in S03 and S04a).
When a procedure step depends on a file that the PR's base does not contain, say so in the
`Unverified` line rather than skipping it silently.

## Procedure

Perform these steps before answering the questions. They produce the evidence the questions
refer to.

1. **Fix the revision.** Record the base and head commits of the PR and review exactly that diff:

   ```bash
   git fetch origin main pull/<N>/head:pr-<N>
   git merge-base origin/main pr-<N>          # base commit
   git rev-parse pr-<N>                       # head commit
   git diff <base>...pr-<N> --stat
   git diff <base>...pr-<N>
   ```

   If the author pushes after the review starts, re-record the head and re-read the changed hunks.
2. **Read the PR metadata and earlier reviews.** Check title, body, and footer against the
   [workflow guide](WORKFLOW_AND_PR_GUIDE.md#pr-workflow-and-formatting): step (`Sxx`) and
   function ID (`Wxx` or `Exx`) in the title, body starting with "This PR", full Rust function names, the
   AI-disclosure line, `Closes #...` where an issue exists, roughly 500 LOC, and no meaningful
   pushes after the PR was marked ready. Check that the diff stays inside the files the plan
   assigns to that step. Read earlier reviews, inline threads, and author replies. For each
   previous finding, check whether the current code fixes it, leaves it present, or shows that it
   was mistaken. Re-run the original counterexample against the revised statement; an author reply
   or resolved thread alone does not establish a fix.
3. **Check the source and the translation inputs.** Diff the target files and every translation
   input against the base:

   ```bash
   git diff <base>...pr-<N> -- crates/rmcp/src/model/request_state.rs \
     crates/rmcp/src/model/request_state_wire.rs crates/rmcp/Cargo.toml \
     crates/rmcp/build.rs Cargo.toml formal/lakefile.toml formal/trusted/ scripts/
   ```

   A source change is not a defect by itself: the refactor (plan Section 9) and new tests in
   `mod tests` (S16) both change the source. It is a defect if the change touches production code
   outside the reviewed refactor, if the regenerated translation is not in the same PR, or if a
   Charon setting, patch, or Aeneas `rev` changed without the review the workflow guide requires.
4. **Re-translate when translation inputs change.** For diffs touching production code in the
   target files, `[package.metadata.charon]`, `crates/rmcp/build.rs`, the root `Cargo.toml`,
   `formal/trusted/patches/`, the scripts, `formal/lakefile.toml`, or anything under
   `formal/translation/`, re-run the translation in a separate working tree and check that
   nothing differs from the commit — the same check as
   `aeneas-translation.yml`:

   ```bash
   scripts/aeneas-install.sh
   scripts/aeneas-translate.sh
   git status --porcelain
   ```

   Any difference means the committed translation is stale or was edited by hand; both are
   blocking. The translate script fails on a nonzero Aeneas exit, a missing target, any `sorry`,
   or a dependency version mismatch.
5. **Build the head.** For Lean changes the baseline is:

   ```bash
   cd formal
   ../scripts/lean-guard.sh sources
   lake exe cache get
   set -o pipefail; lake build 2>&1 | tee .lake/build.log
   ../scripts/lean-guard.sh build-log .lake/build.log
   ../scripts/lean-guard.sh axioms
   ../scripts/lean-guard.sh aeneas-archive
   ```

   Every library sets `warningAsError`; `--wfail` is not used because the pinned Aeneas library
   has four replayed `sorry` warnings (`WORKFLOW_AND_PR_GUIDE.md`, "Building and Checking"). The
   guard's rules and limits are listed there: `sources` is textual, `build-log` is an exact
   allowlist, `axioms` trusts only the axioms declared in the `RmcpExternal` roots
   (`Rmcp.TypesExternal`, `Rmcp.FunsExternal`) and replays every project constant in the kernel.
   In CI these checks run in a separate job on the uploaded build output, which cannot show that
   the output was compiled from these sources; check hand-written Lean for metaprogramming
   (`REVIEWER_GUIDE.md`, step 4).

   Stale `.lake` artifacts can hide a missing import or an unbuilt module. When in doubt, build the
   changed module explicitly, for example `lake build Proofs.Model.RequestState.OpenAt`. Confirm
   the library roots (`Defs.lean`, `Specs.lean`, `Proofs.lean`) list exactly the modules the PR
   intends to accept, and that drafts stay in `formal/specs/Drafts/`.
6. **Audit the trust base on base and head.** Compare the `#guard_msgs` axiom lists in
   `formal/specs/Specs/**` between base and head, and the diff of `formal/trusted/`. Expected
   builtin axioms are `propext`, `Classical.choice`, and `Quot.sound`. Every other axiom must be in
   the trusted-base section of `formal/docs/STATUS.md` (`trusted/` declares none since S08–S09;
   the external models are definitions and `opaque` constants, which these lists do not show, so
   audit them through the diff of `formal/trusted/`); anything else, including `sorryAx` or the
   axioms added by `native_decide`/`bv_decide`, is a trust change to report under question 6. Check
   that the `#guard_msgs` checks themselves were not loosened: each must be a bare
   `#guard_msgs in` before one `#print axioms` line, with the complete axiom list in its docstring
   (`lean-guard.sh sources` rejects options such as `drop` or `substring`). An unchanged textual
   count of `axiom` or `sorry` is not a base audit: imports, external models, and generated bodies
   can change the trust base without adding those keywords. If reusing an earlier audit, identify
   its exact revision; otherwise mark the missing comparison unverified.
7. **Run the Rust checks.** For changes to `request_state.rs`, its tests, or contracts checked by
   test vectors:

   ```bash
   cargo test -p rmcp --no-default-features --features request-state --lib
   cargo clippy -p rmcp --no-default-features --features request-state --lib -- -D warnings
   cargo +nightly fmt --check
   ```

   For a diff that claims to touch only `mod tests`, confirm that from the diff itself.
8. **Read the evidence records.** Read `formal/docs/evidence/Sxx.md`, any
   `formal/docs/blockers/Sxx.md`, `formal/docs/board.yaml`, the affected
   `formal/docs/functions/<ID>.yaml`, and the trusted-base section of `formal/docs/STATUS.md`.
   Compare each recorded command, exit status, and Aeneas tag with what you ran. Plan Section 7 lists what an evidence file must contain.

## Which sections apply

Answer the eight core questions on every PR. Then select topic sections by the kind of change. A
PR that touches several kinds needs each applicable section.

| Kind of change | Typical files | Sections to apply |
| --- | --- | --- |
| Specification of one target | `formal/specs/Drafts/*.lean`, `formal/specs/Defs/*.lean` | Specification strength and error order; Status records |
| Proof of one target | `formal/proofs/Proofs/Model/RequestState{,Wire}/*.lean`, its restated theorem in `formal/specs/Specs/Model/*.lean` | Specification strength; Proof maintainability; Validation |
| Refactor, source change, or Aeneas `rev` bump | `crates/rmcp/src/model/request_state{,_wire}.rs`, `formal/lakefile.toml` | Translation, refactor, and source linkage; Validation |
| Translation, Charon settings, or patch | `crates/rmcp/Cargo.toml` (`[package.metadata.charon]`), `formal/trusted/patches/`, `formal/translation/**`, the pilot record (removed from git history on 2026-11-23) | Translation, refactor, and source linkage; External axioms |
| External model or axiom | `formal/trusted/Rmcp/*External.lean`, `formal/trusted/evidence/`, `formal/proofs/Proofs/External/` (and `formal/proofs/Proofs/Consistency/` if an axiom is added again), trusted base in `formal/docs/STATUS.md` | External axioms and the trust boundary |
| Transcript, encoding, or round trip | `RequestStateWire/TranscriptV{1,2}.lean`, `SealRs1/SealRs2`, `RequestState/Roundtrip.lean` | Transcripts, encoding, and round trips; External axioms |
| Rust boundary tests | `mod tests` in `request_state.rs` or `request_state_wire.rs` | Validation; core question 8 |
| Status and evidence only | `formal/docs/board.yaml`, `functions/*.yaml`, `evidence/`, `blockers/`, `STATUS.md` | Status records and evidence |
| CI, scripts, agents, documentation | `.github/workflows/{aeneas-translation,lean-build,patched-tests}.yml`, `scripts/` (including `scripts/lean-guard.sh`), `formal/trusted/aeneas-bundle.sha256`, `CLAUDE.md`, `.claude/agents/`, `docs/`, `formal/README.md` | Validation and CI; question 8 |
| Other extractions | `verification/host_origin/**` and similar | Translation, refactor, and source linkage; External axioms |

## Questions to answer on every PR

1. **What exact claim is this PR meant to establish?** Identify the step, function ID, Rust
   symbol and line at the pinned commit, changed theorem, and intended observable behaviour. Do
   the title, body, and status records match the actual code? A function translated to compile is
   not a function verified; a generated file is not a specification.
2. **Am I reviewing the right revision?** Use the base and head from procedure step 1, inspect the
   complete diff, and distinguish new changes from inherited problems. Have later commits changed
   the source, the generated Lean, or the contracts covered by an earlier approval or build?
3. **Could a plausible wrong implementation satisfy this postcondition?** Try returning the
   wrong error variant, checking errors in a different order, accepting `now == expiry` the wrong
   way, dropping the length prefix from a MAC transcript, swapping token parts, stopping at the
   first matching fallback key, or ignoring the associated data. Identify the clause that excludes
   each relevant counterexample.
4. **Are the premises satisfiable and justified at the call sites?** Look for no-overflow domains
   that exclude realistic inputs, codec-state hypotheses stronger than what the constructors
   enforce, a 64-bit hypothesis that is used for more than the `usize → u64` cast, and assumptions
   equivalent to the desired conclusion.
5. **Does the Lean model faithfully represent the Rust behaviour?** Confirm the theorem is stated
   about the translated definition in `formal/translation/Rmcp/Funs.lean` (or the external in
   `formal/trusted/Rmcp/FunsExternal.lean`), with the full generated name current after the latest
   translation, not a local copy. Then check
   success, each error variant, panics, arithmetic, and external calls against the Rust source.
6. **What changed in the trust assumptions?** Use the audit and `#print axioms` results from
   procedure step 6. Inspect direct and transitive `sorry`, axioms missing from the trusted base,
   external models that changed, new patches or `exclude`/`opaque` entries, and hand edits to
   generated files. Determine whether an
   apparent reduction in axioms merely moved assumptions into model definitions.
7. **Can callers actually use this result?** Can the E09–E11 and round-trip proofs, and for a W
   target every E proof listed in its `used_by` field, consume this theorem as stated? Does the postcondition expose the transcript, error, and output facts the
   next step needs? Is the statement in the spec file phrased only with `Defs` definitions?
8. **What validation supports my conclusion?** Report the commands from the procedure that
   actually ran on the head revision and their results. Separate command results from claims in
   the PR body or evidence files, and separate a successful build from a passing audit.

Historical examples for each question are listed in the [appendix](#appendix-historical-examples).

## Specification strength and error order

- Does the theorem cover both success and every error result, as the plan requires, rather than
  only the success path? Does it distinguish an application-level `Err(RequestStateError::…)` from
  an Aeneas failure or panic?
- For E09 and E10, does the specification fix the complete error order of plan Section 3? Test an
  input that is wrong in two ways (for example an over-long encoded kid that is also bad Base64)
  and check that the theorem determines which error is returned.
- Is each error variant pinned with its fields where they matter, for example
  `KeyTooShort { minimum: 32, actual: len }`, and the two distinct `InvalidKeyring` messages of E04?
- Is the expiry boundary exact? `now_ms == expiry` is accepted, expiry `0` means no expiry, and a
  negative nonzero expiry is compared as a signed value. Does the statement use signed big-endian
  decoding of the first 8 bytes?
- Does a specification add a restriction the Rust code does not have? E04 accepts any nonempty
  UTF-8 kid of at most 255 bytes; an alphabet restriction would be unfaithful. `seal_rs2` accepts
  any kid; validity belongs in the round-trip premise, not in E08's precondition.
- Is the arithmetic domain written into the theorem? The workspace sets no `overflow-checks`, so
  release builds wrap while Aeneas models overflow as failure. A theorem about E02 or the
  `with_capacity` sums in E07/E08 must state its no-overflow domain, and its documentation must
  say it matches debug-build semantics on that domain.
- Is a statement about `usize` correct for the configured width? The plan pins a 64-bit target;
  a hypothesis fixing the width must be explicit, and used only where it is needed.
- For E09 ring codecs, does the specification describe "some configured fallback key verifies the
  tag" without asserting which key, and without implying early exit? The functional theorem says
  nothing about timing; check that its documentation does not suggest otherwise.
- Is a mathematical abstraction (byte lists, `b64`, abstract HMAC state) clearer than repeating
  implementation steps? Conversely, does it erase a detail callers need, such as part order?
- Are existential witnesses sufficiently constrained? An existential is not inherently weak:
  inspect whether its predicate determines the relevant values before requesting a rewrite.
- For an AI-drafted specification (listed in the PR footer), does every clause cite the Rust
  lines or plan section it encodes, and does that source say what the clause says? Look for
  clauses that mirror the translated code step by step, unused hypotheses, and postconditions
  that follow from the types alone. Was the statement changed after an earlier review round in a
  way that weakens it? Did the same agent draft and prove it?

## Translation, refactor, and source linkage

- Was the translation regenerated by `scripts/aeneas-translate.sh` from the pinned Aeneas `rev`
  and the committed Charon settings and patches? Is anything under `formal/translation/` edited by
  hand? Under `formal/` no hand edit is allowed; the translation CI must pass.
- Does every target appear in `Funs.lean` with a real body, with no `sorry` anywhere in the
  generated files? With the plan's exclusions Aeneas exits 0, so the script treats a nonzero exit
  as failure; a run that needed out-of-scope bodies to fail means an exclusion is missing.
- For a refactor change, does each row of the plan's refactor table hold in the diff: the same
  bytes MACed, same error values in the same order, every fallback still tried, empty-fallback
  check still before decoding, `u64::from_be_bytes(..) as i64` bit-identical to
  `i64::from_be_bytes`? Is the only public API change the addition of
  `rmcp::model::request_state_wire`?
- Does every new public wire item follow the Aeneas-safe coding rules of plan Section 2.1 (free
  functions, byte slices, no nested borrows, no HMAC or `Engine` types in signatures, error enums
  instead of string literals, no Lean keyword identifiers), carry documentation, and use
  `#[non_exhaustive]` on enums and structs?
- Is token byte-identity before and after the refactor shown by a committed regression test, for
  one rs1 and one rs2 token? Do the tests now cover `Expired` and `InvalidKeyId`, which the pilot's
  equivalence check did not?
- Does the `linkage` field match the decision actually taken? A landed and re-pinned refactor makes
  targets `ORIGINAL` relative to the new pin; if the refactor is applied as a patch in
  `formal/trusted/patches/` instead, every target's linkage names that patch (the case since the D2
  fallback of 2026-11-23: all 25 targets are `patch-01`).
- For a translation patch: does its header state the change, why it is needed (with the upstream
  issue, if any), and why the behaviour is unchanged? Is it minimal, with one concern? Does
  `patched-tests.yml` pass on the patched copy, and do those tests actually exercise the changed
  behaviour?
- Does the PR reintroduce a function excluded from the project (plan Section 2.3), as a target, a
  callee of a target, or by dropping one of its `exclude` entries? Re-adding one needs a recorded
  requirement change and a translation run showing the blocker resolved.
- Are new `exclude` or `opaque` entries in `[package.metadata.charon]` justified by a comment, and
  are their verification consequences visible? An excluded item must be outside the target
  closure; an opaque item is a last resort (it cannot be translated and has no useful Rust model)
  and becomes an external that needs a reviewed model in `formal/trusted/` (a definition or `ok`
  of an `opaque` constant; no axiom since S08–S09).
- Does a proposed change to the Rust, a patch, or a Charon setting actually match the intended
  Rust behaviour, or is the problem in a theorem's premises or in a library model? Check the source
  before changing translation inputs to make a proof work.
- For extractions outside `formal/` (for example `verification/host_origin/`), is the README
  precise about which functions are extracted, which are opaque, and that no property has been
  proved?

## External axioms and the trust boundary

- Does each external model or axiom describe its primitive on its own terms? It may not assume
  that a target function is correct.
- Is any external a bare `Result` axiom (`axiom f : … → Result T`)? It must be an exact model or
  `ok` of an opaque value. Is any axiom stated about a function whose Lean type merges distinct
  Rust types (for example `size_of`)?
- Does the HMAC model match plan Section 4: `prim.hmac_sha256 k m` always succeeds with the opaque
  `hmacSha256 k m`, and `prim.hmac_sha256_verify k m t` holds iff `t = hmacSha256 k m` as byte
  lists? Does `verify` reject short or long tags?
- Does the Base64 model match the `URL_SAFE_NO_PAD` engine, rejecting padding and non-canonical
  trailing bits? Its laws (`b64Decode (b64 x) = some x`, `b64Decode s = some y ↔ b64 y = s`,
  alphabet, length) are theorems in `formal/proofs/Proofs/External/Base64.lean`, not
  assumptions; does a proof rely on any Base64 fact that is not one of them?
- Do the W06–W09 specifications, stated with `List.splitOn '.'`, agree with `str::split('.')` on
  the empty string, a string with no `.`, leading and trailing dots, and consecutive dots? Do
  E09–E11's part counts follow from them?
- Are standard-library models (`str::len`, `str::as_bytes`, `String::from_utf8`, `Option::ok_or`,
  `HashMap::get`, `Zeroizing` deref) value-correct for the operations used, without hidden assumptions about hashing or
  allocation? Is allocation failure an explicit assumption rather than a silent no-panic claim?
- Is the codec-state invariant no stronger than what the constructors enforce? Constructor
  correctness is out of scope, so every clause of the invariant must be checkable against the
  constructor source.
- Is each definition, structure and `opaque` constant of `formal/trusted/` listed in the
  trusted-base section of `formal/docs/STATUS.md` with its justification, and does its docstring
  repeat it (Rust source by file and line, stated exceptions)? Does `trusted/` declare no
  `axiom` (human decision 2026-11-23)? An axiom added again needs a human decision and a
  consistency model in `formal/proofs/Proofs/Consistency/` that proves every axiom of its group.
- Are the dependency versions the models rely on pinned in `scripts/aeneas-translate.sh`
  (`hmac`, `sha2`, `base64`; `digest`, `zeroize`, `chrono`, `serde_json` are cited but not yet
  pinned, plan Section 4), and do they match the crate source cited?
- Is each model checked against concrete vectors from the real crates (RFC 4231 for HMAC, known
  Base64url values, split behaviour) in `mod tests`, and listed in
  `formal/trusted/evidence/README.md`? These tests catch a mismatched model; they are not a
  consistency proof, and the review should not describe them as one.
- If an external becomes a concrete definition, where is the justification that the Rust function
  computes it? A concrete body can make correspondence lemmas reflexive while hiding the
  implementation-to-model assumption from the axiom count; it is still part of `formal/trusted/`.
- Does any statement or docstring claim more than the plan's scope: HMAC unforgeability,
  constant-time behaviour, correctness of the `hmac`, `sha2`, `base64`, or `zeroize` crates, or
  coverage of the public wrappers?

## Transcripts, encoding, and round trips

- Does the W10/W11 theorem state the transcript bytes exactly, including the domain separator,
  big-endian 8-byte length prefixes, and field order? Would a transcript without a length prefix,
  or with kid and ad swapped, also satisfy it?
- Do E07–E10 use the W10/W11 theorems rather than restating the transcript?
- Does E07/E08 fix the version prefix, part order, and `.` delimiters, and tie the tag to the
  transcript of the same key, ad, and body?
- Are round-trip theorems stated with exactly the plan's conditions: body of at least 8 bytes,
  expiry `0` or `now ≤ expiry`, the same associated data, an rs1 opening codec that is the same
  single key or a ring whose `rs1_fallbacks` include the signing key, and an rs2 kid that is valid
  UTF-8 of 1–255 bytes mapped by the ring to the signing key? Is any condition missing, or is an
  extra condition excluding valid tokens?
- Does a round trip state that opening returns `body[8..]`, not the whole body or a payload?
- Do encoder postconditions establish the opening function's premises? Check that the 340-byte
  encoded-kid bound in E10 is consistent with a 255-byte kid under `b64`.
- Is each round-trip theorem stated at the intended layer, about the translated `seal_*` and
  `open_*` functions, rather than only about pure models?

## Status records and evidence

- Does the function record use the plan's vocabulary exactly, with `translation`, `spec`,
  `linkage`, and `proof` as independent fields? Is a function called verified only when
  `proof: CHECKED`, `spec: REVIEWED`, `linkage: ORIGINAL`, and its axioms are all in the trusted
  base?
- Was `spec: REVIEWED` set by a named human spec owner after at least two independent agent
  reviews recorded in `spec_reviews`, none by the drafter, as plan Section 6 and the workflow guide
  require? Is AI drafting and AI review disclosed in the PR footer and recorded, with tool and
  model, in the evidence file?
- Does `board.yaml` reflect the step's real state? An accepted blocker report closes the task of
  reporting, never the function's proof. The deadline never changes a status.
- Does each evidence file record the exact commands, exit status, Aeneas tag and commit
  translated, axioms added or changed, and reviewer decision? Do they match what you ran?
- Does the results section of `formal/docs/STATUS.md` follow the plan's results template, list only
  actual results, and name open, blocked, and patched functions as such? Does its trusted-base
  section match `formal/trusted/` and the `exclude`/`opaque` lists?

## Proof maintainability and library layering

- Do the import directions hold? `RmcpExternal` imports only Aeneas and `Rmcp.Types`; `Defs`
  imports only Aeneas, Mathlib, `Rmcp`, and `RmcpExternal`; `Proofs` imports `Rmcp`,
  `RmcpExternal`, and `Defs`, never `Specs`; nothing imports `Specs`. Does a draft with `sorry`
  stay in `formal/specs/Drafts/`, outside every library?
- Is the statement in the spec file phrased only with `Defs` definitions, so its meaning does not
  depend on proof-private definitions? Does its restated `theorem Theorems.…` have the signed-off statement text and is it proved by the spec theorem, and is it in
  Rust source order with its `#guard_msgs` axiom check?
- Does the file sit at the path the plan assigns (one file per Rust item,
  `Proofs/Model/RequestState{,Wire}/<Function>.lean`), and does the theorem use the plan's name
  (`<function>_spec`, `rs1_roundtrip`, …) or a recorded replacement once generated signatures are
  known?
- Is there an existing Aeneas, Mathlib, or local lemma that avoids rebuilding infrastructure? Is a
  new helper actually used? Are shared lemmas about `b64`, `dot`, or the HMAC model placed in a
  shared proof file rather than duplicated per function?
- Are flexible nonterminal tactics replaced by explicit lemma sets where practical? During phase B
  ("complete first") this is non-blocking unless the proof is fragile enough to break CI. Are
  heartbeat increases justified and local?
- Do docstrings explain the statement, the Rust lines it covers, and its assumptions, rather than
  narrate proof development? Do they state the arithmetic domain and target width when relevant?
- Did a proof worker stay inside its assigned file and the statement's restated theorem? The
  `mcp-lean` role may not change statements, `Defs`, generated files, or anything under
  `formal/trusted/`, and may not add axioms, `sorry`, `native_decide`, or `bv_decide`.

## Validation and CI

The commands are in the [procedure](#procedure). These questions interpret their results.

- Did checks use the PR's current sources and the toolchain installed by
  `scripts/aeneas-install.sh`, without stale build artifacts masking a missing import or an unbuilt
  module? Was the generated Lean built in `formal/`, not against an unrelated Aeneas library build?
- Do the three workflows run on the paths the plan lists, for fork and branch PRs, and preserve
  failing exit codes through pipes? Does every `[[lean_lib]]` set
  `leanOptions = { warningAsError = true }`, and does `lean-build.yml` run `lake build` with
  `pipefail` plus the four `scripts/lean-guard.sh` checks (`sources`, `build-log`, `axioms`,
  `aeneas-archive`)? Has each check been shown to fail once — on a hand edit to `Funs.lean`, a new
  axiom, a `sorry`, and a failing patched test (plan S17)?
- Does a fresh clone reproduce the install, translation, and build, with `git status` clean
  (plan S18)?
- Do the Rust boundary tests exercise each case in the plan's Section 7 table for the affected
  function? A test asserting only `is_err()` does not check which error variant is returned.
- For automated or agent-driven workflows, are claimed trigger conditions and edit limits actually
  enforced by permission settings, not only by role prompts?
- Does the proof's build cost come from repeated arguments, broad imports, or expensive
  automation that a symbolic argument could replace? Is a regression acceptable, worth a tracked
  follow-up, or blocking?

## Reporting the review

The questions above are the investigation checklist, not the outline of the report. The report
lists only problems. Do not answer the questions one by one, do not restate what the PR does, and
do not list the checks that passed except in the validation footer. A reader should be able to see
the verdict and every finding, grouped by severity, without reading anything else.

### Severity groups

Group findings under these three headings, in this order, using the vocabulary of the
[reviewer guide](REVIEWER_GUIDE.md). Omit a heading that has no findings.

- **Blocking:** a demonstrated counterexample to a specification, an unsatisfiable or
  question-begging premise, an unfaithful model of the Rust behaviour, a refactor change that
  alters behaviour, an unjustified change to the trust base, a status record that overstates the
  result, or validation that did not actually pass on the head revision.
- **Judgment (blocking or non-blocking):** level of abstraction, usability by later steps,
  composition gaps, test coverage of boundary cases, and build-time regressions, in proportion to
  their impact.
- **Non-blocking:** naming, placement, reuse, comments, PR format, and style, unless the plan makes
  the point mandatory or the problem is pervasive.

A keyword match or a difference from an earlier extraction is a prompt to investigate, not a
finding by itself. State the group explicitly so the human reviewer can override it. State
explicitly whether a judgment finding blocks, and count it in the verdict if it does. When a new
theorem inherits a weak shared contract, locate the new caller-facing consequence and distinguish
it from the pre-existing root cause. Do not classify a missing guarantee as an implementation bug
without evidence for that stronger claim.

### Category tags

Tag each finding with one category so that findings of the same kind can be compared across PRs.
The tag names the section of this guide that produced the finding:

| Tag | Source section |
| --- | --- |
| `spec` | Specification strength and error order; core question 3 |
| `premise` | Core question 4 |
| `model` | Core question 5; Translation, refactor, and source linkage |
| `linkage` | Refactor and patch behaviour, source pin, and `linkage` field |
| `trust` | Core question 6; External axioms and the trust boundary |
| `usability` | Core question 7; Transcripts, encoding, and round trips |
| `status` | Status records and evidence |
| `validation` | Core question 8; Validation and CI |
| `maintainability` | Proof maintainability and library layering |
| `format` | Core questions 1 and 2; PR title, body, revision |

### Finding format

Write each finding as one bullet in this shape:

```text
- [`tag`] `path/to/File.lean:LINE` `theorem_name` — one-sentence defect.
  Evidence: counterexample, dependency argument, or Rust lines that define the intended behaviour.
  Consequence: what later steps, proof meaning, or verification scope lose.
  Ask: the focused question or requested correction, and what evidence would resolve it.
```

Keep the first line short enough to scan. Put the reviewed head commit once in the footer, not in
every finding. If the same defect appears at several places, report it once and list the
locations. Cite Rust lines at the pinned commit, and say which pin you used.

**What an AI review may propose.** The workflow permits AI-drafted specifications, so an AI
review may propose replacement theorem statements, postcondition clauses, or contract definitions
in Lean, as well as proof text, patches, and Rust test cases. Each proposal must:

- be labelled as an AI-drafted proposal, so that adopting it triggers the disclosure rule;
- cite the Rust lines at the pinned commit, or the plan section, that each proposed clause
  encodes, and come with the counterexample or gap it fixes;
- leave acceptance to the human spec owner. A review may not mark a specification accepted,
  and an AI reviewer may not propose a statement for a specification it drafted itself.

Prefer naming the missing property in words when the right formulation depends on a design choice
the plan does not settle; then ask the author or spec owner to choose.

Useful author-facing questions after investigation include:

- "An rs2 token with a 341-byte encoded kid that is also invalid Base64 should return
  `InvalidKeyId`. Which clause rules out `InvalidEncoding` here?"
- "This transcript statement also holds without the length prefix. Which clause fixes it?"
- "This external became a definition and its axiom disappeared from the `#guard_msgs` list. Where
  is the argument that the Rust function computes it?"
- "The round-trip premise requires a nonempty ad. Is that intended? `seal_rs1` accepts an empty ad."
- "The record says `linkage: ORIGINAL`, but the pin still predates the `request_state_wire`
  refactor. Was the refactor PR (S04a) landed and re-pinned?" (Under the D2 fallback the answer
  is no, and the record must name the patch, e.g. `patch-01`.)
- "`git status --porcelain` shows a diff in `Funs.lean` after re-running the translate script.
  Was the translation regenerated after the last Charon setting change?"

### Report layout

```text
Verdict: <no blocking finding | N blocking finding(s)> on <head commit> (base <base commit>).

Blocking
- ...

Judgment
- ...

Non-blocking
- ...

Validation: <commands from the procedure that ran on the head, each with pass/fail>.
Unverified: <material boundaries not checked, or "none">.
```

The verdict line comes first. If no blocking problem is demonstrated, say so without claiming
cryptographic security or full protocol verification. The validation line names the commands that
actually ran and their results; it does not repeat the PR body or evidence files. Recheck claimed
fixes against the updated diff rather than accepting an author reply. An AI review remains
assistance for the responsible human reviewer.

## Appendix: historical examples

Each entry illustrates a principle above; it is not a finding about the current code. Entries were
read on 2026-11-22 from the Host/Origin extraction (PR #4, merged as `7caec76`) and from the
request-state pilot recorded in the [master plan](MCP_SDK_Verification_Master_Plan_EN.md),
Sections 8–9, and the pilot record (removed from git history on 2026-11-23). The pilot wrote all its
outputs outside the repository, under `/tmp`: run 1 compiled the repository's own `crates/rmcp`
(except its `e04`/`e04c` attempts, which used scratch sources), and runs 2 and 3 used scratch
copies. Its results are as recorded there and have not been re-run here. Add newer examples, with
their PR or commit, below the existing ones.

**Extraction is not verification.** The Host/Origin README states that its extraction "is not a
proof of the Host/Origin rejection property", that the two `parse_allowed_*` parsers are axioms,
and that the request-level `validate_dns_rebinding_headers` path failed in Aeneas. A summary that
called that PR a verification of DNS-rebinding protection would overstate it. (Q1, Q6)

**Hand edits to generated files must be recorded.** The pinned Aeneas emitted `filter_map` and
`any` fields in one `Iterator` instance that its Lean library lacks; the Host/Origin extraction
removed them from `Funs.lean` by hand and documented the edit in its README. Re-extraction without
re-applying and recording the edit changes the build result. Under `formal/` such an edit is not
allowed at all: the fix is a patch, a Charon setting, or an upstream fix, and the translation CI
rejects hand edits. (Translation section; Q5)

**Exit codes do not identify which targets failed.** In the pilot's second run, seven
out-of-scope bodies failed in Aeneas (`Debug`/`Display` impls, three constructors, and `seal_at`;
recorded in the pilot record (removed from git history on 2026-11-23)), while all eleven targets compiled. No exit status
was recorded; Aeneas generated partial files, and an exit code alone would not say whether a target
or an out-of-scope body had failed. The plan responded by excluding those items, so Aeneas now
exits 0 and the translate script treats a nonzero exit, a missing target, or any `sorry` as
failure. (Procedure step 4; Validation)

**Library models can be wrong.** The pinned Aeneas library models `i64::from_be_bytes` as taking
`Array I8`, whereas Rust takes `[u8; 8]` (blocker B6, fixed upstream in Aeneas #1355). A proof
built on that model would be about the wrong signature. The tested workaround changes source
(`u64::from_be_bytes(..) as i64`), so it carries a linkage consequence. (Q5; External axioms)

**Workarounds move the trust boundary.** In pilot run 2, blockers B1–B3 were resolved by small
opaque adapter modules (`mac`, `b64`, `dot`); run 3 replaced them with the four public
`request_state_wire::prim` functions, and the same reasoning applies. Their bodies are not extracted, so their contracts and tests become
the trust boundary. The plan describes this as narrower and more explicit than contracts on the
crate APIs, and states that the adapter "does not prove anything about it". (Q6; External
axioms)

**Equivalence evidence has gaps.** The pilot compared 9 tokens and 162 `open` results between the
original and adapted code and found them byte-identical, covering `Ok`, `IntegrityCheckFailed`,
`InvalidEncoding`, `MalformedFormat`, and `UnknownKeyId`. It did not cover `Expired` or
`InvalidKeyId`, so the plan still requires a regression test. Check the stated coverage before
treating such a comparison as complete. (Adapter checklist; Validation)

**Build against the intended library.** The pilot compiled generated Lean against an existing
Aeneas library build at `6e167c9b`. Under `backends/lean/`, the pinned `5d08da45` adds
`ExtractLeanKeywords.lean` and changes `lakefile.lean` (one new `lean_exe`); the `Aeneas` library
sources are identical. The in-repo build in `formal/` (B10) was still
outstanding.
A green build reported against another library revision does not establish the pinned build.
(Procedure step 5; Validation)

**Arithmetic semantics depend on build profile.** The workspace sets no `overflow-checks`; Aeneas
models overflow as failure, matching debug builds only. Arithmetic theorems must therefore state
their no-overflow domain. (Specification strength; Q4)
