# Questions for AI review of MCP SDK verification pull requests

Use these questions to review a verification PR in this fork of the Rust MCP SDK (`rmcp`). Answer
them from the current diff, the Rust source at the pinned commit, theorem statements, generated
Lean, external contracts, status records, and validation results. Then report only the problems
found, grouped and tagged as described in [Reporting the review](#reporting-the-review). Ask the
author only when a material question remains unresolved after that inspection. A passing Lean
proof establishes its formal statement under its assumptions; review must also assess whether
those assumptions and that statement describe the pinned Rust implementation.

This guide supplements the [reviewer guide](REVIEWER_GUIDE.md), [style guide](STYLE_GUIDE.md),
and [workflow guide](WORKFLOW_AND_PR_GUIDE.md), which in turn build on the
[master plan](MCP_SDK_Verification_Master_Plan_EN.md): its scope (Section 1), source behaviour
(Section 3), external contracts (Section 4), library rules (Section 5), status model (Section 6),
acceptance evidence (Section 7), and agent rules (Section 10). Recheck those policies when
reviewing future changes. The workflow permits AI-drafted specifications and proofs, under
disclosure and human responsibility; a named human spec owner accepts every specification, and
two agents agreeing is not a review. This checklist supports review; it does not accept
specifications or substitute for human approval. The limits on what an AI review may propose are
stated in [Reporting the review](#reporting-the-review).

The principles in each section are meant to stay valid as the project evolves. The
[appendix](#appendix-historical-examples) ties them to the Host/Origin extraction and the
request-state pilot, as read on 2026-11-22. Extend the checks when new evidence exposes a gap, and
keep revision-specific examples in the appendix.

Paths below use `<LEAN>` for the crate-local Lean project `crates/rmcp/lean/`. Some files named in
the plan do not exist yet (for example `scripts/check.sh` and `Checks/Axioms.lean` arrive in S17).
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
   function ID (`Exx`) in the title, body starting with "This PR", full Rust function names, the
   AI-disclosure line, `Closes #...` where an issue exists, roughly 500 LOC, and no meaningful
   pushes after the PR was marked ready. Check that the diff stays inside the files the plan
   assigns to that step. Read earlier reviews, inline threads, and author replies. For each
   previous finding, check whether the current code fixes it, leaves it present, or shows that it
   was mistaken. Re-run the original counterexample against the revised statement; an author reply
   or resolved thread alone does not establish a fix.
3. **Check the source pin.** Compare the pinned commit and the SHA-256 of
   `crates/rmcp/src/model/request_state.rs` in `verification/manifest.yaml` with the file at the
   head:

   ```bash
   shasum -a 256 crates/rmcp/src/model/request_state.rs
   git diff <pinned-commit> pr-<N> -- crates/rmcp/src/model/request_state.rs
   ```

   A changed hash is not a defect by itself: the adapter (plan Section 9) and new tests in
   `mod tests` (S16) both change it. It is a defect if the manifest was not updated, if the change
   touches production code outside the reviewed adapter, or if proofs were not re-run after
   re-extraction. Re-extraction invalidates earlier proof evidence for every affected function.
4. **Re-extract when extraction inputs change.** For diffs touching `request_state.rs`
   production code, `<LEAN>/scripts/extract.sh`, Charon arguments, or generated `Rmcp/Types.lean`,
   `Rmcp/Funs.lean`, or `translation.json`, re-run extraction with the pinned toolchain (Charon
   `0.1.235`, Aeneas `5d08da45`, Rust `nightly-2026-06-01`, Lean `4.31.0`) in a separate working
   tree and diff the generated files against the commit:

   ```bash
   cd crates/rmcp/lean && ./scripts/extract.sh
   git diff --stat -- Rmcp/
   ```

   Aeneas exits with code 1 while out-of-scope bodies fail. Check the target list against the
   Aeneas log, not the exit code. Every hand edit to a generated file must be recorded.
5. **Build the head.** For Lean changes the baseline is:

   ```bash
   cd crates/rmcp/lean
   lake build
   lake build Theorems
   lake build Checks
   ```

   Stale `.lake` artifacts can hide a missing import or an unbuilt module. When in doubt, build the
   changed module explicitly, for example `lake build Proofs.Model.RequestState.OpenAt`. Confirm
   the import roots (`Specs.lean`, `Proofs.lean`, `Theorems.lean`, `Checks.lean`) list exactly the
   files the PR intends to accept.
6. **Audit the trust base on base and head.** Run the axiom audit (`scripts/check.sh` or
   `lake build Checks`) on both revisions. For each changed public theorem, run
   `#print axioms <theorem>` in a scratch file. Expected builtin axioms are `propext`,
   `Classical.choice`, and `Quot.sound`. Every other axiom must carry an ID listed in
   `verification/assumptions.yaml`; anything else, including `sorryAx`, is a trust change to report
   under question 6. An unchanged textual count of `axiom` or `sorry` is not a base audit: imports,
   external declarations, and generated bodies can change the trust base without adding those
   keywords. If reusing an earlier audit, identify its exact revision; otherwise mark the missing
   comparison unverified.
7. **Run the Rust checks.** For changes to `request_state.rs`, its tests, or contracts checked by
   test vectors:

   ```bash
   cargo test -p rmcp --no-default-features --features request-state --lib
   cargo clippy -p rmcp --no-default-features --features request-state --lib -- -D warnings
   cargo +nightly fmt --check
   ```

   For a diff that claims to touch only `mod tests`, confirm that from the diff itself.
8. **Read the evidence records.** Read `verification/evidence/Sxx.md`, any
   `verification/blockers/Sxx.md`, `verification/board.yaml`, and the affected
   `verification/functions/Exx.yaml`. Compare each recorded command, exit status, and hash with
   what you ran. Plan Section 7 lists what an evidence file must contain.

## Which sections apply

Answer the eight core questions on every PR. Then select topic sections by the kind of change. A
PR that touches several kinds needs each applicable section.

| Kind of change | Typical files | Sections to apply |
| --- | --- | --- |
| Specification of one target | `<LEAN>/Specs/RequestState.lean`, `<LEAN>/Specs/CodecState.lean`, `<LEAN>/Theorems/Model/RequestState.lean` | Specification strength and error order; Status records |
| Proof of one target | `<LEAN>/Proofs/Model/RequestState/*.lean` | Specification strength; Proof maintainability; Validation |
| Adapter, source change, or re-pin | `crates/rmcp/src/model/request_state.rs`, `verification/manifest.yaml` | Extraction, adapter, and source linkage; Validation |
| Extraction or generated Lean | `<LEAN>/scripts/extract.sh`, `<LEAN>/Rmcp/*.lean`, `verification/pilot.md` | Extraction, adapter, and source linkage; External contracts |
| External contract or axiom | `<LEAN>/Rmcp/*External.lean`, `<LEAN>/Specs/External/*.lean`, `verification/assumptions.yaml` | External contracts and the trust boundary |
| Transcript, encoding, or round trip | `MacV1/MacV2`, `SealRs1/SealRs2`, `Theorems/Model/RequestStateComposition.lean` | Transcripts, encoding, and round trips; External contracts |
| Rust boundary tests | `mod tests` in `request_state.rs` | Validation; core question 8 |
| Status and evidence only | `verification/board.yaml`, `functions/*.yaml`, `evidence/`, `blockers/`, `docs/RESULTS.md` | Status records and evidence |
| CI, scripts, agents, documentation | `.github/workflows/lean-build.yml`, `<LEAN>/scripts/`, `CLAUDE.md`, `.claude/agents/`, `docs/` | Validation and CI; question 8 |
| Other extractions | `verification/host_origin/**` and similar | Extraction, adapter, and source linkage; External contracts |

## Questions to answer on every PR

1. **What exact claim is this PR meant to establish?** Identify the step, function ID, Rust
   symbol and line at the pinned commit, changed theorem, and intended observable behaviour. Do
   the title, body, and status records match the actual code? A function extracted to compile is
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
   about the extracted definition in `Rmcp/Funs.lean` (or the registered external signature), with
   the full generated name current after the latest re-extraction, not a local copy. Then check
   success, each error variant, panics, arithmetic, and external calls against the Rust source.
6. **What changed in the trust assumptions?** Use the audit and `#print axioms` results from
   procedure step 6. Inspect direct and transitive `sorry`, axioms without an approved ID, external
   declarations whose model changed, and hand edits to generated files. Determine whether an
   apparent reduction in axioms merely moved assumptions into model definitions.
7. **Can callers actually use this result?** Can the E09–E11 and round-trip proofs consume this
   theorem as stated? Does the postcondition expose the transcript, error, and output facts the
   next step needs? Is the public statement in `Theorems` phrased only with `Specs` definitions?
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
  clauses that mirror the extracted code step by step, unused hypotheses, and postconditions
  that follow from the types alone. Was the statement changed after an earlier review round in a
  way that weakens it? Did the same agent draft and prove it?

## Extraction, adapter, and source linkage

- Was generated output regenerated from the pinned toolchain and the recorded Charon arguments?
  Were `Types.lean`, `Funs.lean`, or `translation.json` edited by hand, and if so is each edit
  recorded with its reason?
- Does the extraction log show every target translated without `sorry`? Aeneas exits with code 1
  when out-of-scope bodies fail; a script that trusts the exit code either hides a failing target
  or rejects a good run. Is each remaining `sorry` body outside the target closure?
- For an adapter change, does each row of the plan's adapter table hold in the diff: same calls,
  same error values in the same order, every fallback still tried, empty-fallback check still
  before decoding, `u64::from_be_bytes(..) as i64` bit-identical to `i64::from_be_bytes`? Does
  anything outside `request_state.rs` change, or does the public API change?
- Is token byte-identity before and after the adapter shown by a committed regression test, for
  one rs1 and one rs2 token? Do the tests now cover `Expired` and `InvalidKeyId`, which the pilot's
  equivalence check did not?
- Does the `linkage` field match the decision actually taken? Under D2 option 1 a landed and
  re-pinned adapter makes functions `ORIGINAL` relative to the new pin; under option 2 every
  function the adapter touches is `ADAPTED`, with the patch and correspondence argument recorded.
- Are new `--opaque` or `--exclude` arguments justified, and are their verification consequences
  visible? An excluded item must be outside the target closure; an opaque item becomes an external
  declaration that needs a contract.
- Does a proposed fix to generated code actually match Rust, or is the problem in a theorem's
  premises or in a library model? Check the source before repairing generated code to make a
  proof work.
- For extractions outside the crate-local project (for example `verification/host_origin/`), is
  the README precise about which functions are extracted, which are opaque, and that no property
  has been proved?

## External contracts and the trust boundary

- Does each contract describe its primitive on its own terms? A contract may not assume that a
  target function is correct.
- Does the HMAC model match plan Section 4: `new` always succeeds with `⟨k, []⟩`, `update` appends,
  `finalize` is an opaque `hmacSha256` of the absorbed bytes, and `verify s t` holds iff
  `t.length = 32 ∧ t = finalize s`? Does `verify` reject short or long tags?
- Does the Base64 model match the `URL_SAFE_NO_PAD` engine, rejecting padding and non-canonical
  trailing bits? Is the law `decode (b64 x) = Ok x` the only round-trip assumed, or does a proof
  also rely on the converse, which does not hold for non-canonical input?
- Does the `dot::split` model agree with `str::split('.')` on the empty string, a string with no
  `.`, leading and trailing dots, and consecutive dots? Do E09–E11's part counts follow from it?
- Are standard-library models (`div_ceil`, `str::len`, `from_utf8`, `HashMap::get`, `Zeroizing`
  deref) value-correct for the operations used, without hidden assumptions about hashing or
  allocation? Is allocation failure an explicit assumption rather than a silent no-panic claim?
- Is the codec-state invariant no stronger than what the constructors enforce? Constructor
  correctness is out of scope, so every clause of the invariant must be checkable against the
  constructor source.
- Is every remaining axiom listed with an ID in `verification/assumptions.yaml`, and does the audit
  accept only those IDs? Prefer law-carrying structures or hypotheses over global axioms.
- Is each contract checked against concrete vectors from the real crates (RFC 4231 for HMAC,
  known Base64url values, split behaviour) in `mod tests`? These tests catch a mismatched model;
  they are not a consistency proof, and the review should not describe them as one.
- If an external declaration becomes a concrete definition, where is the justification that the
  Rust function computes it? A concrete body can make correspondence lemmas reflexive while hiding
  the implementation-to-model assumption from the axiom count.
- Does any statement or docstring claim more than the plan's scope: HMAC unforgeability,
  constant-time behaviour, correctness of the `hmac`, `sha2`, `base64`, or `zeroize` crates, or
  coverage of the public wrappers?

## Transcripts, encoding, and round trips

- Does the E05/E06 theorem state the absorbed bytes exactly, including the domain separator,
  big-endian 8-byte length prefixes, and field order? Would a transcript without a length prefix,
  or with kid and ad swapped, also satisfy it?
- Are E05/E06 stated over the abstract HMAC state they return, not over a tag?
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
- Is each round-trip theorem stated at the intended layer, about the extracted `seal_*` and
  `open_*` functions, rather than only about pure models?

## Status records and evidence

- Does the function record use the plan's vocabulary exactly, with `extraction`, `spec`, `linkage`,
  and `proof` as independent fields? Is a function called verified only when `proof: CHECKED`,
  `spec: REVIEWED`, `linkage: ORIGINAL`, and the audit shows only approved assumption IDs?
- Was `spec: REVIEWED` set by a named human spec owner, as plan Section 10 and the workflow guide
  require, rather than by an AI tool or by agreement between agents? Is AI drafting disclosed in
  the PR footer and recorded, with tool and model, in the evidence file?
- Does `board.yaml` reflect the step's real state? An accepted blocker report closes the task of
  reporting, never the function's proof. The deadline never changes a status.
- Does each evidence file record the exact commands, exit status, source and generated-file
  hashes, assumptions added, and reviewer decision? Do those hashes match what you computed?
- Does `docs/RESULTS.md` follow the plan's results template, list only actual results, and name
  open, blocked, and adapted functions as such?

## Proof maintainability and library layering

- Do the import directions hold? `Specs` imports nothing from `Proofs`, `Theorems`, or `Checks`;
  `Proofs` imports `Rmcp` and `Specs` only; `Theorems` imports only accepted proofs; nothing
  imports `Checks`. Does a draft with `sorry` sit outside the import roots?
- Is the public theorem in `Theorems` phrased only with `Specs` definitions, so its meaning does
  not depend on proof-private definitions?
- Does the file sit at the path the plan assigns (`Proofs/Model/RequestState/<Function>.lean`), and
  does the theorem use the plan's name (`<function>_spec`, `rs1_roundtrip`, …) or a recorded
  replacement once generated signatures are known?
- Is there an existing Aeneas, Mathlib, or local lemma that avoids rebuilding infrastructure? Is a
  new helper actually used? Are shared lemmas about `b64`, `dot`, or the HMAC state placed under
  `Specs/External` or a shared proof file rather than duplicated per function?
- Are flexible nonterminal tactics replaced by explicit lemma sets where practical? Are heartbeat
  increases justified and local?
- Do docstrings explain the statement, the Rust lines it covers, and its assumptions, rather than
  narrate proof development? Do they state the arithmetic domain and target width when relevant?
- Did a proof worker stay inside its assigned file? The `mcp-lean` role may not change theorem
  statements, specs, generated files, or contracts, and may not add axioms or `sorry`.

## Validation and CI

The commands are in the [procedure](#procedure). These questions interpret their results.

- Did checks use the PR's current sources and the pinned toolchain, without stale build artifacts
  masking a missing import or an unbuilt module? Was the generated Lean built in the crate-local
  project, not against an unrelated Aeneas library build?
- Does `lean-build.yml` build both `Theorems` and `Checks`, preserve failing exit codes through
  pipes, and run for fork and branch PRs? Has the audit been shown to fail on an unapproved axiom
  or `sorry` (plan S17)?
- Does a fresh clone reproduce extraction and build, with generated files matching (plan S18)?
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
  question-begging premise, an unfaithful model of the Rust behaviour, an adapter change that
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
| `model` | Core question 5; Extraction, adapter, and source linkage |
| `linkage` | Adapter behaviour, source pin, and `linkage` field |
| `trust` | Core question 6; External contracts and the trust boundary |
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
in Lean, as well as proof text and Rust test cases. Each proposal must:

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
- "This external became a definition and its axiom ID disappeared. Where is the argument that the
  Rust function computes it?"
- "The round-trip premise requires a nonempty ad. Is that intended? `seal_rs1` accepts an empty ad."
- "The record says `linkage: ORIGINAL`, but the pin still predates the adapter. Was D2 option 1
  landed?"
- "The evidence file reports exit status 0 for extraction, but Aeneas exits with 1 on this input.
  Which log was checked for the target list?"

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
Sections 8–9. The pilot ran in a scratch copy outside the repository; its results are as reported
in the plan and have not been re-run here. Add newer examples, with their PR or commit, below the
existing ones.

**Extraction is not verification.** The Host/Origin README states that its extraction "is not a
proof of the Host/Origin rejection property", that the two `parse_allowed_*` parsers are axioms,
and that the request-level `validate_dns_rebinding_headers` path failed in Aeneas. A summary that
called that PR a verification of DNS-rebinding protection would overstate it. (Q1, Q6)

**Hand edits to generated files must be recorded.** The pinned Aeneas emitted `filter_map` and
`any` fields in one `Iterator` instance that its Lean library lacks; the Host/Origin extraction
removed them from `Funs.lean` by hand and documented the edit in its README. Re-extraction without
re-applying and recording the edit changes the build result. (Extraction section; Q5)

**Exit codes do not identify which targets failed.** In the pilot's second run, Aeneas exited with
code 1 because seven out-of-scope bodies failed (`Debug`/`Display` impls, three constructors, and
`seal_at`), while all eleven targets compiled. The plan therefore requires `extract.sh` to check the
target list against the log. (Procedure step 4; Validation)

**Library models can be wrong.** The pinned Aeneas library models `i64::from_be_bytes` as taking
`Array I8`, whereas Rust takes `[u8; 8]` (blocker B6, fixed upstream in Aeneas #1355). A proof
built on that model would be about the wrong signature. The tested workaround changes source
(`u64::from_be_bytes(..) as i64`), so it carries a linkage consequence. (Q5; External contracts)

**Workarounds move the trust boundary.** Blockers B1–B3 were resolved by small opaque adapter
modules (`mac`, `b64`, `dot`). Their bodies are not extracted, so their contracts and tests become
the trust boundary. The plan describes this as narrower and more explicit than contracts on the
crate APIs, and states that the adapter "does not prove anything about it". (Q6; External
contracts)

**Equivalence evidence has gaps.** The pilot compared 9 tokens and 153 `open` results between the
original and adapted code and found them byte-identical, covering `Ok`, `IntegrityCheckFailed`,
`InvalidEncoding`, `MalformedFormat`, and `UnknownKeyId`. It did not cover `Expired` or
`InvalidKeyId`, so the plan still requires a regression test. Check the stated coverage before
treating such a comparison as complete. (Adapter checklist; Validation)

**Build against the intended library.** The pilot compiled generated Lean against an existing
Aeneas library build at `6e167c9b`, whose Lean files the plan reports as identical to the pinned
`5d08da45` apart from one added utility file. The crate-local build (B10) was still outstanding.
A green build reported against another library revision does not establish the pinned build.
(Procedure step 5; Validation)

**Arithmetic semantics depend on build profile.** The workspace sets no `overflow-checks`; Aeneas
models overflow as failure, matching debug builds only. Arithmetic theorems must therefore state
their no-overflow domain. (Specification strength; Q4)
