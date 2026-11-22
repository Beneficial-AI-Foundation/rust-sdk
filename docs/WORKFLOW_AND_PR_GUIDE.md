# Operational Workflow

This guide covers the formal verification work in this fork of the Rust MCP SDK: the crate-local
Lean project `crates/rmcp/lean/` (written `<LEAN>` below), the records under `verification/`, and
the extraction under `verification/host_origin/`. The scope, targets, steps, and status vocabulary
are defined in the [master plan](MCP_SDK_Verification_Master_Plan_EN.md). Ordinary SDK changes
follow the [contribution guide](CONTRIBUTE.MD). See also the [style guide](STYLE_GUIDE.md), the
[reviewer guide](REVIEWER_GUIDE.md), and the [AI review questions](AI_PR_REVIEW_QUESTIONS.md).

## Do not Modify Auto-generated Files

**Never edit** `<LEAN>/Rmcp/Types.lean`, `<LEAN>/Rmcp/Funs.lean`, or `translation.json` by hand,
except for an unavoidable workaround for a known Aeneas defect. Each such edit must be:

- the smallest change that makes the file compile,
- recorded with its reason in `verification/pilot.md` (or the step's evidence file), and
- re-applied by `scripts/extract.sh` rather than by hand after each extraction.

`Rmcp/TypesExternal.lean` and `Rmcp/FunsExternal.lean` start as copies of the generated
`*_Template.lean` files and are then edited by hand; see [Proof cheats](#proof-cheats).

**Never change** production code in `crates/rmcp/src/model/request_state.rs` as part of a
verification PR. The only exceptions are:

- the reviewed behaviour-preserving adapter of plan Section 9, landed as its own PR under the D2
  decision, and
- new Rust tests inside its private `mod tests` (plan step S16).

Every change to that file changes its SHA-256. Record the new hash in `verification/manifest.yaml`
in the same PR, and re-run extraction. Re-extraction invalidates earlier proof evidence for every
affected function.

If the translation fails or produces unusable output, do not edit generated Lean to work around
it. Instead:

1. try `--opaque` or `--exclude` arguments in `scripts/extract.sh`, if the item is outside the
   target closure or can be covered by a contract;
2. otherwise record a blocker in `verification/blockers/Sxx.md` with a minimal reproducer, and
   propose a source adapter as a separate PR.

Then re-extract. To learn how Aeneas translates Rust into Lean, see the
[Aeneas documentation](https://github.com/AeneasVerif/aeneas/tree/main/documentation).

## Pinned toolchain

Use only the toolchain recorded in `verification/manifest.yaml`: at the time of writing Charon
`0.1.235`, Aeneas `5d08da45`, Rust `nightly-2026-06-01`, and Lean `4.31.0`. Changing any pin is its
own PR. That PR re-extracts all targets, rebuilds all proofs, and records the result in an
evidence file.

## Extraction

Run extraction from `<LEAN>`:

```bash
./scripts/extract.sh
```

Aeneas exits with code 1 while out-of-scope bodies fail to translate. A run is acceptable only if
the Aeneas log shows that no target function is among the failures. Check the log, not the exit
code. Commit the regenerated files together with the source change that caused them.

## Updating the Import Roots after Adding, Removing, or Renaming `.lean` Files

The import roots are `<LEAN>/Specs.lean`, `Proofs.lean`, `Theorems.lean`, and `Checks.lean`. They
list only accepted modules, so they are maintained by hand rather than generated:

- add a module to `Specs.lean` or `Proofs.lean` when its PR is accepted;
- add a public statement to `Theorems.lean` only when its proof has no `sorry`;
- keep drafts with `sorry` outside the import roots.

The import direction rules are in [Library layering](STYLE_GUIDE.md#library-layering).

## Building and Checking

```bash
cd crates/rmcp/lean
lake build
lake build Theorems
lake build Checks          # axiom and sorry audit; must pass in CI
```

For Rust-side changes:

```bash
cargo test -p rmcp --no-default-features --features request-state --lib
cargo clippy -p rmcp --no-default-features --features request-state --lib -- -D warnings
just fix                   # fmt and clippy fixes, see CONTRIBUTE.MD
```

## Status Records and Evidence

Every PR that advances a plan step updates the records under `verification/` in the same PR:

- `board.yaml`: task state (`NOT_STARTED`, `IN_PROGRESS`, `ACCEPTED`, `BLOCKED`, `DEFERRED`);
- `functions/Exx.yaml`: the four independent fields `extraction`, `spec`, `linkage`, and `proof`;
- `evidence/Sxx.md`: exact commands, exit status, source and generated-file hashes, assumptions
  added, and the reviewer decision;
- `blockers/Sxx.md`: written on failure, with a minimal reproducer.

Only a human may set `spec: REVIEWED` or move a task to `ACCEPTED`; see
[AI contributions](#ai-contributions). A deadline never changes a status.

## PR Workflow and Formatting

All verification PRs must advance a step (`Sxx`) of the master plan, or close an open issue in the
project, unless special circumstances are justified.

Whenever possible, a PR should cover exactly one step and one function (`Exx`). Keep its scope as
small as possible, ideally not exceeding ~500 LOC of hand-written Lean and Rust. Regenerated
extraction output, refactoring, and documentation do not count towards that limit.

Keep these kinds of change in separate PRs:

- a source adapter or re-pin (production Rust change),
- a re-extraction,
- a specification,
- a proof of an already accepted specification.

A specification and its proof may share a PR only if the specification is reviewed first; see
[Specifications before proofs](#specifications-before-proofs).

Discuss with the others working on the project before starting a PR, to avoid duplicate work.
The board in `verification/board.yaml` records who owns each task.

PRs are reviewed when marked as ready (i.e., not a draft) and all checks have passed. After the PR
is created (or marked as ready), hold off on meaningful changes until after the review, so that
reviewers do not look at outdated code. After review the author is responsible for merging the
accepted PR, and is expected to do so promptly.

The expected format for PR title, body, and footer is:

**Title format:** verification PRs name the step, function ID, and Rust function, for example
"S06 E01: specify and prove `open_authenticated_body` in `request_state.rs`". Other PR titles use
imperative present tense ("add" not "added") and no trailing period.

**Body format:**

- The first paragraph must start with "This PR". Use imperative present tense.
- Include motivation, and contrast with previous behaviour where relevant.
- Do NOT use markdown headings (## Summary, ## Test plan, etc.) in PR bodies.
- Include the full Rust name of each function the PR concerns (e.g.
  `rmcp::model::request_state::RequestStateCodec::open_rs1_at`) so that automation can find it.
- State the commands run on the head commit and their results.

**Footer format:** a footer is mandatory and must contain:

- **Breaking changes (if any):** changes to an accepted specification, contract, assumption ID,
  or public theorem name, each with justification and the consumers it affects.
- **AI disclosure:** one line per AI-drafted artifact; see [AI contributions](#ai-contributions).
- **Referencing issues:** closed issues on a separate line prefixed with `Closes`, e.g.
  `Closes #123, #456`.

**Labels:** PRs are encouraged, but not required, to use the same labels as the issues they close.

## Proof cheats

- **External functions.** Functions that are not translated (the opaque `mac`, `b64`, and `dot`
  adapter modules; `zeroize`, `base64`, `chrono`, `serde_json`; standard-library operations
  without an Aeneas model) are declared in `Rmcp/FunsExternal.lean` as `noncomputable opaque`
  signatures, never as `axiom`. A signature carries no assumption.
- **Contracts on external functions.** Their behaviour is stated separately, in
  `<LEAN>/Specs/External/`, following plan Section 4. Prefer law-carrying structures or
  hypotheses over global axioms. Each remaining axiom:
  - must have an ID in `verification/assumptions.yaml`;
  - must carry a docstring naming that ID and its justification (RFC, crate documentation, or
    pinned crate source);
  - must be checked against concrete vectors from the real crate in `mod tests` where possible.
- **The audit.** `lake build Checks` fails on any axiom outside `propext`, `Classical.choice`,
  `Quot.sound`, and the approved IDs.
- **`sorry`.** CI flags any PR that introduces `sorry` reachable from `Theorems`. Depending on
  the property:
  - for a placeholder for a proof to be completed later, keep the file outside the import roots,
    open an issue, and link the issue number in a TODO comment next to the `sorry`;
  - for an externally justified property, use an approved `axiom` instead.
- **Compiler-trusting tactics.** Do not use `native_decide`; it adds compiler trust that the audit
  would have to approve. Any exception needs an assumption ID and an issue.

## Performance

All PRs are expected to consider their impact on verification and CI time. Report the build time
of changed proof files in the PR body when it exceeds a few seconds, and justify regressions.

## AI contributions

AI tools, including the Claude agent roles of plan Section 10, may draft specifications, proofs,
contracts, tests, and records. The human submitting the PR is responsible for all of its contents.

### Specifications

AI-drafted specifications are allowed, under these conditions:

1. **Disclosure.** The PR footer lists each AI-drafted artifact, for example
   `AI-drafted: open_rs2_at_spec statement; Specs/External/Base64.lean contract`. Record the tool
   and model in the step's evidence file.
2. **Grounding.** Each drafted clause cites the Rust lines at the pinned commit, or the section of
   plan Section 3 or 4, that it encodes. A clause with no source is a defect, not a design choice.
3. **No self-acceptance.** An AI may not set `spec: REVIEWED`, mark a task `ACCEPTED`, or approve
   a PR. A named human spec owner reviews every AI-drafted specification against the Rust source,
   following the [reviewer guide](REVIEWER_GUIDE.md), before any proof of it is accepted. Two
   agents agreeing is not a review.
4. **Separation of roles.** The agent that drafted a specification may not prove it in the same
   session, and may not be the AI reviewer of it. A proof worker that finds a drafted
   specification false returns a counterexample; it does not weaken the statement.
5. **Contracts and assumptions.** AI-drafted contracts and assumption entries follow the same
   rules. In addition, each new axiom ID needs explicit approval from the spec owner in the PR
   review.

### Specifications before proofs

A specification is reviewed before it is proved. A PR may contain both only if the specification
was accepted in an earlier review round on that PR, and was not changed afterwards to make the
proof go through. Any change to an accepted statement re-opens its review.

### Proofs

AI-generated proofs are welcome if they comply with the [style guide](STYLE_GUIDE.md) and this
document. The proof worker edits only its assigned file under `<LEAN>/Proofs/`. It may not change
theorem statements, specifications, generated files, or contracts, and may not add axioms or
`sorry`.

### Authorship

AI tools are never listed as authors in Lean file headers; see the
[style guide](STYLE_GUIDE.md#header-and-imports). Use the commit trailer convention of the
repository for attribution.
