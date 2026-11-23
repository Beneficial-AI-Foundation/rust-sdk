# Reviewer's guide

## Objectives

This document gives guidelines for reviewers of PRs that add functional-correctness
specifications, external axioms, translation patches, Charon settings, and proofs for this fork of
the Rust MCP SDK. The process is in [`VERIFICATION.md`](VERIFICATION.md); the scope and targets are
defined in the [master plan](MCP_SDK_Verification_Master_Plan_EN.md). Review is a
second layer of quality control. It ensures that every specification (or proof of it) meets the
following criteria as far as possible:

- **Correctness:** as a minimal standard, specifications _must_ be counterexample free, and
  must describe the pinned Rust behaviour, including every error result and the order in which
  errors are checked. A proof does not settle this: it shows only that the code meets the
  statement. For axiomatic contracts there are no such guardrails at all.
- **Simplicity:** all other aspects being equal, a simple formulation is preferable (this also
  supports readability).
- **Readability and maintainability:** comments, deliberate whitespace, and concise statements
  help human readers understand a specification beyond the correctness established by its proof.
- **Verification performance:** CI must check every proof, so among equivalent proofs, prefer the
  one with the lowest build time.

The [workflow guide](WORKFLOW_AND_PR_GUIDE.md) allows AI-drafted specifications. They get the
same review as hand-written ones, with the additional checks in
[step 2](#2-review-ai-drafted-specifications). The checklist for AI-assisted review is in
[AI review questions](AI_PR_REVIEW_QUESTIONS.md).

Everything that must be trusted — specifications, `Defs` definitions, axioms, patches, and
`exclude`/`opaque` entries — gets at least two independent agent reviews before it reaches you
([Review and sign-off](WORKFLOW_AND_PR_GUIDE.md#review-and-sign-off)). Read those reports, but do
not treat their agreement as acceptance: the human sign-off is yours. Proofs and the generated
translation need no trust review: Lean checks the former and the translation CI regenerates the
latter.

## Recommended steps for reviewers

We assume the typical review deals with a PR that covers one plan step for a single function
(`Wxx`, `Exx`, or Phase 2 `Mxx`, `Txx`, `Axx`), provides a specification (or its proof, once the specification is signed off), and
stays near the recommended 500 LOC cap.
For other kinds of PR use the steps below as guidelines, with your own judgement.

### 1. Check for specification correctness

Compare the statement with the Rust source at the pinned commit and with plan Section 3. Since
the D2 fallback of 2026-11-23 the target files are those of the patched copy (the output of
`scripts/apply-patches.sh` in `.llbc/work/`; `request_state_wire.rs` exists only there). In
particular:

- Does it cover the `Ok` case and every `Err` variant, in the Rust order of checks?
- Are boundaries exact (e.g. `now_ms == expiry` is accepted, expiry `0` means no expiry)?
- Is any arithmetic domain or target-width hypothesis stated, and no stronger than needed?
- Would a plausible wrong implementation also satisfy it?

You can spend less effort on proof details when the PR introduces a `sorry`-free proof. You cannot
skip the statement check.

For external models in `formal/trusted/Rmcp/` (definitions, structures and `opaque` constants;
no axiom since S08–S09, human decision 2026-11-23), inspect the cited sources (RFC, crate
documentation, pinned crate source) to make sure they are legitimate and that the formulation was
correctly transcribed. `#print axioms`, the `#guard_msgs` lists and `axioms.lock` do not show
these models, so this review is the only check of a changed model. Check that:

- each definition, structure and `opaque` constant is listed in the trusted-base section of
  `formal/docs/STATUS.md`, and the Rust test vectors cited for it in
  `formal/trusted/evidence/README.md` exist and pass;
- its docstring cites the Rust source it encodes (file and lines at the pinned version) and
  states its exceptions;
- no external is a bare `Result` axiom (`axiom f : … → Result T`); it is an exact model or `ok` of
  an opaque value;
- no model is stated about a function whose Lean type merges distinct Rust types;
- the model does not refer to a target function;
- `trusted/` declares no `axiom`; an axiom added again needs a human decision and a consistency
  model in `formal/proofs/Proofs/Consistency/`.

For a translation patch in `formal/trusted/patches/`, check that its header states the change, why
it is needed, and why the behaviour is unchanged; that it is minimal, with one concern; and that
`patched-tests.yml` passes. For a new `exclude` entry, check that no target depends on the item;
for a new `opaque` entry, check that the item truly cannot be translated and has no useful Rust
model, since it adds an external model to the trusted base.

Comments about correctness are _blocking_.

### 2. Review AI-drafted specifications

The PR footer lists AI-drafted artifacts. For each one:

- Check every clause against the Rust lines or plan section it cites. A clause without a cited
  source, or whose source does not say what the clause says, is _blocking_.
- Look for clauses that restate the implementation instead of specifying it, for hypotheses that
  are never used, or that exclude valid inputs, and for postconditions that are vacuous or follow
  from the types alone.
- Check that the statement was not weakened to make a proof go through: compare it with the
  version accepted in an earlier round, if any.
- Check that the drafting agent is not also the prover or the AI reviewer of the same statement.

Only a named human spec owner may accept the specification and set `spec: REVIEWED` in
`formal/docs/functions/<ID>.yaml`. Check that `spec_reviews` lists at least two independent agent
reviews, none by the drafter. Agreement between AI tools, or an AI review with no findings, does
not count as acceptance.

### 3. Assess the level of abstraction

Unless a specification is externally motivated, there is usually some freedom in its exact
formulation. Consider a function `f` returning the `Nat` value `r = 42`. The same function could
have any of these specifications:

- `r > 1`
- `r != 0 /\ r % 2 = 0`
- `r = 42`

All are correct, and each is stronger than the previous one (it implies it). Which to choose
usually depends on several factors:

- **Upstream requirements.** In this project the later steps are known in advance: the codec
  targets build on the public wire theorems (for example E09–E11 on W07–W11 and E01), and the
  round trips of S15 build on E07–E11. A specification must give
  those steps what they need (transcripts, exact output format, error results), but need not go
  further. Functions that may be called from outside the known call sites should have
  specifications that make no assumptions about their callers.
- **Ease of proof.** Weaker specifications are often easier to prove, both for people and for
  the machine, and the difference can affect build time. If a proof is particularly expensive,
  check whether a weaker statement would still serve its callers.

A specification should not simply restate the implementation (except for very trivial
functions). Specifications should use mathematical abstractions rather than implementation
primitives. For example, state a MAC transcript as a byte-list concatenation
(`DOMAIN_V1 ++ be64 (len ad) ++ ad ++ body`) rather than as a sequence of `update` calls, and
state expiry decoding as a signed big-endian integer rather than as `from_be_bytes` on a slice.

Comments about the level of abstraction _may_ be _blocking_ or _non-blocking_, according to
judgement.

### 4. Check linkage, trust, and status records

- Confirm that the theorem is about the translated function in
  `formal/translation/Rmcp/Funs.lean`, with its current generated name, and that all three CI
  workflows pass on the head commit (translation not stale, Lean build with the
  `scripts/lean-guard.sh` checks, patched tests).
- If `formal/trusted/translation-pins.txt` changes (a trusted item): does its sha256 equal the `Funs.lean` that
  `scripts/aeneas-translate.sh` regenerates (and `aeneas-translation.yml` reproduces)? Is each pinned line, read in
  context, a line where Lean reads the pinned word inside a string literal (no open string or comment before it)? Is
  every new entry needed (a word the translation really emits)?
- Read the `#guard_msgs` axiom lists in the spec files. Every axiom outside `propext`,
  `Classical.choice`, and `Quot.sound` must be in the trusted-base section of
  `formal/docs/STATUS.md`. A changed list is a trust change and must be named in the PR footer.
  The lists do not show the external models; a diff of `formal/trusted/` is a trust change
  too, and a proof may use a model only once S08/S09 are signed off.
- Check that the hand-written Lean (`proofs/`, `specs/`, `trusted/`) has no metaprogramming:
  no `run_cmd`, `run_tac`, `#eval`, `elab`, `macro`, `syntax`, `initialize`, `addDecl`,
  `modifyEnv`, `simproc`, metaprogram attributes (`tactic`, `init`, `delab`, ...) or the like,
  and no indirect route to one (for example an Aesop rule that runs a tactic definition).
  `scripts/lean-guard.sh sources` bans these words as defence in depth, but its list is textual
  and incomplete, and code run during `lake build` could forge the build output that CI audits
  (`formal/README.md`, "What CI checks"). A proof that needs a custom tactic writes it out inline;
  a custom tactic needs a separately reviewed module, which is a human decision (lead decision
  2026-11-22).
- Check that the function record and board use the vocabulary of plan Section 6 and do not
  overstate the result. A function is "verified" only when `proof: CHECKED`, `spec: REVIEWED`,
  `linkage: ORIGINAL`, and its axioms are all in the trusted base. For a Phase 2 target (`Mxx`,
  `Txx`, `Axx`), `ORIGINAL` additionally requires `scripts/check-original-linkage.sh` to pass on
  the head commit (plan Section 19); before S22 lands, a record's `ORIGINAL` is only pending.

Comments that show an overstated status or an unapproved assumption are _blocking_.

### 5. Observe performance

Check the build time of the changed proof files on the head commit, and compare it with the base
when shared files changed. Not all performance decreases are avoidable, and not all avoidable
decreases are worth fixing immediately. Use your judgement to decide whether to:

- accept the PR as is,
- accept the PR now, but open an issue to revisit performance later, or
- block the PR until it is fixed.

### 6. Comment freely

Comment on the specifications without reservation, including:

- requests for adding or changing comments,
- recommendations for new definitions in `Defs`,
- requests for generalizing proof chunks into shared lemmas,
- recommendations for reusing existing spec code or external models,
- incompatibilities with the [style guide](STYLE_GUIDE.md),
- etc.

These comments are generally _non-blocking_, and the author may act on them at their discretion.
They may be made _blocking_ if the problem is particularly serious, especially for chunk
generalization and code reuse.

During phase B the rule is "complete first" (plan Section 8): a working proof is acceptable, and
proof-style comments (flexible tactics, missing shared lemmas) are non-blocking unless the proof is
fragile enough to break CI. Phase C addresses them without changing any statement.

Even when only adding comments, use "Submit review > Comment" rather than adding each comment
individually.
