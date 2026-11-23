# AI review guide for Rust SDK pull requests

This guide supports a quick, evidence-based review of changes to `rmcp`,
`rmcp-macros`, examples, conformance tests, and verification work. It supplements
human review and the repository's `VERSIONING.md`, `DEPENDENCY_POLICY.md`, and
`.github/workflows/ci.yml`. A passing test or an AI comment is not an approval.

## Review procedure

1. Record the PR head, base tip, and merge base. Read the complete diff and the
   relevant files at those pinned revisions. Report only defects introduced by
   the PR. Recheck an earlier finding against the current head before repeating it.
2. Read the PR description, linked issue, previous review comments, and CI results.
   Treat author claims and check names as leads; verify the underlying behavior or
   exact command before relying on them.
3. Trace affected callers and feature gates. For a protocol change, compare the
   implementation with the applicable MCP specification revision and the older
   versions the SDK promises to support.
4. Check boundary cases and failure paths, not only the successful example. For
   async code, include cancellation, timeouts, cleanup, and concurrent requests
   when they are relevant.
5. Distinguish observed CI results, commands personally run, and work that remains
   unverified. The `!review` bot performs static inspection only.

## Questions for every PR

1. What user-visible behavior or maintenance need does the change address? Does
   the diff match that purpose and stay focused?
2. Is the implementation correct for valid, malformed, missing, repeated, and
   boundary inputs? Can a plausible wrong implementation still pass the tests?
3. Does the change preserve wire compatibility and protocol lifecycle behavior
   for every supported MCP version? Are request IDs, `_meta`, error shapes, and
   notification ordering handled consistently?
4. Does the change preserve the public Rust API under the default and non-`local`
   feature sets? Check feature dependencies, MSRV, proc macro output, and SemVer
   implications against `VERSIONING.md`.
5. Are security-sensitive decisions still made at the right boundary? Check
   authentication, authorization, Host/Origin validation, URL handling, input
   limits, and secret exposure where the diff touches them.
6. Are async resources cleaned up after errors, cancellation, and shutdown? Could
   a failed request leak a session, task, permit, or in-flight response?
7. Do tests cover the changed contract, including an important failure case?
   Are docs and examples accurate for user-facing changes?
8. What evidence supports the conclusion? Record the exact CI checks and their
   commit SHA, and identify any missing feature matrix, platform, or conformance
   coverage that matters to the finding.

## Additional checks by change type

- **Transports and HTTP:** inspect header parsing, redirects, status handling,
  response size limits, stream termination, reconnects, and session boundaries.
- **OAuth and request state:** inspect issuer and audience binding, token expiry,
  key selection, CSRF/state validation, error disclosure, and replay behavior.
- **Models and serialization:** inspect `serde` defaults, unknown fields, enum
  variants, round trips, numeric conversions, and JSON Schema output.
- **Macros:** inspect generated names, attributes, diagnostics, generic bounds,
  and compile-time failures at external call sites.
- **Dependencies and CI:** apply `DEPENDENCY_POLICY.md`; confirm the intended
  checks actually run and failures propagate. Avoid treating a skipped job as a
  successful check.
- **Aeneas and Lean:** identify the exact Rust revision and extraction settings.
  Distinguish extracted code, opaque external models, assumptions, and proved
  theorems. A generated Lean file or a successful build alone is not a proof of
  the claimed SDK behavior.

## Reporting the review

Start with a brief verdict. Report only actionable findings, ordered by severity.
Each finding should include a category (`correctness`, `compatibility`,
`security`, `tests`, `verification`, or `CI`), the head file and line, evidence,
the consequence, and a focused requested change. Do not report speculative style
preferences as defects. If no defect is established, say that no blocking finding
was found in this limited review; do not say the PR is approved or secure.

End with **Validation and unverified**. Separate observed CI status from checks
personally run and from work the review did not validate.

## Requesting a quick review

After this workflow is merged into the default branch, a repository collaborator
with write access can post exactly `!review` as a new comment on an open PR.
The bot reviews the pinned diff and posts a comment; it does not submit a GitHub
approval. If the PR head or base changes during the run, the comment is marked
outdated and another `!review` is needed. The run requires an Actions secret named
`OPENAI_API_KEY`; `CODEX_REVIEW_MODEL` is an optional Actions variable. The
workflow's review job has a 15-minute timeout and uses a read-only Codex sandbox.
Run the workflow helper's offline tests with
`node --test scripts/codex-review.test.cjs`.
