# Review dossier — S07 completed spec: E02 `RequestStateCodec.b64_len`

Status: **completed and staged, awaiting your review** (2026-11-23). Statement signed off by the spec
owner (S05); proof checked by Lean; reviews finalized with no open error. Not incorporated: the proof
is in `formal/proofs/Proofs/Model/RequestState/B64Len.lean`, the spec-file content is staged in
`formal/specs/Drafts/Staged/RequestState.lean`, the statement remains in
`formal/specs/Drafts/RequestState.lean`, record E02 says `proof: OPEN` with a `# proof staged` comment.

## Statement

```lean
recall rmcp.model.request_state.RequestStateCodec.b64_len_spec (len : Std.Usize)
    (h_no_overflow : b64Len len.val ≤ Usize.max) :
    rmcp.model.request_state.RequestStateCodec.b64_len len ⦃ (result : Std.Usize) =>
      result.val = b64Len len.val ⦄
```

- Rust: `RequestStateCodec::b64_len` — `crates/rmcp/src/model/request_state.rs` lines 725–727 (at
  `adce319`), which calls `request_state_wire::b64_len` (W01, lines 33–36).
- Proof: `formal/proofs/Proofs/Model/RequestState/B64Len.lean` — `unfold b64_len; step*` using the
  W01 theorem `rmcp.model.request_state_wire.b64_len_spec` (staged S06, completed); no W function is
  unfolded (checked on the kernel proof term by a reviewer).
- `#print axioms`: `[propext, Classical.choice, Quot.sound]` — no trusted or native-code axiom.

## Verification (arguments)

- Premise `b64Len len.val ≤ Usize.max` is exactly the no-overflow domain: the translated function
  fails iff it is violated (largest 64-bit input 13835058055282163709 accepted, +1, +2, +3 and
  `usize::MAX` fail); equivalent bound `len ≤ 3 * (Usize.max / 4)` proved for every width by `omega`.
- Evaluated on n = 0…999 against Rust's `div_ceil(3) * 4`; non-vacuous (len = 5 gives 8).
- Usable by callers: inside E07's capacity prefix, `step*` discharges E02's premise automatically.
- Statement identity: draft = staged `recall` = proof by text (embedded checker, 1/1 and 3/3) and by
  elaborated type (`Expr ==`, pp.all).
- Simulated incorporation (E02 with the W batch): `lake build`, `sources`, `build-log`, `axioms`
  all pass (after the docstring word fix below; 1059 constants, kernel replay accepted).

## Review history (arguments and counterarguments)

- **Spec (S05):** drafted, 2 review rounds + E-batch round 3 (verify/refine), 5 independent reviews
  of the E batch in total, no blocking; signed off by you 2026-11-23.
- **Proof (S07) round 1:** two independent reviewers, no blocking. Raised and resolved: incorporation
  check listed after the file move → step 0; dependency list of the placeholder error type was
  overstated → corrected (E02 does not reach it); long expected-text lines → wrapped (bare
  `#guard_msgs` still strict: 4 negative tests fail as they should); docstring completeness
  (overflow-checks, `now_ms` opaque, serde) → added; unused imports → trimmed.
- **Proof (S07) round 2 (confirming):** one blocking — a new docstring clause contained a word the
  guard bans outside `trusted/`, which would fail `sources` after the move → fixed by the lead and
  pre-checked at the final path (no banned words); E02-only incorporation details → spelled out in
  `formal/docs/evidence/S07.md`.

## How to incorporate

Together with or after the W batch (S07 imports S06 modules): `formal/docs/evidence/S07.md`,
"E02-only variant" plus "Clarifications to the E02-only variant" (step 0 text check and guard
pre-check before any move), and `formal/docs/review/W-batch-incorporation.md` for the W batch.

E01 and E03 are proved too, but not completed: they reach the placeholder type
`serde_json.error.Error` until S08/S09 (in progress) replaces it with a non-axiom declaration.
