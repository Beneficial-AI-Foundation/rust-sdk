# Style Guide

This guide covers hand-written Lean in the crate-local project `crates/rmcp/lean/` (written
`<LEAN>` below). Generated files (`Rmcp/Types.lean`, `Rmcp/Funs.lean`) are not subject to it.
Rust code follows the repository's `rustfmt.toml`, `clippy.toml`, and the
[contribution guide](CONTRIBUTE.MD).

## General Style Guidelines

We follow the [Mathlib style guide][mathlib-style], with some additions for the verification
patterns we use.

### Header and Imports

File headers of hand-written Lean files should be of the form:

```lean
/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Cool
-/
```

- The copyright holder is the author or their current employer.
- Add anyone who has made significant contributions to the file to the author list, in the order
  in which they first edited it. There are no strict rules on what qualifies: list the people we
  would ask about the design or development of the file.
- AI tools cannot be listed as authors, including when they drafted the specification or proof;
  disclose AI drafting in the PR instead (see the
  [workflow guide](WORKFLOW_AND_PR_GUIDE.md#ai-contributions)).

### Avoiding Flexible Tactics

Flexible (non-terminal) tactics make proofs fragile and harder to maintain. Avoid them as much as
possible:

- **`simp`**: use `simp?` to obtain the explicit lemma list, then replace it with
  `simp only [...]`. This makes the proof deterministic and resistant to changes in the simp set.
- **`simp_all`**: same rule; use `simp_all?` to obtain `simp_all only [...]`.
- **`grind`**: prefer more targeted alternatives (`omega`, `decide`, `bv_omega`, explicit
  rewriting) where feasible.
- **`exact?`** / **`apply?`**: use these *interactively* to discover the right lemma, then replace
  them with the explicit `exact` or `apply` call.

When a flexible tactic is genuinely the best option (e.g. a `simp` that closes a goal and whose
lemma list would be impractically long), document why in a short comment.

Do not use `native_decide`; see [Proof cheats](WORKFLOW_AND_PR_GUIDE.md#proof-cheats).

### Linters

Resolve linter warnings rather than suppressing them. Do not leave `#check`/`#eval`/`#print`
leftovers, and do not use `set_option linter.* false` without a justification documented in a
comment.

### Heartbeats

Keep `set_option maxHeartbeats` increases to the minimum needed, and scope them to a single
declaration with `set_option ... in`. Use multiples of **200000** as the standard increment (e.g.
400000, 800000). If a proof needs a very large budget, split it into helper lemmas.

### Formatting

- Limit all lines to 100 characters.
- In multi-line comments, wrap only when necessary: use as much of the 100-character limit as
  possible before breaking.
- List imports immediately after the file header, without empty lines.
- Name definitions and theorems (except function spec theorems) following the
  [Mathlib naming guidelines][mathlib-naming].

## Library layering

The project has four libraries, following plan Section 5. Their import directions are fixed:

| Library | Contents | May import |
| --- | --- | --- |
| `Specs` | Pure definitions used by statements: byte-level models, transcripts, `b64`, HMAC state, codec-state invariant | `Aeneas`, Mathlib, `Rmcp.Types` |
| `Proofs` | Spec theorems about the extracted functions and their support lemmas | `Rmcp`, `Specs` |
| `Theorems` | Public, readable restatements of accepted results | `Proofs`, `Specs` |
| `Checks` | Axiom and `sorry` audit of `Theorems` | `Theorems` |

- `Specs` imports nothing from `Proofs`, `Theorems`, or `Checks`, and nothing imports `Checks`.
- A public theorem in `Theorems` is phrased only with `Specs` definitions, so that its meaning
  never depends on a proof-private definition.
- Proof-only helpers stay in `Proofs`. Promote a helper to `Specs` only if a statement needs it.

## Specification Definition Guidelines

`<LEAN>/Specs/` holds the definitions that statements are written in.

- `Specs/RequestState.lean`: framing, expiry, lengths, error predicates for the codec.
- `Specs/CodecState.lean`: the codec-state invariant enforced by the constructors.
- `Specs/External/<Primitive>.lean`: one file per external contract (`Hmac`, `Base64`, `Str`).

Rules for definitions in `Specs`:

- Each definition has a docstring that says what it denotes, and the Rust lines (at the pinned
  commit) or plan section it models.
- Prefer mathematical objects (`List UInt8`/`List U8`, `Nat`, `Int`) over machine types, except
  where the machine width is part of the claim. State conversions explicitly, e.g. signed
  big-endian decoding of 8 bytes.
- Do not restate the implementation step by step. A specification that mirrors the extracted
  code proves nothing beyond translation.
- An external contract describes its primitive on its own terms, never by referring to a target
  function. Each axiom it introduces names its ID from `verification/assumptions.yaml` in its
  docstring. In this illustrative example, the ID and test name are placeholders:

  ```lean
  /-- `URL_SAFE_NO_PAD` decoding inverts encoding.

  Assumption `A-B64-ROUNDTRIP` (`verification/assumptions.yaml`). Justified by the `base64`
  crate documentation for `Engine::decode` at the pinned version, and checked by the
  `b64_vectors` test in `request_state.rs`. -/
  axiom b64_decode_encode (x : List U8) : decode (b64 x) = .ok x
  ```

## Spec Theorem File Guidelines

Each target function `Exx` has one proof file under `<LEAN>/Proofs/Model/RequestState/`.

- The file holds the function's spec theorem together with any lemmas needed only for its proof.
  Lemmas usable elsewhere go in a shared file (e.g. `Proofs/Model/RequestState/Common.lean`).
- The file is named after the function in UpperCamelCase. E.g., for `open_rs1_at` the file is
  `OpenRs1At.lean`. File names are fixed by the table in plan Section 5.
- The file contains a module docstring immediately after the imports. It explains the function
  concisely, and gives the plan ID, the Rust source path, and the line at the pinned commit:

  ```lean
  /-!
  # Spec theorem for `open_rs1_at` (E09)

  Opens an `rs1` token: parses three `.`-separated parts, decodes body and tag, verifies the tag
  against the configured keys, then checks expiry.

  Source: "crates/rmcp/src/model/request_state.rs", line 620 at `0e2396f`
  -/
  ```

- Further details or an overview of the proof can go in other comments if useful.
- Other extracted code (e.g. `verification/host_origin/`) mirrors the Rust module path below
  `Proofs/Model/`, for example
  `Proofs/Model/Transport/StreamableHttpServer/Tower/HostIsAllowed.lean`.

### Spec Theorem Style

State every function spec theorem with the Aeneas `⦃ ... ⦄` WP syntax of the pinned Aeneas
library. The canonical layout is below; the argument types are illustrative, so use the
generated signature from `Rmcp/Funs.lean`:

```lean
/-- **Spec theorem for `rmcp::model::request_state::RequestStateCodec::open_rs1_at`**

Concise natural language description of the spec, including its arithmetic domain and target
width where relevant. -/
@[step]
theorem open_rs1_at_spec (self : RequestStateCodec) (sealed : Str)
    (associated_data : Slice U8) (now_ms : I64) (h : self.Valid) :
    open_rs1_at self sealed associated_data now_ms ⦃ (result : Result (Vec U8) Error) =>
      post_condition_1 ∧
      post_condition_2 ⦄ := by
  sorry
```

- Add the attribute `@[step]` so that the Aeneas `step` tactic can use the theorem in callers.
  Start a new line after the attributes.
- Name the theorem after the function with the suffix `_spec`. Its identifier must be the __full
  generated name__ of the function with that suffix.
- Open namespaces so that the identifier prefix does not clutter the statement while the theorem
  identifier is still the full name. I.e., for a spec theorem for
  `rmcp.model.request_state.RequestStateCodec.open_rs1_at`, open
  `namespace rmcp.model.request_state.RequestStateCodec` earlier in the file and `end` it later.
- Put arguments and preconditions (`(a : argType)`, `(h : pre_condition)`, ...) after the name and
  on following lines. Name the arguments exactly like the parameters of the Rust function.
- Immediately after the main `:` of the theorem, start a new line with the function application
  and the WP binder: `fun_name a b ⦃ (result : resultType) =>`.
- Always give `result` its type; this needs brackets to parse.
- Write postconditions as a conjunction `post_condition_1 ∧ post_condition_2 ∧ ...` inside
  `⦃ ... ⦄`. When the function returns a Rust `Result`, cover the `Ok` case and every `Err` case,
  for example with a `match result with` whose arms are listed in the Rust order of checks.
- Indentation:
  - `@[step]` tag and `theorem fun_name_spec` line: 0 spaces
  - arguments, preconditions, and the line with the function application: 4 spaces
  - postconditions `post_condition_i ∧`: 6 spaces
  - proof body: 2 spaces

### Hypothesis conventions

- Write a no-overflow domain as a named hypothesis (e.g. `(h_no_overflow : 4 * ((n + 2) / 3) ≤
  Usize.max)`), and mention it in the docstring, together with the fact that it matches debug-build
  semantics.
- Write a target-width assumption as a named hypothesis (e.g. `(h64 : System.Platform.numBits =
  64)`), used only where the claim depends on it.
- Take the codec-state invariant as a single hypothesis `(h : self.Valid)` using the definition in
  `Specs/CodecState.lean`, rather than restating its clauses.

## Composition Theorem File Guidelines

Round-trip and dispatch theorems that span several functions go in
`<LEAN>/Theorems/Model/RequestStateComposition.lean`.

- Theorem names say what the result is, following the [Mathlib naming guidelines][mathlib-naming]
  and the names of plan Section 5 (`rs1_roundtrip`, `open_at_roundtrip_rs2`, ...), rather than
  `<function>_spec`. They are not tagged `@[step]`.
- The docstring lists every premise of the round trip in words (body length, expiry, same
  associated data, key or kid conditions), and says which extracted functions the theorem is
  about.
- A theorem that takes successful calls as hypotheses (`f args = ok r`) says in its docstring that
  it covers only successful calls and does not show that any call succeeds.

## Public Theorem Files

`<LEAN>/Theorems/Model/RequestState.lean` restates each accepted `Exx` spec theorem for readers.

- Each restatement is a theorem whose proof is the corresponding `Proofs` theorem, with a
  docstring giving the plan ID, the Rust function, the assumptions it depends on (by ID), and what
  it does not claim (plan Section 1).
- Add a theorem here only when its proof has no `sorry` and its specification is `REVIEWED`.

[mathlib-style]: https://leanprover-community.github.io/contribute/style.html
[mathlib-naming]: https://leanprover-community.github.io/contribute/naming.html
