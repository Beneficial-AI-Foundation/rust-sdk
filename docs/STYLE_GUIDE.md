# Style Guide

This guide covers hand-written Lean in `formal/`: `trusted/` (external models and axioms),
`specs/` (definitions and spec files), and `proofs/`. Generated files under `formal/translation/`
are not subject to it. Rust code follows the repository's `rustfmt.toml`, `clippy.toml`, and the
[contribution guide](CONTRIBUTE.MD). The process is in [`VERIFICATION.md`](VERIFICATION.md) and the
[workflow guide](WORKFLOW_AND_PR_GUIDE.md).

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

These rules are the target for merged proofs. During phase B ("complete first") a working proof
that uses flexible tactics is acceptable; phase C replaces them without changing any statement.

Do not use `native_decide` or `bv_decide` in a merged proof; see
[External functions and axioms](WORKFLOW_AND_PR_GUIDE.md#external-functions-and-axioms).

### Linters

Resolve linter warnings rather than suppressing them: every library sets `warningAsError`, so every
warning in this project's files fails the build (see
[Building and Checking](WORKFLOW_AND_PR_GUIDE.md#building-and-checking)). Do not leave
`#check`/`#eval` leftovers. The only `#print` allowed is `#print axioms` under a bare
`#guard_msgs in` in spec files. `scripts/lean-guard.sh sources` rejects the whole words
`warningAsError`, `sorry`, `sorryAx`, `admit`, `native_decide`, `bv_decide`, `skipKernelTC`,
`proofAsSorry`, `implemented_by`, `extern`, `unsafe`, `ofReduceBool`, `ofReduceNat` and
`trustCompiler`, and the `native` option of `decide`, in every Lean file under `formal/` except
`.lake/` and `formal/specs/Drafts/`; `set_option linter.<name> false` everywhere outside
`formal/translation/`, `formal/trusted/` included; and `axiom` outside `formal/trusted/` (the
unbuilt Aeneas `*_Template.lean` files in `formal/translation/` are exempt). It also rejects, in
`proofs/`, `specs/` and `trusted/` alike, anything that runs or registers a metaprogram: `#eval`,
`#exit`, `run_cmd`, `run_tac`, `run_elab`, `run_meta`, `elab`, `elab_rules`, `initialize`,
`macro`, `macro_rules`, `syntax`, `simproc`, `addDecl`, `modifyEnv`, `withOptions`, the types
`IO`, `CoreM`, `MetaM`, `TacticM` and the like, `Lean.Elab`, any `debug.` option, and attributes
such as `tactic`, `init` or `delab` (full list in `formal/README.md`). `notation`, `infix`, local
instances and `simp` attributes are allowed. Write a custom tactic out inline; a separately
reviewed tactic module is a human decision (lead decision 2026-11-22). The check is textual, so
these words are rejected in comments and docstrings too: write "placeholder" or "unproved" for
sorry, "assumption" or "postulate" for axiom, "foreign" for extern, "unchecked" for unsafe,
"grammar" or "notation" for syntax, "set up" for initialize and "input/output" for IO in prose. Only `#guard_msgs` may be written as prose in backticks
(`` `#guard_msgs` ``); see [Building and Checking](WORKFLOW_AND_PR_GUIDE.md#building-and-checking)
for the full rules.

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

`formal/lakefile.toml` declares five libraries, following plan Section 5. Each has its own
`srcDir` and explicit `roots` (no `globs`: `scripts/lean-guard.sh` allows only `name`, `srcDir`,
`roots` and `leanOptions`), so every module belongs to exactly one library. Their import
directions are fixed:

| Library | `srcDir` | Contents | May import |
| --- | --- | --- | --- |
| `Rmcp` | `translation` | Generated `Rmcp.Types`, `Rmcp.Funs` | Aeneas, `RmcpExternal` |
| `RmcpExternal` | `trusted` | Hand-written `Rmcp.TypesExternal`, `Rmcp.FunsExternal`: external models, opaque functions, axioms | Aeneas, `Rmcp.Types` (the generated `FunsExternal` template imports it) |
| `Defs` | `specs` | Pure definitions used by statements: byte-level models, transcripts, codec-state invariant | Aeneas, Mathlib, `Rmcp`, `RmcpExternal` |
| `Proofs` | `proofs` | Spec theorems about the translated functions, their support lemmas, consistency models | `Rmcp`, `RmcpExternal`, `Defs` |
| `Specs` | `specs` | One spec file per Rust source file: `recall` of each accepted statement and its axioms | `Defs`, `Proofs` |

- `Proofs` never imports `Specs`, and nothing imports `Specs`.
- A statement is phrased only with `Defs` definitions (and the translated function), so that its
  meaning never depends on a proof-private definition.
- Proof-only helpers stay in `Proofs`. Promote a helper to `Defs` only if a statement needs it.
- `formal/specs/Drafts/` belongs to no library. Draft statements live there until their proofs are
  complete.

## External models and axioms

`formal/trusted/Rmcp/FunsExternal.lean` and `TypesExternal.lean` declare everything Aeneas does not
translate (plan Section 4). Organise `FunsExternal.lean` in sections: HMAC, Base64, standard
library, clock.

- Each opaque reference function (`hmacSha256`, `b64`, `b64Decode`) is an `opaque` declaration,
  and the translated external is a `def` returning `ok` of it, never a bare `Result` axiom.
- Each axiom describes its primitive on its own terms, never by referring to a target function.
- Each axiom has a docstring giving its justification and the Rust tests that check it. The same
  axiom is listed in the trusted-base section of `formal/docs/STATUS.md`. For example (the test
  name is a placeholder):

  ```lean
  /-- `URL_SAFE_NO_PAD` decoding inverts encoding.

  Justified by the `base64` crate documentation for `Engine::decode` at the pinned version
  (`0.23.x`, checked by `scripts/aeneas-translate.sh`), and checked by the `b64_vectors` test in
  `request_state_wire.rs`. Consistency model: `Proofs/Consistency/Base64.lean`. -/
  axiom b64Decode_b64 (x : List U8) : b64Decode (b64 x) = some x
  ```

## Specification Definition Guidelines

`formal/specs/Defs/` holds the definitions that statements are written in.

- `Defs/Wire.lean`: `splitOn` components, `be64`, transcripts, framing and expiry.
- `Defs/RequestState.lean`: codec outputs and error predicates.
- `Defs/CodecState.lean`: the codec-state invariant enforced by the constructors.

Rules for definitions in `Defs`:

- Each definition has a docstring that says what it denotes, and the Rust lines (at the pinned
  commit) or plan section it models.
- Prefer mathematical objects (`List UInt8`/`List U8`, `Nat`, `Int`) over machine types, except
  where the machine width is part of the claim. State conversions explicitly, e.g. signed
  big-endian decoding of 8 bytes.
- Do not restate the implementation step by step. A specification that mirrors the translated
  code proves nothing beyond translation.
- `Defs` contains no axioms. Anything taken on trust belongs in `formal/trusted/`.

## Proof File Guidelines

There is one proof file per Rust item (`VERIFICATION.md` §8), under
`formal/proofs/Proofs/Model/RequestStateWire/` for `Wxx` and
`formal/proofs/Proofs/Model/RequestState/` for `Exx`.

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

  Source: "crates/rmcp/src/model/request_state.rs", line 620 at `<pinned commit>`
  -/
  ```

- Further details or an overview of the proof can go in other comments if useful.
- Consistency models of axioms go in `Proofs/Consistency/<Group>.lean` (`Hmac`, `Base64`,
  `HashMap`). Each one instantiates the opaque functions with a concrete model and proves every
  axiom of the group for it.
- Other translated code, if it later moves into `formal/`, mirrors the Rust module path below
  `Proofs/Model/`, for example
  `Proofs/Model/Transport/StreamableHttpServer/Tower/HostIsAllowed.lean`.

### Spec Theorem Style

State every function spec theorem with the Aeneas `⦃ ... ⦄` WP syntax of the pinned Aeneas
library. The canonical layout is below; the argument types are illustrative, so use the
generated signature from `formal/translation/Rmcp/Funs.lean`:

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
  ...
```

The statement means that the call terminates without panicking and its result satisfies the
postcondition (plan Section 3); preconditions say when that is guaranteed.

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

A draft in `formal/specs/Drafts/` uses the same layout, with the proof replaced by `sorry`; it is
never built.

### Hypothesis conventions

- Write a no-overflow domain as a named hypothesis (e.g. `(h_no_overflow : 4 * ((n + 2) / 3) ≤
  Usize.max)`), and mention it in the docstring, together with the fact that it matches debug-build
  semantics.
- Write a target-width assumption as a named hypothesis (e.g. `(h64 : System.Platform.numBits =
  64)`), used only where the claim depends on it.
- Take the codec-state invariant as a single hypothesis `(h : self.Valid)` using the definition in
  `Defs/CodecState.lean`, rather than restating its clauses.

## Composition Theorems

Round-trip and dispatch theorems that span several functions are proved in
`formal/proofs/Proofs/Model/RequestState/Roundtrip.lean` (`frame_roundtrip` in
`Proofs/Model/RequestStateWire/Frame.lean`), and recalled at the end of the spec file of the
corresponding Rust file.

- Theorem names say what the result is, following the [Mathlib naming guidelines][mathlib-naming]
  and the names of plan Section 5 (`rs1_roundtrip`, `open_at_roundtrip_rs2`, ...), rather than
  `<function>_spec`. They are not tagged `@[step]`.
- The docstring lists every premise of the round trip in words (body length, expiry, same
  associated data, key or kid conditions), and says which translated functions the theorem is
  about.
- A theorem that takes successful calls as hypotheses (`f args = ok r`) says in its docstring that
  it covers only successful calls and does not show that any call succeeds.

## Spec Files

`formal/specs/Specs/Model/RequestStateWire.lean` and `Specs/Model/RequestState.lean` are the spec
files, one per Rust source file (`VERIFICATION.md` §7). They are what a reader needs to trust the
result.

- The module docstring states the translated configuration
  (`x86_64-unknown-linux-gnu`, `--no-default-features --features request-state`), names the `Defs`
  the statements use, and lists the items of that Rust file that were not translated (plan
  Section 2.3).
- Statements appear in Rust source order, composition theorems last.
- Each statement is restated with `recall` from its proof, with a docstring giving the plan ID and
  a one-line summary, and is followed by its axioms, checked by `#print axioms`:

  ```lean
  open rmcp.model.request_state_wire  -- for `Rs1Parts`; the theorem is still named in full

  /-- W08 `parse_rs1`: `Some {body, tag}` iff the token splits on `.` into
  `["rs1", body, tag]`. -/
  recall rmcp.model.request_state_wire.parse_rs1_spec (s : Slice U8) :
      rmcp.model.request_state_wire.parse_rs1 s ⦃ (r : Option Rs1Parts) =>
        r = Defs.parseRs1 s.val ⦄

  /--
  info: 'rmcp.model.request_state_wire.parse_rs1_spec' depends on axioms: [propext, Quot.sound]
  -/
  #guard_msgs in
  #print axioms rmcp.model.request_state_wire.parse_rs1_spec
  ```

  Use exactly this form: a bare `#guard_msgs in` (no options such as `drop`, `whitespace` or
  `substring`) followed by one `#print axioms` line; `scripts/lean-guard.sh` rejects any other.
  The docstring therefore matches the complete message, which prints the full name of the theorem
  (generated definitions live in `namespace rmcp`, so the name starts with `rmcp.model.`).

- Add a statement here only when its proof has no `sorry` and its specification is `REVIEWED`.

[mathlib-style]: https://leanprover-community.github.io/contribute/style.html
[mathlib-naming]: https://leanprover-community.github.io/contribute/naming.html
