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
| `RmcpExternal` | `trusted` | Hand-written `Rmcp.TypesExternal`, `Rmcp.FunsExternal`: external models (definitions, structures, `opaque` constants; no axiom since S08–S09) | Aeneas, `Rmcp.Types` (the generated `FunsExternal` template imports it) |
| `Defs` | `specs` | Pure definitions used by statements: byte-level models, transcripts, codec-state invariant | Aeneas, Mathlib, `Rmcp`, `RmcpExternal` |
| `Proofs` | `proofs` | Spec theorems about the translated functions, their support lemmas, laws of the external models (`Proofs/External/`; consistency models only if a trusted axiom is added again) | `Rmcp`, `RmcpExternal`, `Defs` |
| `Specs` | `specs` | One spec file per Rust source file: each accepted statement restated as a `theorem` in `Theorems`, and its axioms | `Defs`, `Proofs` |

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

- No `axiom` in `trusted/` (human decision 2026-11-23). Each external function is a `def` with
  the generated name and signature, and each external type a `structure`, keeping the
  template's `@[rust_fun]` or `@[rust_type]` attribute where it has one (the template gives none
  to the opaque `rmcp` functions, `prim` and `now_ms`); never a bare `Result` axiom. What a
  model cannot compute is an `opaque` constant in the namespace `ExtModel` (`hmacSha256`,
  `sipHash13`, `nowMs`, `SerdeJsonErrorImpl`), and the external returns `ok` of it. Laws about
  the models (for example the Base64 round trip) are theorems in
  `formal/proofs/Proofs/External/`.
- Each model describes its primitive on its own terms, never by referring to a target function.
- Each model has a docstring with the Rust source it encodes (crate or `rust-src` file and lines
  at the pinned version) and its stated exceptions (panics or behaviours it does not model). The
  same model is listed in the trusted-base section of `formal/docs/STATUS.md`, and
  `formal/trusted/evidence/README.md` names the Rust tests that check it. For example:

  ```lean
  /-- [rmcp::model::request_state_wire::prim::b64_decode]: ...

  **Model:** `ok (b64Decode input)`. `URL_SAFE_NO_PAD` (`base64-0.23.1`,
  `src/engine/general_purpose/mod.rs` line 472) decodes strictly: padding, foreign bytes,
  a length `≡ 1 (mod 4)` and non-zero trailing bits are errors. -/
  def model.request_state_wire.prim.b64_decode (input : Slice Std.U8) :
      Result (Option (alloc.vec.Vec Std.U8)) := ...
  ```

## Specification Definition Guidelines

`formal/specs/Defs/` holds the definitions that statements are written in.

- `Defs/Wire.lean`: `splitOn` components, `be64`, transcripts, framing and expiry.
- `Defs/RequestState.lean`: codec outputs and error predicates.
- `Defs/CodecState.lean`: the codec-state predicate `CodecValid` enforced by the keyring
  constructors (single-key codecs unconstrained; key ids pairwise distinct), its clauses, key
  lookup, and the expected results of the opening functions E09–E11.

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
  concisely, and gives the plan ID, the Rust source path, and the line at the pinned commit
  (since the D2 fallback of 2026-11-23: the line in the patched copy, patch 01 on origin/main
  `7caec76`):

  ```lean
  /-!
  # Spec theorem for `open_rs1_at` (E09)

  Opens an `rs1` token: parses three `.`-separated parts, decodes body and tag, verifies the tag
  against the configured keys, then checks expiry.

  Source: "crates/rmcp/src/model/request_state.rs", line 620 at `<pinned commit>`
  -/
  ```

- Further details or an overview of the proof can go in other comments if useful.
- Consistency models are needed only for trusted axioms, and `trusted/` declares none since
  S08–S09 (definitions and `opaque` constants cannot prove `False`). If an axiom is added again
  (human decision), its consistency model goes in `Proofs/Consistency/<Group>.lean`, instantiating
  the opaque functions with a concrete model and proving every axiom of the group for it. Laws
  about the external models are theorems in `Proofs/External/<Group>.lean`.
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
    (associated_data : Slice U8) (now_ms : I64) (h : CodecFallbacksKnown self) :
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
- Take the codec-state invariant as a hypothesis built from the definitions in
  `Defs/CodecState.lean`, and only the clauses the function needs: `CodecFallbacksKnown self` for
  E09/E11, `FallbacksKnown keys rs1_fallbacks` for E09a, none for E10 (spec-owner decision
  2026-11-23). Composition theorems may take the whole predicate `CodecValid self`, which implies
  each clause. Do not restate a clause inline.

## Composition Theorems

Round-trip and dispatch theorems that span several functions are proved in
`formal/proofs/Proofs/Model/RequestState/Roundtrip.lean` (`frame_roundtrip` in
`Proofs/Model/RequestStateWire/Frame.lean`), and restated at the end of the spec file of the
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
- Each statement is restated as a `theorem` in the `Theorems` namespace (as in the
  curve25519-dalek fork's `ForHumans/Theorems`), with the statement text of the signed-off spec,
  proved by the spec theorem it restates (so Lean checks the restated type against the proved
  one). It has a docstring giving the plan ID and a one-line summary, and is followed by its
  axioms, checked by `#print axioms`. Names: `Theorems.<module>.<function>` without `_spec` for
  targets (`Theorems.request_state_wire.parse_rs1`,
  `Theorems.request_state.RequestStateCodec.open_rs1_at`); `Theorems.External.<original name>`
  for the laws of the external models, keeping the original name, because a shorter one could
  shadow a Rust function name that the statements mention.

  ```lean
  open rmcp.model.request_state_wire  -- for `Rs1Parts`; the function is still named in full

  /-- W08 `parse_rs1`: `Some {body, tag}` iff the token splits on `.` into
  `["rs1", body, tag]`. -/
  theorem Theorems.request_state_wire.parse_rs1 (s : Slice U8) :
      rmcp.model.request_state_wire.parse_rs1 s ⦃ (r : Option Rs1Parts) =>
        r = Defs.parseRs1 s.val ⦄ :=
    rmcp.model.request_state_wire.parse_rs1_spec s

  /--
  info: 'Theorems.request_state_wire.parse_rs1' depends on axioms: [propext, Quot.sound]
  -/
  #guard_msgs in
  #print axioms Theorems.request_state_wire.parse_rs1
  ```

  Use exactly this form: a bare `#guard_msgs in` (no options such as `drop`, `whitespace` or
  `substring`) followed by one `#print axioms` line; `scripts/lean-guard.sh` rejects any other.
  The docstring therefore matches the complete message, which prints the full name of the theorem
  (generated definitions live in `namespace rmcp`, so the name starts with `rmcp.model.`).

- Add a statement here only when its proof has no `sorry` and its specification is `REVIEWED`.

[mathlib-style]: https://leanprover-community.github.io/contribute/style.html
[mathlib-naming]: https://leanprover-community.github.io/contribute/naming.html
