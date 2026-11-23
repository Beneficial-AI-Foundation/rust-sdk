# Verifying Rust in Lean with Aeneas

This describes how we verify a Rust crate in Lean 4. The Rust code is translated to Lean by
[Charon](https://github.com/AeneasVerif/charon) and [Aeneas](https://github.com/AeneasVerif/aeneas).
We state specs for the public API and prove them against the translation.

This is the simplest version of the process: one crate, translated for **a single target**. (For
the multi-target version, where several configurations are translated and merged, see
`curve25519-dalek-fork`.)

## Layout

Everything about the verification lives under one top-level folder, `formal/`, organised by
what an auditor does with each part. Only the Charon settings (in `Cargo.toml`), the two scripts
and the CI workflows live outside it.

```
Cargo.toml                    [package.metadata.charon]: what Charon translates, excludes, opaque
scripts/aeneas-install.sh     downloads the pinned charon + aeneas binaries into .aeneas/
scripts/apply-patches.sh      copies the crate into .llbc/work/ and applies the patches
scripts/aeneas-translate.sh   calls apply-patches.sh, then translates the copy
.github/workflows/            CI: translation current, Lean builds, patched copy passes its tests
formal/
  README.md                   minimal: where each part lives, and what must be trusted
  docs/STATUS.md              coverage, trusted-base details, bugs found, open items
  lakefile.toml               the Lean project (Lake root); pins the Aeneas version
  lean-toolchain              copied from the pinned Aeneas release by the install script
  lake-manifest.json
  trusted/                    READ ALL OF IT: everything taken on trust
    patches/*.patch           local Rust edits that work around translation problems
    <Crate>/                  hand-written FunsExternal.lean, TypesExternal.lean (models, axioms)
    evidence/                 tests backing the axioms that are not part of the build
  specs/                      READ ALL OF IT: what is claimed
    Defs/ Defs.lean           definitions needed to state the specs
    Specs/ Specs.lean         one spec file per Rust file: public statements + axioms used
  translation/                generated, never edited
    <Crate>/                  the Aeneas translation (Funs.lean, Types.lean)
    <Crate>.lean              root module importing the translation and the externals
    translation.json
  proofs/                     checked by Lean, no need to read
    Proofs/ Proofs.lean       the proofs, one file per Rust item; Proofs/Consistency/ holds
                              models showing the axioms are consistent
```

Each part is its own `[[lean_lib]]` with its own `srcDir`, so the module names do not mention
the folders (`<Crate>.Funs`, `Defs.*`, `Specs.*`, `Proofs.*`). The externals keep their module
names `<Crate>.FunsExternal` / `<Crate>.TypesExternal` but live in `formal/trusted/`, in a library
of their own. Lake makes every submodule of a library root part of that library when the root is
also in `globs`, so the translation library lists `<Crate>` in `globs` only. With explicit
`roots`/`globs`, each module belongs to exactly one library:

```toml
[[lean_lib]]
name = "<Crate>"                               # formal/translation
srcDir = "translation"
roots = ["<Crate>.Types", "<Crate>.Funs"]
globs = ["<Crate>", "<Crate>.Types", "<Crate>.Funs"]

[[lean_lib]]
name = "<Crate>External"                       # formal/trusted
srcDir = "trusted"
roots = ["<Crate>.TypesExternal", "<Crate>.FunsExternal"]
globs = ["<Crate>.TypesExternal", "<Crate>.FunsExternal"]

[[lean_lib]]
name = "Defs"                                  # likewise Specs (specs/), Proofs (proofs/)
srcDir = "specs"
roots = ["Defs"]
globs = ["Defs.*"]                             # `X.*`: X and its submodules; `X.+`: only these
```

Lean commands (`lake build`, `lake exe cache get`) run in `formal/`. `.aeneas/` and `.llbc/` stay
at the repository root.

### What is committed

- **Committed:** the generated translation (`Funs.lean`, `Types.lean`, `translation.json`), the
  hand-written `FunsExternal.lean` and `TypesExternal.lean`, `lake-manifest.json`, and
  `lean-toolchain`. The stale-translation check in CI needs the generated files to be in git.
- **Git-ignored:** `.aeneas/`, `.llbc/` and `formal/.lake/` (build outputs), and
  `formal/translation/<Crate>/*External_Template.lean` (regenerated on every run; Aeneas writes
  them next to `Funs.lean`, never over the hand-written files in `formal/trusted/`).
- **Never edited by hand:** the generated files. To change them, change the Rust, a patch, or the
  Charon settings, and re-run the translation. CI rejects hand-edits.

## 0. Scope

Before translating anything, decide which part of the crate is worth verifying and which part
Aeneas can handle. Aeneas works well on pure, sequential, safe Rust: data structures, parsing,
encoding, arithmetic. It does not handle I/O, threads and synchronisation, interior mutability or
`unsafe` code well. Code that is mostly about those is usually excluded rather than patched, and the
verification concentrates on the logic underneath it. Write the scope decision down, since it
determines what the final result does and does not cover.

## 1. The Lean project pins Aeneas

`formal/lakefile.toml` requires the Aeneas Lean library at a specific release tag:

```toml
[[require]]
name = "aeneas"
git = "https://github.com/AeneasVerif/aeneas.git"
subDir = "backends/lean"
rev = "nightly-YYYY.MM.DD-<hash>"   # must be a GitHub release tag
```

This one `rev` is the single source of truth for the Aeneas version. Both scripts read it from
`formal/lakefile.toml`, so the binaries that translate the code always match the Lean library the proofs
build against. To upgrade Aeneas, change the `rev`, rerun both scripts, and fix whatever breaks.

## 2. Install: `scripts/aeneas-install.sh`

The script:

1. Reads the Aeneas `rev` from `formal/lakefile.toml`.
2. If `.aeneas/aeneas -version` doesn't already report that tag, downloads the matching release
   bundle (charon, charon-driver, aeneas, the Lean backend) for the current platform from GitHub
   into `.aeneas/`.
3. Installs the Rust nightly toolchain that `charon-driver` was built against, from the bundle's
   `rust-toolchain` file.
4. Copies the bundle's `backends/lean/lean-toolchain` to `formal/lean-toolchain`, so Lean
   matches too, and seeds `formal/.lake/packages/aeneas` with the bundle's prebuilt Aeneas Lean
   library.

Running it again does nothing if the right version is already installed.

## 3. Charon settings live in `Cargo.toml`

What gets translated is set in the crate's `Cargo.toml`, not in the script:

```toml
[package.metadata.charon]
start_from = ["my_crate"]
# Items we will never verify: not translated at all.
exclude = [
  "my_crate::some_module::{impl core::fmt::Debug for _}",
]
# Items verification relies on but which we deliberately do not translate.
opaque = []
```

- **`exclude`** is for things we have no interest in verifying, such as `Debug` and `Hash` impls,
  marker-trait impls, and other code outside the scope of the specs. Excluded items are not
  translated, and nothing we verify may depend on them.
- **`opaque`** is almost never used. An item is made opaque only when it **cannot be translated
  and there is no useful Rust model** we could patch in. Its Lean signature is then generated
  without a body, and we state its behaviour as a Lean axiom in
`formal/trusted/<Crate>/FunsExternal.lean`. Every opaque
  item adds to the trusted base, so it needs a strong justification. The default answer to a
  translation problem is a patch (below), not `opaque`.

Each entry should have a comment saying why it is there.

Entries are Charon name patterns, such as `my_crate::module::Type::method` or
`my_crate::module::{impl core::fmt::Debug for _}` (every `Debug` impl in a module). For the full pattern
syntax and the other options, see the [Charon documentation](https://github.com/AeneasVerif/charon)
and `charon cargo --help` for the pinned version.

## 4. Translation patches

Aeneas can't translate every Rust construct (for example, iterator adaptors like `fold` when only
`Iterator::next` is modelled). Rather than give up on the item, we make a small,
behaviour-preserving edit to the Rust source so that it translates.

Each workaround is one patch file in `formal/trusted/patches/`, kept **local to this repo** (never
fetched from elsewhere). The patches are applied only to a copy of the crate at translation time.
The real Rust source is never modified. Each patch starts with a header:

```
Translation patch: <EdwardsPoint as Sum<T>>::sum

Change: `iter.fold(..)` becomes a `for item in iter` loop.
Why: Aeneas only models `Iterator::next` (aeneas#1057).
Behaviour: identical for iterators whose `fold` agrees with `next` (all std/lawful iterators).

diff --git a/src/... b/src/...
...
```

The patch changes the code that is verified, so it is part of the trusted base. That means:

- Keep each patch minimal, with one concern per file.
- The header must state the change, why it is needed (link the upstream Aeneas/Charon issue if
  there is one), and why the behaviour is unchanged.
- Each patch is **reviewed by multiple independent agents** for behaviour preservation before it is
  accepted. A human checks it in the final review.
- CI runs the crate's own test suite on the patched copy (§9), so a patch that changes behaviour
  the tests cover is caught automatically.
- When an Aeneas upgrade fixes the underlying limitation, delete the patch.

To write a patch:

1. Run `scripts/apply-patches.sh` (or the translate script), so that `.llbc/work/` holds a patched
   copy of the crate.
2. Make the edit in `.llbc/work/`.
3. Save it with `git diff` into `formal/trusted/patches/NN-short-name.patch`, numbered so the order
   they apply in is clear, and add the header.
4. Re-run the translate script and check that the item now translates.

The real `src/` is never patched, so merging new upstream code stays easy. After a merge, a patch
may stop applying. Then the script stops, and the patch has to be regenerated against the new code
and reviewed again.

## 5. Translate: `scripts/aeneas-translate.sh`

The script:

1. Checks that `.aeneas/` matches the `rev` in `formal/lakefile.toml` (otherwise asks you to run
   the install script).
2. Runs `scripts/apply-patches.sh`, which `rsync`s the crate into `.llbc/work/` (leaving out
   `target/`, `formal/`, `.aeneas/`, `.llbc/`, `.git`, `.claude/`) and applies every
   `formal/trusted/patches/*.patch` **one after the other**, in the numeric order of its number
   prefix (so `120-*` after `60-*`), with `git apply`, stopping if any patch fails. It is a
   separate script so CI can build the same copy to run the crate's tests without charon or aeneas.
3. Runs `charon cargo --preset=aeneas` on the patched copy for the single target and features we
   verify, writing `.llbc/<crate>.llbc`. Charon reads its settings from `Cargo.toml`.

   The target triple and the cargo features (and any `--cfg` flags) are fixed in the script. They
   pick one configuration of the crate, and **the proofs hold only for that configuration**. Choose
   it deliberately (usually the default features on a 64-bit target), and state it in
   `formal/README.md` and the spec files.
4. Runs `aeneas -backend lean -split-files -emit-json -dest formal/translation -subdir <Crate>`
   on the LLBC, writing the generated Lean into `formal/translation/<Crate>/` and
   `formal/translation/translation.json` (needed if another crate later reuses this
   translation with `-extern-crate`).

Aeneas regenerates `Funs.lean` and `Types.lean` on every run. It also emits
`*External_Template.lean` files (next to `Funs.lean`, git-ignored) listing the signatures of
anything it needs from outside (std functions it doesn't model, opaque items). We write those by
hand in `formal/trusted/<Crate>/FunsExternal.lean` and `TypesExternal.lean`, which are kept in git;
Aeneas never writes there.

### External functions need axioms

Aeneas only translates the crate itself. Anything it calls from outside (std functions that Aeneas'
standard library doesn't model, functions from other crates, opaque items) has no Lean body. Each
of these has to be declared in `FunsExternal.lean` (types in `TypesExternal.lean`), with its
behaviour stated as an axiom. These axioms are trusted, so:

- Keep them as few and as weak as possible, and state only what the proofs need.
- **Never leave a bare `axiom f : … → Result T`.** Give it an exact model or `ok` of an opaque
  value (`def f x := ok (Trusted.fOpaque x)`); a bare `Result` axiom asserts nothing returns, so
  proofs through it get stuck.
- **Don't axiomatise a function whose Lean type merges distinct Rust types** (e.g. `size_of`,
  where `T` and `&T` share a Lean type) — state the fact as a hypothesis on the spec instead.
- **Pin any dependency version an axiom relies on** (flate2, regex, …) and have the translate
  script check it (`cargo tree --locked`).
- Each one is reviewed like a patch: by multiple agents, then by a human.
- Where an axiom is backed by tests (a differential test against the dependency, say), keep the
  test program in `formal/trusted/evidence/` if it is not part of the build. Where possible, also
  give a model of the axioms in `formal/proofs/Proofs/Consistency/`, so they cannot prove `False`.
- Where a model is generally useful (most std functions), prefer adding it to the Aeneas standard
  library upstream, so it stops being an axiom here.

Calls into other crates the project depends on can be handled in two ways:

- Leave them as externals with axioms. This is cheap, but every function adds to what must be
  trusted.
- Translate the dependency too, and reuse its translation with `-extern-crate NAME=PATH` (see the
  Aeneas
  README section
  [Translating crates which depend on each other](https://github.com/AeneasVerif/aeneas#translating-crates-which-depend-on-each-other)).
  This is more work, but the calls are then verified rather than assumed.

Decide this per dependency, based on how much of the crate's behaviour flows through it.

For how the template files, `-split-files` and the `rust_fun`/`rust_type` attributes work, see the
Aeneas docs:
[Adding models of Rust definitions to the Lean backend](https://github.com/AeneasVerif/aeneas#adding-models-of-rust-definitions-to-the-lean-backend).

### Translating carefully

The goal is to **translate everything possible**. Work through the Charon and Aeneas output item
by item:

- For each error or skipped item, decide what to do. If it's out of scope, add it to `exclude`. If
  it's in scope, write a patch, or fix it upstream in Aeneas/Charon. Use `opaque` only as the last
  resort described above.
- Don't accept silent losses. Check that every public item we care about appears in `Funs.lean`
  with a real body.
- Rerun the translation after each change and commit the regenerated output together with the
  patches and settings that produced it.

## 6. Decide the public API specs

Once the translation is complete, we decide which public API items we care about and what each one
should guarantee. The spec statements are the part that has to be trusted, so they are reviewed
before any proof work starts:

What a statement means: Aeneas translates each function into the `Result` monad, where panics,
arithmetic overflow and out-of-bounds indexing become failure. A spec of the form
`f x ⦃ r => P r ⦄` therefore says that `f x` **terminates without panicking** and that its result
satisfies `P`. Preconditions (hypotheses on the inputs) say when the function is guaranteed not to
panic. A weaker precondition gives a stronger result.

1. Draft the statements (and the definitions they need in `formal/specs/Defs/`).
2. **Multiple agents review them independently.** Is each one faithful to the Rust documentation
   and the intended behaviour? Is it strong enough to be useful? Does it accidentally assume what it
   should prove?
3. **A human then checks** and signs off on the statements.

## 7. Spec files

There is one file in `formal/specs/Specs/` per Rust source file. It lists the file's public items in source
order. Each statement is restated (with `recall`) from its proof in `Proofs/`, followed by the
axioms that proof depends on, checked by `#print axioms`:

```lean
/-- `PartialEq for MontgomeryPoint`: equality of the encoded `u`-coordinates. -/
recall eq_spec (self other : MontgomeryPoint) :
    eq self other ⦃ (r : Bool) =>
      r = true ↔ decodeUCoordinate self.toVector = decodeUCoordinate other.toVector ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec
```

So the spec file is everything a reader needs to trust the result. It shows what is claimed and
what each claim rests on: the standard Lean axioms plus any of our own (from `FunsExternal.lean` or
opaque items). The module docstring names the definitions the statements use and lists what was
not translated. If a proof starts using a new axiom, the `#guard_msgs` check fails the build.

### What must be trusted

A proved spec says something about the Rust code only if all of the following are right:

- **Tools:** Charon and Aeneas translate the Rust faithfully, and Lean's kernel checks proofs
  correctly.
- **Configuration:** the target and features chosen in the translate script. Other configurations
  are not covered.
- **Translation patches** (`formal/trusted/patches/`): each one preserves behaviour.
- **Axioms:** in `formal/trusted/<Crate>/FunsExternal.lean` and `TypesExternal.lean` (external and
  opaque items), and any others listed in the spec files.
- **Statements:** the definitions in `formal/specs/Defs/` and the statements in
  `formal/specs/Specs/` say what we mean.
- **Exclusions:** excluded items are not verified at all, and neither is anything outside the
  scope decided in §0.

The proofs themselves don't need to be read or trusted: Lean checks them. The folder layout
mirrors this: an auditor reads all of `formal/trusted/` and `formal/specs/`, and none of
`formal/translation/` (generated) or `formal/proofs/` (checked).

## 8. Proofs

Proofs are added for everything else: the public specs, plus whatever lemmas about internal
functions they need. There is one file per Rust item in `formal/proofs/Proofs/`.

1. **Complete first.** Get every spec proved with no `sorry`, by whatever works.
2. **Improve later.** Once everything is proved, go back over the proofs to make them shorter,
   more robust to translation changes and Aeneas upgrades, and better factored into reusable
   lemmas. Spec statements don't change during this phase.

`native_decide` / `bv_decide` are fine while developing a proof but not in the final version: both
add an axiom the `#print axioms` check flags, so remove them before sign-off. Where available, a
Lean LSP / Beam MCP (goals at a point, run a tactic, `#print axioms`) speeds this work; it is an
optional aid.

## 9. CI

Three GitHub Actions workflows keep the repo honest:

- **Translation is not stale** (`.github/workflows/aeneas-translation.yml`). Runs when `src/`,
  `Cargo.toml`, `Cargo.lock`, `formal/trusted/patches/`, the scripts, `formal/lakefile.toml`, the
  externals in `formal/trusted/<Crate>/` or anything in `formal/translation/` changes. It runs `scripts/aeneas-install.sh` (caching `.aeneas/` and the nightly by the
  pinned tag), then `scripts/aeneas-translate.sh`, and fails if `git status --porcelain` shows any
  difference from what is committed. This catches a Rust change, a patch, a Charon setting or an
  Aeneas bump that was committed without regenerating the translation, and it catches hand-edits
  to generated files.
- **Lean project builds** (`.github/workflows/lean-build.yml`). Runs when anything under `formal/`
  changes. It installs elan and, with `working-directory: formal`, fetches the Mathlib cache
  (`lake exe cache get`) and runs `lake build --wfail`, which treats warnings
  (including `sorry`) as errors. The build also runs the `#guard_msgs` axiom checks in `formal/specs/Specs/`,
  so a proof that starts using a new axiom fails CI. Cache `formal/.lake/packages` and
  `formal/.lake/build` (keyed on `formal/lean-toolchain` and `formal/lake-manifest.json`) to keep
  it fast.
- **Patched copy passes the crate's tests** (`.github/workflows/patched-tests.yml`). Runs on the
  same paths as the translation check. It installs the pinned nightly, runs
  `scripts/apply-patches.sh`, and runs the crate's library tests on `.llbc/work/` (with
  `register_tool` for the patches' `#[verify::…]` attributes) — evidence that the patches, part of
  the trusted base, preserve behaviour.

Together these guarantee that what is proved is the translation of the Rust code currently in the
repo, and that the patches don't change its behaviour.

## Workflow summary

```
scripts/aeneas-install.sh                       # once, and after bumping the Aeneas rev
scripts/aeneas-translate.sh                     # after any change to src/, patches, charon settings
cd formal && lake exe cache get && lake build   # check the specs and proofs
```
