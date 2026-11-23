# Formal verification of the request-state codec

Status: **S03: toolchain only.** The Lean project, the pinned toolchain and the scripts exist;
there is no translation, specification or proof yet. The plan is
[`docs/MCP_SDK_Verification_Master_Plan_EN.md`](../docs/MCP_SDK_Verification_Master_Plan_EN.md);
the day-to-day rules are in [`docs/WORKFLOW_AND_PR_GUIDE.md`](../docs/WORKFLOW_AND_PR_GUIDE.md).

## Translated configuration

`scripts/aeneas-translate.sh` fixes it:

```
--target x86_64-unknown-linux-gnu --no-default-features --features request-state --lib
--config profile.dev.overflow-checks=true --config profile.dev.debug-assertions=true
```

The two `--config` options are passed to every cargo call (also through Charon); command-line
`--config` has the highest precedence in cargo. They fix the overflow mode explicitly: arithmetic
is checked and panics on overflow, which is what Aeneas models as failure (with
`overflow-checks=false`, `i + 1#usize` would become `Std.Usize.wrapping_add`). Nothing else may
change the build, so the script also refuses to run when:

- an environment variable that changes how cargo or rustc build is set: `RUSTFLAGS`, `RUSTC*`
  (`RUSTC`, `RUSTC_WRAPPER`, `RUSTC_WORKSPACE_WRAPPER`, `RUSTC_BOOTSTRAP`, ...), `RUSTDOC*`,
  `CHARON_*`, `AENEAS_*`, and every `CARGO_*` except `CARGO_HOME`, `CARGO_TARGET_DIR` (overridden),
  `CARGO_TERM_*`, `CARGO_NET_*`, `CARGO_HTTP_*`, `CARGO_INCREMENTAL` and
  `CARGO_REGISTRIES_CRATES_IO_PROTOCOL` (so `CARGO_PROFILE_*`, `CARGO_BUILD_*`,
  `CARGO_TARGET_<triple>_*`, `CARGO_ENCODED_RUSTFLAGS`, `CARGO_UNSTABLE_*` are refused), and
  every `RUSTUP_*` except `RUSTUP_TOOLCHAIN` (set by the script itself) and `RUSTUP_HOME`
  (container images such as the devcontainer's set it);
- the toolchain actually selected is not the pinned nightly: after setting `RUSTUP_TOOLCHAIN`
  to the bundle's channel, `rustc -vV` (the `rustc` cargo runs, whose sysroot provides the
  `librustc_driver` that `charon-driver` loads) must report commit-hash
  `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, commit-date `2026-05-31`, release
  `1.98.0-nightly` (nightly-2026-06-01), and `charon toolchain-version` must print the bundle's
  channel. This catches a `RUSTUP_HOME` whose `nightly-2026-06-01` is another toolchain; a fake
  `rustc` that prints exactly these lines is not caught by asking it (`charon-driver` would then
  not find its `librustc_driver`);
- a `.cargo/config` or `.cargo/config.toml` exists in the source (`apply-patches.sh` refuses it
  and never copies a `.cargo/` directory), in the work copy, or in any ancestor directory of the
  work directory. A *symlink* named `.cargo` is not a directory, so rsync's exclusion does not
  skip it: `apply-patches.sh` copies it and then refuses the copy (any `.cargo` entry in
  `.llbc/work/`), and the translate script's ancestor check would refuse it too if it pointed at
  a configuration. Cargo runs with an isolated `CARGO_HOME` (`.llbc/cargo-home`) that holds only
  symlinks to the registry and git caches of the real one, so `~/.cargo/config.toml` is not read;
- the workspace or `crates/rmcp` manifest has `[profile]`, `[patch]`, `[replace]` or
  `cargo-features`;
- a dependency of `rmcp` in this configuration does not come from crates.io (path, git or other
  registry, as `cargo tree` reports it), or `hmac`, `sha2`, `base64` resolve to a version other
  than the pinned one;
- the build script of `rmcp` is not `crates/rmcp/build.rs` with the sha256 pinned in the script,
  or its output file is not empty. That build script only runs `git config core.hooksPath` when
  `.git` exists (it does not in `.llbc/work/`) and prints no `cargo:` directive, so it adds no
  cfg, flag or environment variable to the build.

Proofs hold only for this configuration and for the pinned commit (plan Section 1). The Charon
settings (`start_from`, `exclude`, `opaque`) are in `[package.metadata.charon]` of
`crates/rmcp/Cargo.toml`, each entry with its reason (plan Section 9). The pinned Charon reads
them itself. The translate script fails if that table has any other key (Charon would ignore a
misspelt key, and accepts keys such as `include` or `rustc.flags` that widen the translation)
or an empty list, if the options recorded in the LLBC file differ from the lists or widen the
translation, or if the LLBC was produced for another target.

## Toolchain

The toolchain pin is the Aeneas release tag in `lakefile.toml` (`rev`), at present
`nightly-2026.08.20-5d08da4`; the bundle components below follow from it. The Lean
dependencies are pinned by commit in `lake-manifest.json`, and `scripts/lean-guard.sh sources`
fails unless the manifest lists exactly the recorded packages at the recorded commits: Aeneas at
`5d08da45a405913bbee6fd544e01debf8154ac9d` with `url`, `inputRev` and `subDir` equal to the
lakefile's `git`, `rev` and `subDir`; Mathlib at `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`
(`v4.31.0`); and the eight packages Mathlib brings in (`MANIFEST_PACKAGES` in
`scripts/lean_guard.py`, updated in the same PR as the Aeneas rev), and unless `lean-toolchain` is
exactly `leanprover/lean4:v4.31.0` (`LEAN_TOOLCHAIN`, same rule). Whether the Mathlib pin and
its prebuilt oleans belong to the trusted base, and how they are checked, is an open scope
question for the human (`docs/evidence/S03.md`, open items).

| Component | Version | Source |
|---|---|---|
| Aeneas | `nightly-2026.08.20-5d08da4` (commit `5d08da45`) | `rev` in `lakefile.toml` |
| Charon | `0.1.235` (commit `f5208b1c`) | release bundle |
| Rust | `nightly-2026-06-01` | the bundle's `rust-toolchain` |
| Lean | `v4.31.0` (Mathlib `v4.31.0`) | the bundle's `backends/lean/lean-toolchain`, copied to `lean-toolchain` |

The release assets are checked against the sha256 values committed in
`trusted/aeneas-bundle.sha256` (see Trusted base, Tools).

The dependency versions the external models rely on are pinned in `scripts/aeneas-translate.sh`
(`hmac 0.13.0`, `sha2 0.11.1`, `base64 0.23.1`, and since S08–S09 `digest 0.11.3`,
`zeroize 1.9.2`, `chrono 0.4.45` and `serde_json 1.0.154`, which the models also cite); the
script fails if `cargo tree` resolves any other version or a source other than crates.io. `Cargo.lock` is git-ignored and `scripts/apply-patches.sh` never copies it into
`.llbc/work/`, so every run, local or CI, resolves the dependencies afresh (this needs the
crates.io index).

## Commands

From the repository root:

```bash
scripts/aeneas-install.sh      # bundle into .aeneas/<tag>/, Rust nightly, Lean toolchain
scripts/aeneas-translate.sh    # copy + patches (.llbc/work/), version check, Charon, Aeneas,
                               # target and sorry checks, then formal/translation/
```

For a scratch source, set `RMCP_SOURCE_ROOT`, `RMCP_LLBC_DIR` and `RMCP_TRANSLATION_DEST`
together. The paths are canonicalised (symlinks, `.`, `..`); the script refuses a scratch source
with an output directory inside the repository, any output directory that contains the
repository, and, before replacing it, an output directory that holds anything other than an
earlier output (`Rmcp/`, `translation.json`). The work directory gets `rsync --delete` (`work/`)
and `rm -rf` (`out/`, `cargo-home/`), so both scripts refuse an `RMCP_LLBC_DIR` that is `/`,
`$HOME`, the repository or contains one of them, contains the source or lies inside it (except
`<source>/.llbc`), whose `work/`, `out/`, `cargo-home/` or `target/` is a symlink, or that
exists, is not empty and has no marker file `.rmcp-llbc-dir` (written into every work directory
they accept; the repository's own git-ignored `.llbc` is accepted without it). Use a new or
empty directory for a scratch run (`scripts/llbc-dir-guard.sh`).

In `formal/`:

```bash
lake exe cache get
../scripts/lean-guard.sh sources
set -o pipefail; lake build 2>&1 | tee .lake/build.log    # .lake/ is git-ignored
../scripts/lean-guard.sh build-log .lake/build.log
../scripts/lean-guard.sh axioms            # only after a successful lake build
../scripts/lean-guard.sh aeneas-archive
```

`../scripts/lean-guard.sh fresh` is for CI only (first step after checkout): it fails when
`formal/.lake` exists, which is normal in a local working tree.

Run `axioms` only after a `lake build` that succeeded: it audits the `.olean` files as they are.
It fails if a project module's source changed after its `.olean` was built (it compares the
source hash recorded in Lake's `.trace` file with the current file), but an `.olean` left from
an earlier build of a module that the roots no longer import is simply not audited, and a
failed build can leave older `.olean` files of the modules it did not reach.

The build gate (decided at S03): every library sets `warningAsError`, and CI runs a plain
`lake build`, which fails on any warning in this project's modules, including `sorry`.
`lake build --wfail` is not used because the pinned Aeneas Lean library has four `sorry`
warnings that Lake replays on every build (`Aeneas/Std/Slice.lean:363,586`,
`Aeneas/Std/StringIter.lean:12,15`; `docs/evidence/S03.md`) and `--wfail` fails on them.

A file could switch `warningAsError` off, hide messages (`#guard_msgs (drop all) in`) or use a
construct the kernel does not check, so `scripts/lean-guard.sh` (run by CI; the checks are in
`scripts/lean_guard.py`, Python 3.11 or later, and `scripts/lean-axiom-audit.lean`) also fails if:

- `lakefile.toml`, parsed as TOML, is not exactly the five libraries of plan Section 5 (`Rmcp`
  in `translation/`, `RmcpExternal` in `trusted/`, `Defs` and `Specs` in `specs/`, `Proofs` in
  `proofs/`, with their fixed roots), each with exactly the keys `name`, `srcDir`, `roots`,
  `leanOptions` and `leanOptions = { warningAsError = true }` exactly; if the package sets
  anything but `name`, `defaultTargets`, one `[[require]]` (aeneas) and the libraries (so no
  `leanOptions` or `moreLeanArgs`-style key at any level); or if `lakefile.lean` exists;
- `lake-manifest.json` does not list exactly the recorded packages at the recorded commits (see
  Toolchain);
- `lean-toolchain` is not exactly `leanprover/lean4:v4.31.0` (`LEAN_TOOLCHAIN` in
  `scripts/lean_guard.py`, updated in the same PR as the Aeneas rev; elan runs whatever toolchain
  this file names, so CI checks it before elan is installed); git tracks anything under a `.lake`
  directory below `formal/` (Lake loads a committed `.lake/config/<idx>/lakefile.olean` as
  compiled code at its first command); a `.lake` directory exists below `formal/` other than
  `formal/.lake`; or a file is named with a case variant of `.lean` (`Foo.LEAN`);
- a `.lean` file anywhere under `formal/` except `.lake/` and `specs/Drafts/` (generated files in
  `translation/` included, with the exceptions below) contains, as a whole token (Lean's
  tokenization: a hit needs no letter, digit, `_`, `'`, `!` or `?` directly before or after, so
  `by_elab` is its own token and `my_elaborate`, `elab_as_elim`, `List.drop` are not hit):
  - `warningAsError`, `sorry`, `sorryAx`, `admit`, `native_decide`, `bv_decide`,
    `skipKernelTC`, `proofAsSorry`, `implemented_by`, `extern`, `unsafe`, `ofReduceBool`,
    `ofReduceNat`, `trustCompiler`; the `native` option of `decide` (`+native`, `-native`,
    `native :=`); any `debug.` option; `set_option linter.<name> false` (allowed in
    `translation/`, where Aeneas emits it); `axiom` outside `trusted/` (and the unbuilt Aeneas
    `*_Template.lean` files);
  - a keyword or name that runs code during the build (`META_WORDS`): `run_cmd`, `run_tac`,
    `run_elab`, `run_meta`, `by_elab`, `include_str`, `test_extern`,
    `register_error_explanation`, `show_panel_widgets`, `with_panel_widgets`, `bv_check`,
    `bv_decide?`, `autoParam`, `elab`, `elab_rules`, `initialize`, `builtin_initialize`, `macro`,
    `macro_rules`, `syntax`, `simproc`, `dsimproc`, `simproc_decl`, `builtin_simproc`,
    `register_option`, `register_simp_attr`, `declare_syntax_cat`, `declare_simp_like_tactic`,
    `eval%`, `trace` (the tactic; `set_option trace.<class>` is allowed), `success_if_fail_with_msg`,
    `pi_lower_bound`, `pi_upper_bound`, `lrat_proof`, `from_lrat`, `run_conv`, `run_tacq`,
    `by_elabq`, `plausible`, `bv_tac`, `initialize_simps_projections(?)`, `discharger`,
    `preprocessors`, `addDecl`, `addAndCompile`, `modifyEnv`, `setEnv`, `withOptions`, the
    metaprogramming types `IO`, `EIO`, `BaseIO`, `CoreM`, `MetaM`, `TermElabM`, `TacticM`,
    `CommandElabM`, `MacroM`, `SimpM`, `DelabM`, `CommandElab`, `TermElab`, and `Elab` (so both
    `Lean.Elab` and `open Lean Elab`). The list was derived from the pinned toolchain and packages:
    every syntax whose elaborator or macro reaches an evaluation primitive or builds such syntax
    (`docs/evidence/S03.md`, fix round 5, W1);
  - any `#` command except `#check`, `#print` and `#guard_msgs` (`#eval`, `#exit`, `#guard`,
    Aeneas's `#assert`, Plausible's `#test`, `#leansearch`, ... run code or have side effects);
    `#guard_msgs` only in `specs/Specs.lean` and `specs/Specs/`, and there only as
    `#guard_msgs in` followed by one `#print axioms <name>` line (no options, no `drop`); in
    prose write it in backticks;
  - an attribute, in `@[...]` or `attribute [...]` (after `local`, `scoped` or `-`), that is not
    in `ATTR_ALLOWED`: what Aeneas emits in the generated code (`reducible`, `irreducible`,
    `global_simps`, `discriminant`, `rust_fun`, `rust_type`, `rust_trait`, `rust_trait_impl`,
    `rust_loop`, `rust_loop_body`, ...) and lemma tags, simp sets, reducibility, compiler and
    documentation flags (`simp`, `instance`, `ext`, `grind`, `norm_cast`, `step`, `progress`,
    `scalar_tac`, `inline`, `deprecated`, ...). Any other attribute can hand its declaration to
    code the build runs (`command_elab`, `tactic`, `macro`, `init`, `simproc`, `norm_num`,
    `positivity`, `aesop`, `delab`, linters, doc roles, ...). Extending the list is a reviewed
    change of `scripts/lean_guard.py`.

  `notation`, `infix`, `prefix`, `postfix` stay allowed: the macro they generate only replaces
  the notation by its right-hand side, which is written in the same file and checked by the same
  rules. `macro`/`syntax` are banned because a macro can build any syntax node (a `run_tac`, say)
  without its keyword in the text. A proof that needs a custom tactic writes it out inline; a
  reviewed tactic module would be a human decision.

  The check is textual: **comments and docstrings count**. Prose hits the banned words too:
  "axiom", "admit", "extern", "unsafe", "sorry", "syntax", "macro", "elab", "initialize", "IO",
  "simproc", "trace", "plausible". This includes the docstrings of the
  `Proofs/External` laws (S08–S09), which are about the trusted models. Write instead
  "assumption", "postulate" or "trusted statement" (for axiom), "placeholder" or "unproved"
  (for sorry/admit), "foreign" or "outside Lean" (for extern), "unchecked" (for unsafe),
  "grammar" or "notation" (for syntax), "set up" or "create" (for initialize), "input/output"
  (for IO), "follow" or "record" (for trace). Symlinks under `formal/` fail;
- a file under `trusted/` contains, outside comments, string and character literals, an
  identifier whose first component is `rmcp` (also `_root_.rmcp…`, `«rmcp»…`) or the keyword
  `export`, except in a line that is exactly `open rmcp` (see "Trusted base");
- the `lake build` log has a line with `warning:` or `error:` other than the four Aeneas lines
  above, or no "Build completed successfully" line;
- (`axioms`) `.lake/build/lib/lean` holds anything but modules named `Rmcp`, `Defs`, `Proofs`,
  `Specs` or below them; a project `.olean` is stale; the constants declared in the modules of
  this project reached from the default targets depend (one order-independent walk over all of
  them, through types, values and whole inductive blocks; a superset of what `#print axioms`
  reports) on an axiom other than `propext`, `Classical.choice`, `Quot.sound`, the axioms declared
  in the roots of `RmcpExternal` and the `toStr` native-code axioms of `Rmcp.Types`/`Rmcp.Funs`
  (next item; locked if used; nothing else native) (this catches `sorryAx`, also when inherited
  from the Aeneas library, and the `_native` axioms of `native_decide`/`decide +native`); a root of
  `RmcpExternal` declares a name in the namespace `rmcp` or adds an
  alias (see "Trusted base"); or the kernel rejects a project constant when all of them are replayed
  (`Lean.Environment.replay`, the check `leanchecker` runs) onto the non-project modules they
  import. The replay catches declarations that were added without a kernel check (for example
  through `debug.skipKernelTC` set from a metaprogram, `docs/evidence/S03.md`, V1) and altered
  `.olean` files. The audit reads the `.olean` files without running any code from them
  (`loadExts := false`) and runs with the toolchain's own `lean`, not `lake env`, with the
  toolchain library first on `LEAN_PATH`; `leanchecker` is not run separately (it uses the same
  replay); or
  `trusted/axioms.lock` does not cover the trusted axioms in use. Audit scope (human decision
  2026-11-23 for `axioms.lock`; the lead applied the same rule to `native-axioms.lock`, next item):
  an axiom is *used* if it is reachable from some constant declared in a module of the `Defs`,
  `Proofs` or `Specs` library, transitively through any constant (including the generated
  `Rmcp.Types`/`Rmcp.Funs` definitions and the externals). Every constant of such a module counts,
  including private helpers, instances and auxiliary declarations (conservative). The audit computes
  the set with one walk over types, values and whole inductive blocks (constructors, recursors, the
  other types of a mutual block) with a single visited set, so the result does not depend on the
  order of the constants; it contains every axiom that `#print axioms` reports for those constants
  and can contain more (an over-approximation). `#print axioms` itself can miss an axiom reached
  through any inductive/constructor cycle, not only a mutual block: Lean stores per module the axiom
  set of each constant computed with a shared cache, and a constant entered while its cycle is open
  gets an incomplete set (`#print axioms rmcp.model.request_state.Keys.Single` omits the `HashMap`
  and `RandomState` axioms that `Keys` reports; `docs/evidence/S03.md`). `axioms` fails if a used
  axiom declared in a root of `RmcpExternal` is not in `trusted/axioms.lock`, if a lock entry names
  no axiom declared in those roots (stale), or if the sha256 of a declared axiom's canonical
  statement differs from its entry (a structural text of the type `Expr`: constants by full name
  with universe levels, de Bruijn indices, binder info; independent of notation and pretty-printer
  options). Trusted axioms that no `Defs`/`Proofs`/`Specs` constant depends on (before S08–S09, the
  placeholder externals used only by generated functions that no theorem mentions) are listed for
  information and need no entry; an entry for a declared but unused axiom is reported as "unused
  (allowed)", so a reviewed model can be locked before a theorem depends on it. Importing
  `Rmcp.Funs` into a proof module therefore does not require locking all externals. The weakening
  this accepts: the statement of a declared trusted axiom that is not in the lock and not used
  (before S08–S09, all 41 placeholder externals; none is declared once the S08–S09 models land,
  human decision 2026-11-23) can change, or the axiom can vanish, without CI noticing, as
  long as nothing in `Defs`/`Proofs`/`Specs` depends on it. This holds for ordinary PRs too, not
  only for forged artifacts: only the source diff of `trusted/` and the guard's informational list
  show such a change, so review of `trusted/` is the barrier for unused axioms. The scope applies to
  the locks only: the allowed-axiom check, the kernel replay and the namespace check above cover
  every project constant, including all of `Rmcp.Types`/`Rmcp.Funs` and `RmcpExternal`. The PR that
  adds or changes a used axiom adds its line (the failure message prints it), and review checks that
  each line belongs to a reviewed axiom (which covers the locked axioms only);
- (`axioms`, native-code axioms; human decision 2026-11-22, handled as in the SPQR project) a
  native-code axiom (a name with a `_native` component, as `decide +native` and
  `native_decide` declare, or `Lean.trustCompiler`) is a trust item of its own, listed
  separately in the audit output. The project constants may reach one (by the walk of the
  previous item over all of them) only if its statement is exactly the side condition of the
  pinned Aeneas `toStr` for one string literal,
  `decide ("…".toByteArray.size ≤ Aeneas.Std.U32.max) = true`, and it is declared in
  `Rmcp.Types` or `Rmcp.Funs` (the generated modules; any other native-code axiom, including a
  `toStr` side condition from hand-written code in `Proofs`, `Specs`, `Defs` or `trusted/`,
  fails, even if listed), and it is listed in `trusted/native-axioms.lock` as
  `<name> <declaring module> sha256:<hash>` (the same structural statement hash as
  `axioms.lock`) if it is used (the audit scope of `axioms.lock`, previous item, which the lead
  applied to this lock; a native axiom reached only through generated functions that no
  `Defs`/`Proofs`/`Specs` constant depends on needs no entry and is listed for information; the
  `toStr`-form and module restrictions hold for every native-code axiom reachable from any
  project constant). A used one that is unlisted, a changed statement or module of a reached one,
  a lock entry for a module other than `Rmcp.Types`/`Rmcp.Funs`, and a stale entry (its module is
  in the audited import closure, the axiom is not reached there, so no longer declared) fail; an
  entry for a reached but unused axiom is reported as "unused (allowed)". Only the import closure
  of the roots of the default targets is audited: `Rmcp`/`RmcpExternal` are covered once a
  `Defs`, `Proofs` or `Specs` module imports `Rmcp.Funs` (S06) or they become default targets (a
  change of `lakefile.toml` by the lead; the unused placeholder externals no longer block it:
  with `Rmcp` and `RmcpExternal` added to the default targets, `lake build` and the `sources`,
  `build-log` and `axioms` checks pass, `docs/evidence/S03.md`, test D1); until then native-lock
  entries for `Rmcp.Types`/`Rmcp.Funs` are reported as not checked (entries for any other module
  fail) and any `axioms.lock` entry fails as stale, even when `.olean` files of `Rmcp` exist from
  an explicit `lake build Rmcp RmcpExternal`. The lock holds the five string literals of the
  target code (`VERSION_V1`, `VERSION_V2`, `KID_EMPTY_MSG`, `KID_TOO_LONG_MSG`, the `expect`
  message in `rs1_fallbacks_verify`). These side conditions also have a kernel proof
  (`simp only [U32.max, U32.numBits, UScalarTy.numBits]; decide`, axioms `[propext]`), so an
  upstream Aeneas `toStr` fix and a rev bump would remove the axioms; that is preferred to a
  local replacement (open item, `docs/evidence/S04a.md`);
- the Aeneas Lean-library archive downloaded by Lake does not match its committed sha256, the
  installed Aeneas build and the archive do not hold the same regular files with the same bytes
  (every file except `*.hash` and `*.trace`: `.olean`, `.olean.private`, `.olean.server`,
  `.ilean`, `.ir`, `.c`, `.json`, shared libraries), or the Aeneas library is built but no
  archive is present (unless `LEAN_GUARD_AENEAS_FROM_SOURCE=1` marks a build from source).

### What CI checks

`.github/workflows/lean-build.yml` has two jobs, because `lake build` elaborates the project,
and elaboration can run code that rewrites files of the runner (a `#eval` writing
`scripts/lean-guard.sh`, say) before a later step of the same job.

- `build`: checkout; `lean-guard.sh fresh` (no `formal/.lake` in the checkout, nothing tracked
  under a `.lake` directory) and `lean-guard.sh sources` (lean-toolchain, lakefile, manifest,
  sources), both plain Python before elan is installed and before any `lean` or `lake`
  command; pinned elan, and the Lean toolchain installed by its name
  (`leanprover/lean4:v4.31.0`, not read from the file); `lake exe cache get`, `lake build` into
  `.lake/build.log`, then `.lake/build` and the log are uploaded as one tar file. Only this job
  restores the `.lake/packages` cache; `.lake/build` is never cached.
- `check` (`needs: build`): a fresh runner and checkout, so the scripts come from git; `fresh`
  and `sources` again before elan; pinned elan and the named toolchain installed afresh;
  Mathlib cache and the Aeneas release archive fetched afresh (`lake exe cache get`,
  `lake build Aeneas`; no cache) and `aeneas-archive`; then the artifact is unpacked
  (`unpack-build`: only `build/` and `build.log`, no links, no `..`) and `build-log` and
  `axioms` run. No Lake command runs after the unpack, and the audit runs no code from the
  `.olean` files, so no project code runs in this job.

What job `check` can and cannot detect in the artifact: it detects a project constant that
depends on a disallowed axiom (`sorryAx`, `Lean.ofReduceBool`, an axiom outside the
`RmcpExternal` roots), a constant the kernel rejects on replay, a trusted axiom used by a
`Defs`/`Proofs`/`Specs` constant that is not in `trusted/axioms.lock`, a declared trusted axiom
whose statement differs from its lock entry, a module outside the project names, a build log
with unexpected warnings or errors, and an `.olean` older than its source by the trace hash
(which a forger can fake). It does not detect that the artifact was compiled from other
sources: the statements of spec theorems, definitions and non-axiom externals are not
re-elaborated in job `check`, so a forged artifact can contain a different, kernel-correct
project (for example a theorem with the reviewed name and a weaker statement), as long as its
`Defs`/`Proofs`/`Specs` constants use no trusted axiom outside the lock (since the audit-scope
change of 2026-11-23 it can also add, remove or change in `RmcpExternal` any unlocked axiom
that no `Defs`/`Proofs`/`Specs` constant depends on; such an axiom supports no theorem).

Accepted residual limits (human decision, 2026-11-22; S03 is accepted with them):

- **Build-time code execution cannot be fully excluded by text bans.** The only barriers are
  the ban list of `sources` and human review of every Lean file of every PR for
  metaprogramming. A ban that misses a code-running construct is a hole: code run by
  `lake build` can replace or forge the uploaded artifact, which job `check` then accepts within
  the limits above. Known ways around the list (fix round 5, X3): metaprograms reached without a
  banned word, for example a command assembled from string pieces, parsed with
  `Parser.runParserCategory` and run with `elabCommand` from code that some executor runs; the
  configuration terms and rule clauses of tactics that compile and run them (`linarith`,
  `nlinarith`, `aesop` and its wrappers, `saturate`/`forward`, Aeneas `step`/`progress`; a
  `linarith` discharger given as a `do` block ran during the build, `docs/evidence/S03.md`);
  and constructs in packages not yet seen. The run-code-free barrier against a forged artifact
  (V2) is therefore not closed against a determined attacker; review is the barrier.
- The locks cover axioms only. The external models of `trusted/` are definitions, structures and
  `opaque` constants (no axiom since S08–S09), which neither `#print axioms` nor `axioms.lock`
  shows: a changed or forged model is caught only by review of `trusted/` (a hash lock over the
  declarations of `RmcpExternal` is an option for the human at the S08/S09 sign-off).
- The trusted-axiom lock limits what a forged artifact can do to non-axiom content: it cannot
  add or change a trusted axiom that some `Defs`/`Proofs`/`Specs` constant depends on, and
  cannot change a locked axiom's statement; it can add, remove or change any unlocked trusted
  axiom that no such constant depends on (audit scope, human decision 2026-11-23), and it can
  change everything else as described above.
- `Specs` imports `Proofs`, so a module in `proofs/` can change the meaning of a reviewed spec
  statement without any metaprogramming: a global instance, notation, coercion or attribute
  declared there is in scope when the statement is elaborated (for example
  `instance (priority := high) : OfNat Nat 2 := ⟨1⟩` makes `theorem spec : (1 : Nat) = 2`
  provable, and every gate passes). Reading `trusted/` and `specs/` is therefore not enough for
  an auditor while this holds; `proofs/` must be read for such declarations too. The structural
  fix is an open decision before S06 (`docs/evidence/S03.md`, open items).
- The Mathlib oleans of job `check` come from Mathlib's cache server and are not checked
  against a digest here (open scope question, see Toolchain).
- `scripts/aeneas-translate.sh` asks `rustc -vV` for the pinned version; a fake `rustc` that
  prints exactly the pinned lines is not caught by asking it.
- The `.olean` files are memory images that Lean maps without validating them. A crafted file
  could crash the audit or worse; the job has read-only repository permissions and no secrets,
  so the worst outcome is a wrong check result.

## Layout

| Path | Library | Contents |
|---|---|---|
| `translation/` | `Rmcp` | generated by Aeneas, never edited by hand (from S04a) |
| `trusted/` | `RmcpExternal` | patches, hand-written external models (definitions, structures and `opaque` constants; no axiom since S08–S09, human decision 2026-11-23), their evidence and the differential check (`evidence/`); `aeneas-bundle.sha256` (expected digests of the Aeneas release assets); `axioms.lock` (name and statement hash of every trusted axiom used by a `Defs`/`Proofs`/`Specs` constant, plus any reviewed unused one locked in advance); `native-axioms.lock` (name, module and statement hash of every accepted native-code axiom used by such a constant, plus locked unused ones) |
| `specs/` | `Defs`, `Specs` | definitions used by statements; spec files; `Drafts/` is in no library |
| `proofs/` | `Proofs` | proofs; laws and specs of the external models (`Proofs/External/`, S08–S09) |
| `docs/` | — | status, board, function records, evidence, blockers |

`Rmcp` and `RmcpExternal` are declared in `lakefile.toml` but are not default targets (`lake build
Rmcp RmcpExternal` builds them); `lake build` builds `Defs`, `Proofs` and `Specs`. Making them
default targets is a change of `lakefile.toml` by the lead. The unused placeholder externals
(replaced at S08–S09 by definitions) no longer blocked it (audit scope, human decision
2026-11-23): with both added to the default targets,
`lake build` and the `sources`, `build-log` and `axioms` checks pass (`docs/evidence/S03.md`,
test D1). Until then they are audited only through a `Defs`/`Proofs`/`Specs` module that imports
`Rmcp.Funs` (S06).

## Trusted base

An auditor reads all of `trusted/` (including `axioms.lock` and `native-axioms.lock`) and `specs/`, the Charon settings in
`crates/rmcp/Cargo.toml` and the configuration in `scripts/aeneas-translate.sh`; see plan
Section 4, "What must be trusted". While `Specs` imports `Proofs`, that is not sufficient: the
auditor also reads `proofs/` for instances, notation, coercions and attributes that change what
a spec statement means (see "What CI checks", accepted residual limits).
At S03 there are no patches, externals or axioms. S04a part 2 started `trusted/Rmcp/` from the
Aeneas templates with unreviewed placeholder axioms. Since S08–S09 (human decision 2026-11-23:
convert every axiom into a definition) it declares **no axiom**: each external type is a
`structure`, each external function a definition with the generated name and signature
(keeping the template's `@[rust_type]` or `@[rust_fun]` attribute where it has one; the five
opaque `rmcp` functions, the `prim` functions and `now_ms`, have none), and what a model cannot
compute is one of four `opaque` constants
(`ExtModel.hmacSha256`, `ExtModel.sipHash13`, `ExtModel.nowMs`, `ExtModel.SerdeJsonErrorImpl`),
which add no axiom; `axioms.lock` stays empty. What an auditor trusts is that each definition
describes its Rust function, with the exceptions stated in its docstring
(`trusted/evidence/README.md` cites the source and tests of each). These models do not appear in
`#print axioms`, the `#guard_msgs` lists or `axioms.lock`, so a change to one is caught only by
review of `trusted/`; a proof may use them once S08/S09 are signed off. Review rule: no spec statement
mentions the functions `rmcp.model.request_state.RequestStateCodec.now_ms`,
`…RequestStateCodec.open` or `…RequestStateCodec.open_with` (a variable named `now_ms`, such as the
time parameter of E01 `open_authenticated_body`, is not covered): the single opaque clock reading
`nowMs` makes those functions pure in
the model; opening is specified through `open_at`.
Names in the namespace `rmcp` are banned in `trusted/`: the generated code
works inside `namespace rmcp` and names the root-level externals and the Aeneas library functions
unqualified, so a name `rmcp.<x>` from `trusted/` would silently take precedence over the one it
means. Enforced in two layers. (1) `lean-guard.sh sources`, on every
file under `trusted/`: after comments (`--`, nested `/- -/`, docstrings), string literals and
character literals are blanked, any identifier token whose first component is `rmcp` (also after
`_root_.`, and quoted, `«rmcp»`) fails (declaration name, `namespace`, `alias`, a reference),
and so does the keyword `export`. This layer is a best-effort lexer: it does not skip `«…»`
identifiers, so a quoted name containing `--`, `/-` or `"` can blank what follows and hide a
declaration from it; layer (2) is authoritative; the only exception is a line that is
exactly `open rmcp`, which `FunsExternal.lean` keeps from the Aeneas template because its
signatures name trait structures of `Rmcp.Types` (`core.hash.BuildHasher`, `zeroize.Zeroize`,
…; the file does not build without it) and which declares nothing. (2) `lean-guard.sh axioms`,
on the build output: a constant of a root of `RmcpExternal` whose name (private prefix removed)
starts with `rmcp`, including auxiliary ones such as `rmcp.x_def`, or any alias added by such a
module (`export`, read from Lean's alias table), fails. Layer (2) runs only when `RmcpExternal`
is reached from the default targets (once a `Defs`/`Proofs`/`Specs` module imports `Rmcp.Funs`
and so `Rmcp.FunsExternal`, or `RmcpExternal` becomes a default target, see "Layout"; until then
only in a scratch audit, see `docs/evidence/S04a.md`). Open routes, recorded for S08–S09 (human
decision 2026-11-23, no fix in S04a): layer (2) checks only constants declared in the `RmcpExternal`
roots themselves, so a
shadowing `rmcp.<x>` declared in another project module that a trusted root imports passes both
layers (plan Section 5 allows `RmcpExternal` to import only Aeneas and `Rmcp.Types`, but nothing
enforces it yet); and global `notation`/`infix` or a high-priority `instance` declared in
`trusted/` can redirect generated code without any `rmcp` name. Reviewers of `trusted/` check
imports, notation and instances until this is enforced. The exclusions and opaque items are those of plan Section 2.3 and Section 9 (S04a part 2
adds the derived `Debug` impls to `exclude`, human decision 2026-11-22). The trusted-base section of `docs/STATUS.md` is authoritative once
it exists.

### Tools

- Charon, Aeneas and charon-driver: the binaries of the Aeneas release bundle for the pinned tag,
  checked by `scripts/aeneas-install.sh` against `trusted/aeneas-bundle.sha256`; not built from
  source.
- Aeneas Lean library: its oleans are **prebuilt**. Lake downloads the release archive
  `lean-build-aeneas-<platform>.tar.gz` (the Aeneas package sets `preferReleaseBuild`) and does
  not check a digest; `scripts/lean-guard.sh aeneas-archive` checks it against
  `trusted/aeneas-bundle.sha256` and checks that the installed oleans are those of the archive. The library's sources are pinned by the commit in
  `lake-manifest.json`, but the oleans are not rebuilt from them.
- Mathlib: its oleans are **prebuilt**, fetched by `lake exe cache get`, and not rebuilt from
  source.
- Lean (`lean-toolchain`) and the Rust nightly come from elan and rustup; CI installs a pinned
  elan binary checked by sha256 and the Lean toolchain by its name
  (`.github/workflows/lean-build.yml`).
