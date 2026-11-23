# Evidence: the translation and patched-tests CI workflows (S04a part 2, input to S17)

Status (2026-11-23): both workflows written and their shell steps run locally on macOS; never run
on GitHub (no push). Awaiting review. S17 (each check shown to fail once on a throwaway branch on
GitHub) is still open.

## Files

- `.github/workflows/aeneas-translation.yml`, "translation is not stale" (plan Section 5, "CI";
  VERIFICATION.md Section 9; WORKFLOW_AND_PR_GUIDE.md, "CI runs three workflows").
- `.github/workflows/patched-tests.yml`, "patched copy passes the crate's tests" (same sections).

Both follow `lean-build.yml`: actions pinned by commit SHA (`actions/checkout` v7.0.1,
`actions/cache` v6.1.0, the same SHAs), `permissions: contents: read`, checkout with
`persist-credentials: false`, a `concurrency` group per ref with cancel-in-progress, path
filters on `push` (main) and `pull_request`, `workflow_dispatch`, `timeout-minutes`, and
`shell: bash`.

## Trigger paths

Both workflows have the same list (plan: "Same paths as the translation check"):

| Path | Source |
|---|---|
| `crates/rmcp/src/**`, `crates/rmcp/Cargo.toml`, `crates/rmcp/build.rs`, `Cargo.toml` | plan Section 5 |
| `formal/trusted/patches/**`, `formal/trusted/Rmcp/**`, `formal/translation/**`, `formal/lakefile.toml` | plan Section 5 |
| `scripts/aeneas-install.sh`, `scripts/aeneas-translate.sh`, `scripts/apply-patches.sh`, `scripts/llbc-dir-guard.sh` | plan "the scripts" (the four translation scripts) |
| `formal/trusted/aeneas-bundle.sha256`, `formal/lean-toolchain` | added: `aeneas-install.sh` reads the first and writes the second |
| the workflow file itself | added, as in `lean-build.yml` |

`Cargo.lock` (named in VERIFICATION.md) is not a trigger: it is git-ignored in this repository.

## Steps

`aeneas-translation.yml`, job `translate` (ubuntu-latest, 60 min):

1. Checkout.
2. `RUST_NIGHTLY` (`nightly-2026-06-01`, used only for the cache path) must appear as the
   channel check in `scripts/aeneas-translate.sh`.
3. Pinned elan v4.4.0 checked by sha256 (as in `lean-build.yml`), no default toolchain:
   `aeneas-install.sh` fails without `elan` and installs the bundle's Lean toolchain itself.
4. `actions/cache` for `.aeneas/`, `~/.rustup/toolchains/<nightly>-x86_64-unknown-linux-gnu` and
   `~/.rustup/update-hashes/<nightly>-x86_64-unknown-linux-gnu`,
   keyed on the channel and `hashFiles(formal/lakefile.toml, formal/trusted/aeneas-bundle.sha256)`
   (the files that hold the tag and the bundle digest).
5. `scripts/aeneas-install.sh`.
6. `scripts/aeneas-translate.sh` (the pinned-rustc, Charon-channel, dependency, build.rs,
   Charon-option, target and `sorry` checks are all inside the script).
7. `git status --porcelain --untracked-files=all` must be empty; otherwise it prints the
   status, `git diff --stat` and the diff, and fails.

No Rust setup action and no variable that `aeneas-translate.sh` refuses is set (only
`RUST_NIGHTLY`, read by the workflow's own consistency step): `dtolnay/rust-toolchain` and
`Swatinem/rust-cache` export `CARGO_*` variables (e.g. `CARGO_PROFILE_DEV_DEBUG`) that
`aeneas-translate.sh` refuses. The runner's preinstalled rustup is used.

`patched-tests.yml`, job `test` (ubuntu-latest, 45 min), with `RUSTUP_TOOLCHAIN=nightly-2026-06-01`
(overrides the `rust-toolchain.toml` that `apply-patches.sh` copies into `.llbc/work/`):

1. Checkout.
2. The same `RUST_NIGHTLY` check.
3. `actions/cache` for the nightly.
4. `rustup toolchain install nightly-2026-06-01 --profile minimal`; prints `rustc -vV`.
5. `scripts/apply-patches.sh`.
6. In `.llbc/work/crates/rmcp`: `cargo test --no-default-features --features request-state --lib
   --config profile.dev.overflow-checks=true --config profile.dev.debug-assertions=true` (the
   translation's profile settings; the runner host is the translated target).

## Local validation (macOS 26.6.2 arm64, scratch clones under `/tmp/ci-wf/`)

Clone `/tmp/ci-wf/clone` of `d08ded8` with the two workflow files committed on top (`026271d`).
Each step's `run:` text was run with `bash -eo pipefail`.

| # | Check | Exit |
|---|---|---|
| 1 | YAML of both files parses (`python3 -I`, `yaml.safe_load`) | 0 |
| 2 | `actionlint` | not installed, not run |
| 3 | `RUST_NIGHTLY` check step; with `RUST_NIGHTLY=nightly-2099-01-01` | 0; 1 |
| 4 | `scripts/aeneas-install.sh` (bundle downloaded afresh, sha256 matches, 27 s) | 0 |
| 5 | `scripts/aeneas-translate.sh` ("all 25 targets defined in Funs.lean; no sorry", 14 s) | 0 |
| 6 | diff-check step; `git diff --exit-code formal/translation` | 0; 0 |
| 7 | Negative: line 1162 of `formal/translation/Rmcp/Funs.lean` (`i * 4#usize` → `i * 5#usize`, in `b64_len`) hand-edited and committed; translate again | translate 0 |
| 8 | diff-check step after 7 (shows ` M formal/translation/Rmcp/Funs.lean`, the one-line diff, `::error::`); `git diff --exit-code formal/translation` | 1; 1 |
| 9 | Second clone `/tmp/ci-wf/clone2` of `026271d`: `RUST_NIGHTLY` check; `rustup toolchain install nightly-2026-06-01 --profile minimal` (already installed; rustc commit `14210df0e27c…`, 2026-05-31) | 0; 0 |
| 10 | `scripts/apply-patches.sh` ("no patches in formal/trusted/patches/") | 0 |
| 11 | `cargo test --no-default-features --features request-state --lib` in `.llbc/work/crates/rmcp` (293 passed) | 0 |
| 12 | Negative: `codec_constants_agree_with_wire` changed in the source (`"rs1"` → `"rs9"`); apply-patches, cargo test (292 passed, 1 failed) | 0; 101 |
| 13 | Negative through a patch: source restored, `formal/trusted/patches/99-neg.patch` makes the same change in the copy only; apply-patches ("applied 99-neg.patch"), cargo test (1 failed) | 0; 101 |

## Not tested locally

- GitHub Actions itself: path filters, concurrency, `actions/cache` save/restore of `.aeneas/`
  and `~/.rustup/toolchains/...`, `GITHUB_PATH`, the `::error::` annotations.
- The Linux x86_64 runner: the `aeneas-linux-x86_64.tar.gz` download (its digest is committed but
  was never downloaded here), the elan Linux binary, rustup installing the nightly with the
  bundle's components and the `x86_64-unknown-linux-gnu` target from scratch, the preinstalled
  `python3` (>= 3.11), `jq` and `rsync`.
- Whether the runner's environment sets a `CARGO_*` or `RUSTUP_*` variable outside the allowlist
  of `aeneas-translate.sh` (it accepts `CARGO_HOME` and `RUSTUP_HOME`); such a variable would
  stop the script with "refused environment variable".
- A byte-identical translation on a Linux host: every recorded run (pilot, S04a, S18, this one)
  was on macOS arm64. The target triple is fixed to `x86_64-unknown-linux-gnu`, so the output
  should not depend on the host, but CI would be the first Linux-host run.

## Notes for review

- A restored `.aeneas/` is accepted by `aeneas-install.sh` on its stamp (recorded digest equals
  the committed one) and `aeneas -version`, without hashing the binaries again. Cache entries
  can only be written by workflow runs of this repository (a pull request's cache is scoped to
  its ref), so this trusts the repository's own earlier runs.
- The Lean toolchain is downloaded on every run of the translation workflow (only needed because
  `aeneas-install.sh` requires it); it is not cached.

## AI disclosure

Written and run by Claude Code (model claude-opus-5-5) in scratch directories under `/tmp/ci-wf/`;
no file of the repository was changed except the two workflows and this note.

## Review round 1 (2026-11-23) and lead fixes

One independent `mcp-review` agent: no blocking finding; both workflows fail on their S17 cases
(hand edit or extra file under `formal/translation/`; a failing test through a patch) and none
passes vacuously; hardening matches `lean-build.yml`. Applied by the lead:
- R1a-1: both path filters also include `**/Cargo.toml` (any workspace manifest changes the
  workspace-wide resolution, since `Cargo.lock` is not committed); plan Section 5 updated.
- R1a-2: the diff step prints the `::error::` line first and writes the diff to
  `$RUNNER_TEMP/translation.diff` before `head`, so a large diff cannot hide the message (SIGPIPE).
- R1a-3: header and note say "no variable that `aeneas-translate.sh` refuses"; cache paths listed
  in full.
- R1a-4: STATUS and the plan header updated (the workflows exist; not yet run on GitHub).
- R1a-5: the patched tests pass the translation's `--config profile.dev.overflow-checks=true
  --config profile.dev.debug-assertions=true`; re-run locally: 293 passed.
- R1a-6: both headers state the residual risk (a PR's own scripts and dependency build scripts run
  in the checking job; review of `scripts/` is the barrier).

