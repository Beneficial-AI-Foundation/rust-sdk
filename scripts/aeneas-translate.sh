#!/usr/bin/env bash
# Translate the request-state targets of rmcp to Lean with the pinned Charon and
# Aeneas (plan Section 9, "Charon settings"), into formal/translation/.
#
# What is translated is set in [package.metadata.charon] of crates/rmcp/Cargo.toml,
# which the pinned Charon reads itself; this script fixes only the configuration.
# It fails on:
#   - an environment variable that changes how cargo or rustc build the crate (RUSTFLAGS,
#     RUSTC*, RUSTDOC*, CARGO_* other than a short allowlist, RUSTUP_* other than
#     RUSTUP_TOOLCHAIN and RUSTUP_HOME, CHARON_*, AENEAS_*), see check_environment below;
#   - a selected toolchain whose `rustc -vV` is not the pinned nightly (RUSTC_VV_PINNED),
#     or a Charon whose toolchain-version is not the bundle's channel; see
#     check_environment below,
#   - a cargo configuration file (.cargo/config or .cargo/config.toml) in the work copy or in
#     any ancestor directory of it; cargo runs with an isolated CARGO_HOME that has no
#     configuration file (only the registry and git caches of the real one, by symlink),
#   - [profile], [patch], [replace] or cargo-features in the workspace or rmcp manifest,
#   - a build script of rmcp other than the pinned crates/rmcp/build.rs, or one that emits
#     anything (its output file must be empty),
#   - a scratch source (RMCP_SOURCE_ROOT) combined with an output directory inside the
#     repository, or an output directory that contains the repository (both canonicalised),
#   - a work directory (RMCP_LLBC_DIR) that is /, $HOME, the repository or contains one of
#     them, contains or lies inside the source (except <source>/.llbc), or exists, is not
#     empty and has no marker file .rmcp-llbc-dir from an earlier run (the repository's own
#     .llbc excepted); see scripts/llbc-dir-guard.sh,
#   - a dependency version different from the pinned list below (Cargo.lock is
#     git-ignored and never copied into .llbc/work/, so the dependencies are resolved
#     afresh on every run and this is what catches drift; plan Section 4), or any
#     dependency of rmcp in the translated configuration that does not come from the
#     crates.io registry (a path, git or other-registry source, e.g. through [patch]),
#   - a nonzero Charon exit, or an LLBC file flagged with errors,
#   - [package.metadata.charon] with a key other than start_from, hide_marker_traits,
#     exclude, opaque, or with an empty or missing start_from/exclude/opaque list,
#   - Charon options recorded in the LLBC that differ from those lists, or that widen the
#     translation (rustc_args, include, start_from_if_exists, start_from_attribute,
#     extract_opaque_bodies, start_from_pub), or a target other than TARGET_TRIPLE,
#   - a nonzero Aeneas exit,
#   - a target missing from Funs.lean, or any `sorry` in the generated files.
# formal/translation/ is replaced only when every check passes.
#
# Usage:
#   scripts/aeneas-translate.sh            full run: patch, check, translate, check, install
#   scripts/aeneas-translate.sh --check D  only the output checks on an existing output
#                                          directory D (containing Rmcp/Funs.lean)
#   scripts/aeneas-translate.sh --check-deps
#                                          dependency checks only: the environment and
#                                          pinned-rustc checks, apply-patches.sh, the cargo
#                                          configuration and manifest refusals, the crates.io
#                                          source and PINNED_DEPS checks and the build.rs
#                                          digest, exactly as in a full run (same code); then
#                                          it stops before Charon, leaving the checked
#                                          resolution in <work>/Cargo.lock and the isolated
#                                          CARGO_HOME in <llbc>/cargo-home. It needs no Aeneas
#                                          bundle (the toolchain is RUSTUP_TOOLCHAIN, which
#                                          must be unset or the pinned nightly) and writes no
#                                          translation. patched-tests.yml runs it, then
#                                          `cargo test --locked` on that Cargo.lock.
# Every cargo call after the dependency check (cargo metadata, and cargo build through
# Charon) gets --locked, so the translation uses exactly the resolution that was checked.
# The overflow mode is fixed explicitly: every cargo call gets
#   --config profile.dev.overflow-checks=true --config profile.dev.debug-assertions=true
# (command-line --config has the highest precedence in cargo). Aeneas models overflow as
# failure, which is the meaning of the checked arithmetic of this mode.
#
# Environment (default to the repository; used for scratch runs):
#   RMCP_SOURCE_ROOT        workspace to translate (passed to apply-patches.sh)
#   RMCP_LLBC_DIR           work directory (default: <repo>/.llbc)
#   RMCP_TRANSLATION_DEST   output directory (default: <repo>/formal/translation);
#                           required when RMCP_SOURCE_ROOT is not the repository
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LLBC="${RMCP_LLBC_DIR:-$ROOT/.llbc}"
DEST="${RMCP_TRANSLATION_DEST:-$ROOT/formal/translation}"
WORK="$LLBC/work"
CRATE_DIR="$WORK/crates/rmcp"

# The translated configuration. The proofs hold only for it (plan Section 1).
TARGET_TRIPLE="x86_64-unknown-linux-gnu"
# Fixed profile settings, passed to every cargo call (also through Charon).
CONFIG_ARGS=(--config 'profile.dev.overflow-checks=true' --config 'profile.dev.debug-assertions=true')
FEATURE_ARGS=(--target "$TARGET_TRIPLE" --no-default-features --features request-state)
CARGO_ARGS=("${CONFIG_ARGS[@]}" "${FEATURE_ARGS[@]}" --lib)

# crates/rmcp/build.rs (installs git hooks; prints no cargo: directive, so it adds no cfg,
# flag or environment variable to the build; in .llbc/work/ there is no .git, so it does
# nothing). Any change to it must be reviewed and this digest updated.
BUILD_RS_SHA256="31b905abf91292bab290271e993e347e06a1944e6305f742f69dbd01e6b89349"

# Dependency versions the external models of plan Section 4 rely on: hmac, sha2, base64
# resolved at S03; digest, zeroize, chrono, serde_json added at S08-S09, whose models cite their
# sources (formal/trusted/evidence/README.md).
PINNED_DEPS=(
  "hmac 0.13.0"
  "sha2 0.11.1"
  "base64 0.23.1"
  "digest 0.11.3"
  "zeroize 1.9.2"
  "chrono 0.4.45"
  "serde_json 1.0.154"
)

# Lean names of the targets (plan Section 2): each needs a `def` in Funs.lean.
TARGETS=(
  model.request_state_wire.b64_len                          # W01
  model.request_state_wire.key_length_ok                    # W02
  model.request_state_wire.check_kid_len                    # W03
  model.request_state_wire.bytes_eq                         # W04
  model.request_state_wire.next_dot                         # W05
  model.request_state_wire.component_count                  # W06
  model.request_state_wire.version_of                       # W07
  model.request_state_wire.parse_rs1                        # W08
  model.request_state_wire.parse_rs2                        # W09
  model.request_state_wire.transcript_v1                    # W10
  model.request_state_wire.transcript_v2                    # W11
  model.request_state_wire.decode_expiry                    # W12
  model.request_state_wire.is_expired                       # W13
  model.request_state_wire.open_frame                       # W14
  model.request_state_wire.frame                            # W15
  model.request_state.RequestStateCodec.open_authenticated_body  # E01
  model.request_state.RequestStateCodec.b64_len             # E02
  model.request_state.RequestStateCodec.validate_key_length # E03
  model.request_state.RequestStateCodec.validate_config_kid # E04
  model.request_state.RequestStateCodec.seal_rs1            # E07
  model.request_state.RequestStateCodec.seal_rs2            # E08
  model.request_state.RequestStateCodec.open_rs1_at         # E09
  model.request_state.RequestStateCodec.rs1_fallbacks_verify  # E09a
  model.request_state.RequestStateCodec.open_rs2_at         # E10
  model.request_state.RequestStateCodec.open_at             # E11
)

log() { printf '[aeneas-translate] %s\n' "$*"; }
die() { printf '[aeneas-translate] error: %s\n' "$*" >&2; exit 1; }

# Output checks on a directory holding Rmcp/Funs.lean: every target has a `def`
# (a real body, not an opaque declaration), and no generated file mentions `sorry`.
check_output() {
  local out="$1" funs="$1/Rmcp/Funs.lean" missing=() t pat sorries f rc hit
  [[ -f "$funs" ]] || die "no Rmcp/Funs.lean in $out"
  for t in "${TARGETS[@]}"; do
    pat="^(noncomputable )?(private )?def ${t//./\\.}([[:space:]]|$)"
    grep -Eq "$pat" "$funs" || missing+=("$t")
  done
  if [[ ${#missing[@]} -gt 0 ]]; then
    printf '[aeneas-translate] missing target: %s\n' "${missing[@]}" >&2
    die "${#missing[@]} target(s) have no definition in Funs.lean"
  fi
  # grep: exit 0 = match, 1 = no match, anything else = error (not swallowed).
  sorries=""
  while IFS= read -r -d '' f; do
    rc=0
    hit="$(grep -HnwE 'sorry|sorryAx' "$f")" || rc=$?
    case $rc in
      0) sorries+="$hit"$'\n' ;;
      1) ;;
      *) die "grep failed on $f (exit $rc)" ;;
    esac
  done < <(find "$out" -name '*.lean' -print0)
  if [[ -n "$sorries" ]]; then
    printf '%s' "$sorries" >&2
    die "generated files contain sorry"
  fi
  log "all ${#TARGETS[@]} targets defined in Funs.lean; no sorry"
}

MODE=full
if [[ "${1:-}" == "--check" ]]; then
  [[ $# -eq 2 ]] || die "usage: $0 --check <output-dir>"
  check_output "$2"
  exit 0
elif [[ "${1:-}" == "--check-deps" ]]; then
  [[ $# -eq 1 ]] || die "usage: $0 --check-deps"
  MODE=deps
else
  [[ $# -eq 0 ]] || die "usage: $0 [--check <output-dir> | --check-deps]"
fi

# Environment variables that change what cargo or rustc build are refused (not unset), so
# that a CI log shows why a run stopped. Allowed: CARGO_HOME (its configuration is not used,
# see below), CARGO_TARGET_DIR (overridden), CARGO_TERM_*, CARGO_NET_*, CARGO_HTTP_*,
# CARGO_INCREMENTAL, CARGO_REGISTRIES_CRATES_IO_PROTOCOL (how crates.io is fetched; the
# source check below still requires crates.io). Everything else named CARGO_* (config keys
# such as CARGO_PROFILE_*, CARGO_BUILD_*, CARGO_TARGET_<triple>_*, CARGO_ENCODED_RUSTFLAGS,
# CARGO_UNSTABLE_*), RUSTFLAGS, RUSTC* (RUSTC, RUSTC_WRAPPER, RUSTC_WORKSPACE_WRAPPER,
# RUSTC_BOOTSTRAP, ...), RUSTDOC*, CHARON_*, AENEAS_* and RUSTUP_* other than RUSTUP_TOOLCHAIN
# and RUSTUP_HOME (e.g. RUSTUP_DIST_SERVER, another source of toolchains) is refused.
# RUSTUP_TOOLCHAIN is overridden below. RUSTUP_HOME is allowed (container images set it);
# the toolchain it yields is checked below (`rustc -vV` must report the pinned nightly).
# RUST_LOG and RUST_BACKTRACE only affect logging.
check_environment() {
  local v bad=()
  while IFS= read -r v; do
    case "$v" in
      CARGO_HOME|CARGO_TARGET_DIR|CARGO_INCREMENTAL|CARGO_REGISTRIES_CRATES_IO_PROTOCOL) ;;
      CARGO_TERM_*|CARGO_NET_*|CARGO_HTTP_*) ;;
      RUSTUP_TOOLCHAIN|RUSTUP_HOME) ;;
      CARGO*|__CARGO*|RUSTFLAGS*|RUSTC*|RUSTDOC*|RUSTUP_*|CHARON_*|AENEAS_*) bad+=("$v") ;;
    esac
  done < <(compgen -e)
  if [[ ${#bad[@]} -gt 0 ]]; then
    printf '[aeneas-translate] refused environment variable: %s\n' "${bad[@]}" >&2
    die "unset the variable(s) above: they change how the crate is built (see check_environment)"
  fi
}
check_environment

# canon_path, within, check_llbc_dir.
# shellcheck source=scripts/llbc-dir-guard.sh
. "$ROOT/scripts/llbc-dir-guard.sh"

# The output directory is replaced with rsync --delete. It must never contain the
# repository (e.g. RMCP_TRANSLATION_DEST=<repo>/formal would delete formal/), and with a
# scratch source it must lie outside the repository, so that a scratch translation never
# overwrites formal/translation/ (paths canonicalised: symlinks, `.`, `..`).
# (--check-deps writes no output, so it skips these checks.)
ROOT_C="$(canon_path "$ROOT")"
if [[ "$MODE" == full ]]; then
  DEST_C="$(canon_path "$DEST")"
  REPO_DEST_C="$(canon_path "$ROOT/formal/translation")"
  within "$ROOT_C" "$DEST_C" && die "RMCP_TRANSLATION_DEST ($DEST_C) contains the repository"
  if [[ -n "${RMCP_SOURCE_ROOT:-}" && "$(canon_path "$RMCP_SOURCE_ROOT")" != "$ROOT_C" ]]; then
    within "$DEST_C" "$ROOT_C" \
      && die "RMCP_SOURCE_ROOT is not this repository; set RMCP_TRANSLATION_DEST to a scratch directory outside the repository (got $DEST_C)"
  elif [[ "$DEST_C" != "$REPO_DEST_C" ]] && within "$DEST_C" "$ROOT_C"; then
    die "RMCP_TRANSLATION_DEST ($DEST_C) is inside the repository but is not formal/translation"
  fi
fi

# The work directory gets rsync --delete (work/) and rm -rf (out/, cargo-home/); see
# scripts/llbc-dir-guard.sh for what is refused. On success it holds the marker file.
LLBC="$(check_llbc_dir "$ROOT" "$LLBC" "${RMCP_SOURCE_ROOT:-$ROOT}")" || die "refused RMCP_LLBC_DIR (see above)"
export RMCP_LLBC_DIR="$LLBC"
WORK="$LLBC/work"
CRATE_DIR="$WORK/crates/rmcp"

# The pinned bundle (installed by aeneas-install.sh from the rev in formal/lakefile.toml).
# Every table header starts a new block and clears `name`/`rev` (same awk as aeneas-install.sh).
# --check-deps does not use the bundle: its channel is RUSTUP_TOOLCHAIN (default: the pinned
# nightly), checked against the same pin below.
if [[ "$MODE" == full ]]; then
  TAG="$(awk '
    /^[[:space:]]*\[/ { in_req = ($0 ~ /^[[:space:]]*\[\[require\]\]/); is_aeneas = 0; rev = ""; next }
    in_req && /^[[:space:]]*name[[:space:]]*=[[:space:]]*"aeneas"[[:space:]]*(#.*)?$/ { is_aeneas = 1 }
    in_req && /^[[:space:]]*rev[[:space:]]*=/ { rev = $0 }
    in_req && is_aeneas && rev != "" { sub(/^[^"]*"/, "", rev); sub(/".*$/, "", rev); print rev; exit }
  ' "$ROOT/formal/lakefile.toml")"
  BUNDLE="$ROOT/.aeneas/$TAG"
  [[ -n "$TAG" && -f "$BUNDLE/.installed" ]] || die "bundle ${TAG:-?} not installed; run scripts/aeneas-install.sh"
  CHARON="$BUNDLE/charon"
  AENEAS="$BUNDLE/aeneas"
  RUST_CHANNEL="$(sed -n 's/^channel[[:space:]]*=[[:space:]]*"\(.*\)"/\1/p' "$BUNDLE/rust-toolchain")"
  CHANNEL_FROM="bundle channel"
else
  RUST_CHANNEL="${RUSTUP_TOOLCHAIN:-nightly-2026-06-01}"
  CHANNEL_FROM="RUSTUP_TOOLCHAIN"
fi
export RUSTUP_TOOLCHAIN="$RUST_CHANNEL"
# The toolchain actually selected (RUSTUP_HOME may point at any rustup home): the `rustc` on
# PATH, which cargo runs and whose sysroot provides the librustc_driver that charon-driver
# loads, must report the pinned nightly; Charon must have been built for the same channel.
# RUSTC_VV_PINNED is the `rustc -vV` of nightly-2026-06-01 (commit date 2026-05-31); it
# changes with the Aeneas rev ("Pinned toolchain").
[[ "$RUST_CHANNEL" == "nightly-2026-06-01" ]] \
  || die "$CHANNEL_FROM $RUST_CHANNEL, but RUSTC_VV_PINNED is for nightly-2026-06-01 (update it with the Aeneas rev)"
RUSTC_VV_PINNED="commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65 commit-date: 2026-05-31 release: 1.98.0-nightly"
command -v rustc >/dev/null 2>&1 || die "rustc not found"
rustc_vv="$(rustc -vV)" || die "rustc -vV failed for toolchain $RUST_CHANNEL${RUSTUP_HOME:+ (RUSTUP_HOME=$RUSTUP_HOME)}"
got_vv="$(awk -F': ' '$1 == "release" || $1 == "commit-hash" || $1 == "commit-date" { printf "%s%s: %s", (n++ ? " " : ""), $1, $2 }' <<<"$rustc_vv")"
[[ "$got_vv" == "$RUSTC_VV_PINNED" ]] \
  || die "the selected rustc reports '$got_vv', expected '$RUSTC_VV_PINNED' (toolchain $RUST_CHANNEL${RUSTUP_HOME:+, RUSTUP_HOME=$RUSTUP_HOME})"
export CARGO_TARGET_DIR="$LLBC/target"
command -v jq >/dev/null 2>&1 || die "jq not found"
if [[ "$MODE" == full ]]; then
  # The bundle's macOS binaries reference libiconv/zlib under /nix/store; the same
  # libraries exist in /usr/lib (see aeneas-install.sh).
  if [[ "$(uname -s)" == "Darwin" ]]; then
    export DYLD_FALLBACK_LIBRARY_PATH="/usr/lib${DYLD_FALLBACK_LIBRARY_PATH:+:$DYLD_FALLBACK_LIBRARY_PATH}"
  fi
  charon_tc="$("$CHARON" toolchain-version)" || die "charon toolchain-version failed"
  [[ "$charon_tc" == "$RUST_CHANNEL" ]] || die "charon was built for $charon_tc, the bundle pins $RUST_CHANNEL"
  log "aeneas $TAG, charon $("$CHARON" version), rust $RUST_CHANNEL (rustc $got_vv)"
else
  log "dependency check only (--check-deps), rust $RUST_CHANNEL (rustc $got_vv)"
fi

# 1. Fresh copy of the workspace with the translation patches applied (apply-patches.sh
# refuses a source with a .cargo/config* file and never copies .cargo/).
"$ROOT/scripts/apply-patches.sh"
cd "$CRATE_DIR"

# Cargo configuration. Cargo reads .cargo/config{,.toml} in the working directory and every
# ancestor, then $CARGO_HOME/config{,.toml}. Any such file in the work copy or an ancestor of
# the crate directory is refused; $CARGO_HOME is replaced by an isolated directory that
# holds only symlinks to the registry and git caches of the real one (no configuration, no
# credentials), so a ~/.cargo/config.toml is not read either.
cfg_hits="$(find "$WORK" -type d -name .cargo -print)"
[[ -z "$cfg_hits" ]] || die "cargo configuration directory in the work copy: $cfg_hits"
d="$(pwd -P)"
while :; do
  for f in "$d/.cargo/config" "$d/.cargo/config.toml"; do
    [[ ! -e "$f" ]] || die "cargo configuration file $f would apply to the translation; remove it or move the work directory (RMCP_LLBC_DIR)"
  done
  [[ "$d" != "/" ]] || break
  d="$(dirname "$d")"
done
REAL_CARGO_HOME="${CARGO_HOME:-$HOME/.cargo}"
ISO_CARGO_HOME="$LLBC/cargo-home"
rm -rf "$ISO_CARGO_HOME"
mkdir -p "$ISO_CARGO_HOME" "$REAL_CARGO_HOME/registry" "$REAL_CARGO_HOME/git"
ln -s "$REAL_CARGO_HOME/registry" "$ISO_CARGO_HOME/registry"
ln -s "$REAL_CARGO_HOME/git" "$ISO_CARGO_HOME/git"
export CARGO_HOME="$ISO_CARGO_HOME"
log "cargo: no configuration file in the work copy or its ancestors; isolated CARGO_HOME $ISO_CARGO_HOME"

# Manifests: no [profile] (it could change overflow-checks for rmcp through a package
# override), no [patch]/[replace] (dependency sources) and no cargo-features (unstable
# manifest keys such as profile rustflags), in the workspace and the rmcp manifest.
command -v python3 >/dev/null 2>&1 || die "python3 not found"
python3 -I -c '
import sys
if sys.version_info < (3, 11): sys.exit("python3 >= 3.11 needed (tomllib)")
import tomllib
bad = []
for path in sys.argv[1:]:
    with open(path, "rb") as f: m = tomllib.load(f)
    bad += [f"{path}: [{k}]" for k in ("profile", "patch", "replace", "cargo-features") if k in m]
if bad: sys.exit("refused manifest key(s): " + ", ".join(bad))
' "$WORK/Cargo.toml" "$CRATE_DIR/Cargo.toml" || die "manifest check failed"
log "manifests: no [profile], [patch], [replace] or cargo-features"

# 2. Dependencies, resolved for the translated configuration: every dependency of rmcp
# must come from crates.io (`cargo tree` prints a source only for a path, git or
# other-registry package), and the pinned crates must have the pinned versions. This
# `cargo tree` writes <work>/Cargo.lock (the copy has none); every later cargo call uses it
# with --locked.
[[ ! -e "$WORK/Cargo.lock" ]] || die "$WORK/Cargo.lock exists before resolution (apply-patches.sh never copies one)"
tree="$(cargo tree --color never "${CONFIG_ARGS[@]}" "${FEATURE_ARGS[@]}" -e normal --prefix none --format '{p}' \
  | sed -e 's/ (\*)$//' -e 's/ (proc-macro)$//' | sort -u)"
foreign="$(awk -v root="rmcp" '$1 != root && / \(/' <<<"$tree")"
if [[ -n "$foreign" ]]; then
  printf '%s\n' "$foreign" >&2
  die "dependencies not from crates.io (path, git or other registry)"
fi
# The same source check over build and dev dependencies too: cargo test (patched-tests.yml)
# also builds the dev-dependencies, so none of them may come from a path, git or other
# registry either (review of PR #9).
alltree="$(cargo tree --color never "${CONFIG_ARGS[@]}" "${FEATURE_ARGS[@]}" -e normal,build,dev --prefix none \
  --format '{p}' | sed -e 's/ (\*)$//' -e 's/ (proc-macro)$//' | sort -u)"
foreign="$(awk -v root="rmcp" '$1 != root && / \(/' <<<"$alltree")"
if [[ -n "$foreign" ]]; then
  printf '%s\n' "$foreign" >&2
  die "build or dev dependencies not from crates.io (path, git or other registry)"
fi
rootline="$(awk '$1 == "rmcp"' <<<"$tree")"
[[ "$rootline" == "rmcp v"*" ($(pwd -P))" ]] || die "unexpected rmcp package(s) in the tree: $rootline"
for entry in "${PINNED_DEPS[@]}"; do
  name="${entry% *}"
  want="${entry#* }"
  got="$(awk -v n="$name" '$1 == n { sub(/^v/, "", $2); print $2 }' <<<"$tree" | sort -u | tr '\n' ' ')"
  got="${got% }"
  [[ "$got" == "$want" ]] || die "dependency $name resolves to '${got:-none}', pinned $want"
  log "dependency $name $got from crates.io (pinned)"
done

# 3. [package.metadata.charon], checked before Charon runs. It may hold only the four
# documented keys, and the three lists must be present and non-empty. The pinned
# Charon's TomlConfig ignores unknown keys (a misspelt key would be dropped silently)
# and also accepts keys that widen the translation (include, start_from_pub,
# extract_opaque_bodies, start_from_if_exists, start_from_attribute, rustc.flags);
# none of them is allowed here.
pkg="$(cargo metadata "${CONFIG_ARGS[@]}" --locked --format-version 1 --no-deps \
  | jq -c '[.packages[] | select(.name == "rmcp")] | if length == 1 then .[0] else error("rmcp package count \(length)") end')"
# Build script: exactly crates/rmcp/build.rs, with the pinned digest.
builds="$(jq -r '[.targets[] | select(.kind | index("custom-build")) | .src_path] | join(" ")' <<<"$pkg")"
[[ "$builds" == "$(pwd -P)/build.rs" || "$builds" == "$CRATE_DIR/build.rs" ]] \
  || die "rmcp build script(s) '$builds', expected crates/rmcp/build.rs"
if command -v sha256sum >/dev/null 2>&1; then got_sha="$(sha256sum build.rs | awk '{print $1}')"
else got_sha="$(shasum -a 256 build.rs | awk '{print $1}')"; fi
[[ "$got_sha" == "$BUILD_RS_SHA256" ]] \
  || die "crates/rmcp/build.rs has sha256 $got_sha, pinned $BUILD_RS_SHA256 (review it, then update BUILD_RS_SHA256)"
log "build script crates/rmcp/build.rs (pinned sha256)"
if [[ "$MODE" == deps ]]; then
  log "dependency checks passed; checked resolution in $WORK/Cargo.lock (use cargo --locked), CARGO_HOME $ISO_CARGO_HOME"
  exit 0
fi
meta="$(jq -c '.metadata.charon' <<<"$pkg")"
[[ "$meta" != "null" && -n "$meta" ]] || die "no [package.metadata.charon] in crates/rmcp/Cargo.toml"
extra="$(jq -c '(keys - ["start_from", "hide_marker_traits", "exclude", "opaque"])' <<<"$meta")"
[[ "$extra" == "[]" ]] || die "[package.metadata.charon] has unexpected key(s) $extra"
for key in start_from exclude opaque; do
  jq -e --arg k "$key" '(.[$k] | type) == "array" and (.[$k] | length) > 0 and all(.[$k][]; type == "string")' \
    <<<"$meta" >/dev/null || die "[package.metadata.charon].$key is missing, empty or not a list of strings"
done
jq -e '(.hide_marker_traits // true) | type == "boolean"' <<<"$meta" >/dev/null \
  || die "[package.metadata.charon].hide_marker_traits is not a boolean"

# 4. Charon. It reads [package.metadata.charon] from ./Cargo.toml.
mkdir -p "$LLBC"
LLBC_FILE="$LLBC/rmcp.llbc"
rm -f "$LLBC_FILE"
set +e
"$CHARON" cargo --preset=aeneas --dest-file "$LLBC_FILE" -- "${CARGO_ARGS[@]}" --locked
rc=$?
set -e
[[ $rc -eq 0 ]] || die "charon exited with $rc"
[[ "$(jq -r '.has_errors' "$LLBC_FILE")" == "false" ]] || die "charon reported errors in $LLBC_FILE"
# The build script ran for the target and printed nothing (no cfg, flag or env directive).
outs=()
while IFS= read -r f; do outs+=("$f"); done \
  < <(find "$CARGO_TARGET_DIR/$TARGET_TRIPLE" -path '*/build/rmcp-*/output' -type f 2>/dev/null | sort)
[[ ${#outs[@]} -gt 0 ]] || die "no build-script output of rmcp under $CARGO_TARGET_DIR/$TARGET_TRIPLE"
for f in "${outs[@]}"; do
  [[ ! -s "$f" ]] || { cat "$f" >&2; die "rmcp build script emitted directives ($f)"; }
done

# The options recorded in the LLBC (translated.options) must be exactly those lists ...
for key in start_from opaque exclude; do
  want="$(jq -c --arg k "$key" '.[$k] | sort' <<<"$meta")"
  got="$(jq -c --arg k "$key" '.translated.options[$k] | sort' "$LLBC_FILE")"
  [[ "$want" == "$got" ]] || die "charon option $key is $got, but Cargo.toml says $want"
done
# ... with nothing that widens the translation ...
for check in 'rustc_args == []' 'include == []' 'start_from_if_exists == []' \
             'start_from_attribute == []' 'extract_opaque_bodies == false' 'start_from_pub == false'; do
  jq -e ".translated.options | .$check" "$LLBC_FILE" >/dev/null \
    || die "charon option check failed: $check (got $(jq -c ".translated.options.${check%% *}" "$LLBC_FILE"))"
done
# ... and for the fixed target only.
targets="$(jq -c '[.translated.target_information[].key]' "$LLBC_FILE")"
[[ "$targets" == "[\"$TARGET_TRIPLE\"]" ]] || die "LLBC target information is $targets, expected [\"$TARGET_TRIPLE\"]"
log "charon applied [package.metadata.charon] (start_from, opaque, exclude); no widening options; target $TARGET_TRIPLE"

# 5. Aeneas, into a scratch directory; formal/translation/ is replaced only on success.
OUT="$LLBC/out"
rm -rf "$OUT"
mkdir -p "$OUT"
set +e
"$AENEAS" -backend lean -split-files -emit-json -no-progress-bar \
  -dest "$OUT" -subdir Rmcp "$LLBC_FILE"
rc=$?
set -e
[[ $rc -eq 0 ]] || die "aeneas exited with $rc"

# 6. Output checks, then install. rsync --delete replaces DEST; as a second guard (besides the
# path checks at the top) DEST must be absent, empty, or hold only an earlier output
# (Rmcp/ and translation.json), so that a wrong path can never delete anything else.
check_output "$OUT"
if [[ -d "$DEST_C" ]]; then
  others="$(find "$DEST_C" -mindepth 1 -maxdepth 1 ! -name Rmcp ! -name translation.json -print | head -5)"
  [[ -z "$others" ]] || die "RMCP_TRANSLATION_DEST ($DEST_C) holds files that are not a translation output: $others"
elif [[ -e "$DEST_C" ]]; then
  die "RMCP_TRANSLATION_DEST ($DEST_C) is not a directory"
fi
mkdir -p "$DEST_C"
rsync -a --delete --checksum "$OUT/" "$DEST_C/"
log "translation written to $DEST"
