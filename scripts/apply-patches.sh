#!/usr/bin/env bash
# Copy the workspace into .llbc/work/ and apply the translation patches of
# formal/trusted/patches/*.patch to the copy, in file-name order.
#
# The real source is never patched (formal/CONTRIBUTING.md,
# "Translation patches"). With no patches, .llbc/work/ is a plain copy.
#
# Cargo.lock is not copied, and any Cargo.lock left in .llbc/work/ by an earlier run is
# deleted: Cargo.lock is git-ignored, so CI always resolves the dependencies afresh, and a
# local run must do the same for the pinned-version check of aeneas-translate.sh to mean
# the same thing on both (plan Section 4). Resolving needs the crates.io index.
#
# No cargo configuration is copied: the copy skips every .cargo/ directory, and the script
# fails if the source has a .cargo/config or .cargo/config.toml anywhere in the copied tree
# (it would change how the crate is built; scripts/aeneas-translate.sh also refuses one in
# any ancestor of the work directory).
#
# Usage: scripts/apply-patches.sh
# Environment (both default to the repository; used for scratch runs):
#   RMCP_SOURCE_ROOT   workspace to copy (must contain Cargo.toml and crates/rmcp)
#   RMCP_NO_PATCHES    1: copy without applying any patch (scripts/check-original-linkage.sh)
#   RMCP_LLBC_DIR      directory holding work/ (default: <repo>/.llbc); refused if it is /,
#                      $HOME, the repository or an ancestor, or an existing non-empty
#                      directory without the marker .rmcp-llbc-dir (scripts/llbc-dir-guard.sh)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SRC="${RMCP_SOURCE_ROOT:-$ROOT}"
LLBC="${RMCP_LLBC_DIR:-$ROOT/.llbc}"
WORK="$LLBC/work"
PATCHES="$ROOT/formal/trusted/patches"

log() { printf '[apply-patches] %s\n' "$*"; }
die() { printf '[apply-patches] error: %s\n' "$*" >&2; exit 1; }

[[ -f "$SRC/Cargo.toml" && -f "$SRC/crates/rmcp/Cargo.toml" ]] || die "$SRC is not the rmcp workspace"
command -v rsync >/dev/null 2>&1 || die "rsync not found"

# The copy below runs rsync --delete into $LLBC/work: refuse a work directory that is /,
# $HOME, the repository, contains one of them or the source, lies inside the source (except
# <source>/.llbc), or exists non-empty without the marker of an earlier run
# (scripts/llbc-dir-guard.sh).
# shellcheck source=scripts/llbc-dir-guard.sh
. "$ROOT/scripts/llbc-dir-guard.sh"
LLBC="$(check_llbc_dir "$ROOT" "$LLBC" "$SRC")" || die "refused RMCP_LLBC_DIR (see above)"
WORK="$LLBC/work"

# Same exclusions as the rsync below.
cfg="$(find "$SRC" \( -path "$SRC/.git" -o -path "$SRC/target" -o -path "$SRC/.llbc" \
  -o -path "$SRC/.aeneas" -o -path "$SRC/formal" -o -path "$SRC/.claude" -o -name node_modules \) -prune \
  -o -path '*/.cargo/config' -print -o -path '*/.cargo/config.toml' -print)"
if [[ -n "$cfg" ]]; then
  printf '%s\n' "$cfg" >&2
  die "cargo configuration file(s) in the source; they would change the translated build"
fi

mkdir -p "$WORK"
# Mirror the workspace exactly (deleting stale files) so that every run starts from
# the unpatched source. Build outputs, tool installs, the Lean project and every
# Cargo.lock are skipped; --delete-excluded also removes them from an earlier copy.
rsync -a --delete --delete-excluded \
  --exclude '/.git/' --exclude '/target/' --exclude '/.llbc/' --exclude '/.aeneas/' \
  --exclude '/formal/' --exclude '/.claude/' --exclude 'node_modules/' \
  --exclude 'Cargo.lock' --exclude '.cargo/' \
  "$SRC/" "$WORK/"
[[ ! -e "$WORK/Cargo.lock" ]] || die "Cargo.lock still present in $WORK"
# rsync's '.cargo/' exclusion matches directories only: a symlink named .cargo is copied (as
# a symlink). Any .cargo entry in the copy is refused.
cargo_hits="$(find "$WORK" -name .cargo -print)"
[[ -z "$cargo_hits" ]] || die ".cargo copied into $WORK (a symlink named .cargo in the source?): $cargo_hits"
log "copied ${SRC} to ${WORK}"

# RMCP_NO_PATCHES=1 (used only by scripts/check-original-linkage.sh, plan Section 19): copy the
# workspace without applying any patch, to translate the unmodified source.
if [[ "${RMCP_NO_PATCHES:-}" == 1 ]]; then
  log "RMCP_NO_PATCHES=1: no patch applied (unmodified source)"
  exit 0
fi
[[ -z "${RMCP_NO_PATCHES:-}" ]] || die "RMCP_NO_PATCHES must be unset or 1"
shopt -s nullglob
patches=("$PATCHES"/*.patch)
shopt -u nullglob
if [[ ${#patches[@]} -eq 0 ]]; then
  log "no patches in formal/trusted/patches/"
  exit 0
fi
for p in "${patches[@]}"; do
  patch -p1 -F 0 -d "$WORK" --forward --batch --dry-run -i "$p" >/dev/null \
    || die "patch $(basename "$p") does not apply cleanly"
  patch -p1 -F 0 -d "$WORK" --forward --batch -i "$p" >/dev/null
  log "applied $(basename "$p")"
done
