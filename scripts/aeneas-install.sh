#!/usr/bin/env bash
# Install the pinned Aeneas release bundle (Aeneas, Charon, charon-driver) into
# .aeneas/<tag>/, together with the Rust nightly and the Lean toolchain it names.
#
# The tag is read from the `rev` of the `aeneas` requirement in
# formal/lakefile.toml, the single source of truth for the toolchain
# (plan Section 5, "Toolchain"). Rerunning the script is a no-op once the
# bundle, the toolchains and formal/lean-toolchain are in place.
#
# The downloaded bundle must match the sha256 committed for <tag>/<asset> in
# formal/trusted/aeneas-bundle.sha256; the script fails on a mismatch or a missing entry.
#
# Usage: scripts/aeneas-install.sh
#        scripts/aeneas-install.sh --verify FILE KEY   only the digest check of FILE against
#                                                      the committed entry KEY (<tag>/<asset>)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LAKEFILE="$ROOT/formal/lakefile.toml"
REPO="AeneasVerif/aeneas"
# Extra Rust target needed by the fixed translation configuration (scripts/aeneas-translate.sh).
TRANSLATION_TARGET="x86_64-unknown-linux-gnu"

log() { printf '[aeneas-install] %s\n' "$*"; }
die() { printf '[aeneas-install] error: %s\n' "$*" >&2; exit 1; }

DIGESTS="$ROOT/formal/trusted/aeneas-bundle.sha256"

# Print the `rev` of the [[require]] block whose name is "aeneas". Every table header
# starts a new block and clears `name`/`rev`, so a `rev` of another requirement is never used.
read_tag() {
  awk '
    /^[[:space:]]*\[/ { in_req = ($0 ~ /^[[:space:]]*\[\[require\]\]/); is_aeneas = 0; rev = ""; next }
    in_req && /^[[:space:]]*name[[:space:]]*=[[:space:]]*"aeneas"[[:space:]]*(#.*)?$/ { is_aeneas = 1 }
    in_req && /^[[:space:]]*rev[[:space:]]*=/ { rev = $0 }
    in_req && is_aeneas && rev != "" { sub(/^[^"]*"/, "", rev); sub(/".*$/, "", rev); print rev; exit }
  ' "$1"
}

sha256_of() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d' ' -f1
  else shasum -a 256 "$1" | cut -d' ' -f1; fi
}

# Print the committed sha256 for KEY (<tag>/<asset>); fail if there is not exactly one.
expected_sha256() {
  local key="$1" hits
  [[ -f "$DIGESTS" ]] || die "missing $DIGESTS"
  hits="$(awk -v k="$key" '$1 !~ /^#/ && NF == 2 && $2 == k { print $1 }' "$DIGESTS")"
  [[ -n "$hits" ]] || die "no committed sha256 for $key in ${DIGESTS#"$ROOT"/}"
  [[ "$hits" != *$'\n'* ]] || die "several committed sha256 entries for $key"
  [[ "$hits" =~ ^[0-9a-f]{64}$ ]] || die "malformed committed sha256 for $key: $hits"
  printf '%s\n' "$hits"
}

# Fail unless FILE has the committed sha256 for KEY; print the digest.
verify_sha256() {
  local file="$1" key="$2" want got
  want="$(expected_sha256 "$key")"
  got="$(sha256_of "$file")"
  [[ "$got" == "$want" ]] || die "sha256 mismatch for $key: got $got, committed $want"
  printf '%s\n' "$got"
}

# Print the entries of `components = [ ... ]` in a rust-toolchain file, separated by
# spaces. The list may span several lines; `#` comments are dropped. POSIX awk only.
read_components() {
  awk '
    !on && /^[[:space:]]*components[[:space:]]*=/ { on = 1; sub(/^[^=]*=/, "") }
    on { line = $0; sub(/#.*/, "", line); buf = buf " " line; if (line ~ /\]/) exit }
    END { gsub(/\[/, " ", buf); gsub(/\]/, " ", buf); gsub(/"/, " ", buf); gsub(/,/, " ", buf)
          n = split(buf, a, /[[:space:]]+/); out = ""
          for (i = 1; i <= n; i++) if (a[i] != "") out = out (out == "" ? "" : " ") a[i]
          print out }
  ' "$1"
}

if [[ "${1:-}" == "--verify" ]]; then
  [[ $# -eq 3 ]] || die "usage: $0 --verify FILE KEY"
  verify_sha256 "$2" "$3" >/dev/null
  log "sha256 of $2 matches the committed entry for $3"
  exit 0
fi
[[ $# -eq 0 ]] || die "usage: $0 [--verify FILE KEY]"

TAG="$(read_tag "$LAKEFILE")"
[[ -n "$TAG" ]] || die "no rev for the aeneas requirement in $LAKEFILE"

case "$(uname -s)-$(uname -m)" in
  Darwin-arm64) ASSET="aeneas-macos-aarch64.tar.gz" ;;
  Linux-x86_64) ASSET="aeneas-linux-x86_64.tar.gz" ;;
  Linux-aarch64 | Linux-arm64) ASSET="aeneas-linux-aarch64.tar.gz" ;;
  *) die "no Aeneas release bundle for $(uname -s)-$(uname -m)" ;;
esac

DEST="$ROOT/.aeneas/$TAG"
STAMP="$DEST/.installed"
changed=0

# The bundle's macOS binaries reference libiconv/zlib under /nix/store; the same
# libraries exist in /usr/lib, so let dyld fall back to it.
if [[ "$(uname -s)" == "Darwin" ]]; then
  export DYLD_FALLBACK_LIBRARY_PATH="/usr/lib${DYLD_FALLBACK_LIBRARY_PATH:+:$DYLD_FALLBACK_LIBRARY_PATH}"
fi

# 1. The release bundle. An installed bundle counts only if its recorded digest is the
# committed one, so changing the committed value forces a fresh download and check.
EXPECTED="$(expected_sha256 "$TAG/$ASSET")"
if [[ -f "$STAMP" ]] && grep -qx "asset=$ASSET" "$STAMP" && grep -qx "sha256=$EXPECTED" "$STAMP"; then
  log "bundle $TAG ($ASSET) already installed in ${DEST#"$ROOT"/}"
else
  command -v curl >/dev/null 2>&1 || die "curl not found"
  tmp="$(mktemp -d)"
  trap 'rm -rf "$tmp"' EXIT
  log "downloading $ASSET"
  curl -fsSL --retry 3 -o "$tmp/$ASSET" "https://github.com/$REPO/releases/download/$TAG/$ASSET"
  actual="$(verify_sha256 "$tmp/$ASSET" "$TAG/$ASSET")"
  log "sha256 $actual matches ${DIGESTS#"$ROOT"/}"
  rm -rf "$DEST.partial"
  mkdir -p "$DEST.partial"
  tar -xzf "$tmp/$ASSET" -C "$DEST.partial"
  for f in aeneas charon charon-driver rust-toolchain backends/lean/lean-toolchain; do
    [[ -e "$DEST.partial/$f" ]] || die "bundle $ASSET lacks $f"
  done
  printf 'tag=%s\nasset=%s\nsha256=%s\n' "$TAG" "$ASSET" "$actual" > "$DEST.partial/.installed"
  rm -rf "$DEST"
  mv "$DEST.partial" "$DEST"
  changed=1
  log "installed bundle in ${DEST#"$ROOT"/}"
fi

# The bundle must be the release it claims to be.
aeneas_version="$("$DEST/aeneas" -version 2>&1 | head -n1)"
[[ "$aeneas_version" == "aeneas $TAG" ]] || die "bundle aeneas reports '$aeneas_version', expected 'aeneas $TAG'"
charon_version="$("$DEST/charon" version)" || die "bundle charon does not run"

# 2. The Rust nightly named by the bundle's rust-toolchain file.
command -v rustup >/dev/null 2>&1 || die "rustup not found"
channel="$(sed -n 's/^channel[[:space:]]*=[[:space:]]*"\(.*\)"/\1/p' "$DEST/rust-toolchain")"
[[ -n "$channel" ]] || die "no channel in the bundle's rust-toolchain"
components="$(read_components "$DEST/rust-toolchain")"
if ! rustup toolchain list | grep -q "^$channel-"; then
  log "installing Rust $channel"
  rustup toolchain install "$channel" --profile minimal
  changed=1
fi
installed_components="$(rustup component list --installed --toolchain "$channel")"
[[ -n "$components" ]] || die "no components in the bundle's rust-toolchain"
for c in $components; do
  [[ "$c" =~ ^[A-Za-z0-9_-]+$ ]] || die "unexpected component name '$c' in the bundle's rust-toolchain"
  if ! grep -Eq "^$c(-|\$)" <<<"$installed_components"; then
    log "adding component $c to $channel"
    rustup component add --toolchain "$channel" "$c"
    changed=1
  fi
done
if ! rustup target list --installed --toolchain "$channel" | grep -qx "$TRANSLATION_TARGET"; then
  log "adding target $TRANSLATION_TARGET to $channel"
  rustup target add --toolchain "$channel" "$TRANSLATION_TARGET"
  changed=1
fi

# 3. The Lean toolchain of the bundle's Lean library, copied to formal/lean-toolchain.
if ! cmp -s "$DEST/backends/lean/lean-toolchain" "$ROOT/formal/lean-toolchain"; then
  cp "$DEST/backends/lean/lean-toolchain" "$ROOT/formal/lean-toolchain"
  log "wrote formal/lean-toolchain"
  changed=1
fi
lean_toolchain="$(tr -d '[:space:]' < "$ROOT/formal/lean-toolchain")"
command -v elan >/dev/null 2>&1 || die "elan not found (install it from https://github.com/leanprover/elan)"
if ! elan toolchain list | awk -v t="$lean_toolchain" '$1 == t { f = 1 } END { exit !f }'; then
  log "installing Lean $lean_toolchain"
  elan toolchain install "$lean_toolchain"
  changed=1
fi

log "aeneas:  $aeneas_version"
log "charon:  $charon_version"
log "rust:    $channel"
log "lean:    $lean_toolchain"
if [[ "$changed" -eq 0 ]]; then
  log "nothing to do: everything already installed"
fi
