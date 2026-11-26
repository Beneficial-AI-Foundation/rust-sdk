#!/usr/bin/env bash
# Differential tests of translation patch 05 (formal/trusted/patches/05-metadata-resolver.patch):
# the patched metadata_resolver.rs and AuthorizationManager::is_loopback_metadata_host against
# the original code of upstream 7caec76 (README.md in this directory). Not part of any build or
# CI job.
#
# Usage: run.sh [--full] <scratch-dir>
#   <scratch-dir>  a new or empty directory outside the repository (its parent must exist);
#                  receives llbc/work (the patched copy made by scripts/apply-patches.sh with
#                  RMCP_LLBC_DIR=<scratch-dir>/llbc), the cargo target, old_module.rs,
#                  toolchain.txt and test.log
#   --full         run the whole library test suite of the patched copy together with the
#                  differential modules, in one test process, instead of the 7 tests only
# Before anything is created: the scratch path is canonicalised (its parent with symlinks
# resolved) and refused if it is a symlink, `/`, $HOME or an ancestor of it, the repository, inside
# the repository or an ancestor of it, or an existing non-directory or non-empty directory; and
# old_body.rs and old_wrappers.rs are compared with the original code at 7caec76 (failing on any
# drift). Appends to the patched copy's metadata_resolver.rs (never to the repository): the
# module `old` (old_body.rs, the original file before its `mod tests`, adapted as below, then
# old_wrappers.rs), and the test modules diff_tests.rs and review_a1_tests.rs; then runs the
# tests. Writes only inside <scratch-dir>; deletes nothing.
set -euo pipefail
die() { echo "run.sh: $*" >&2; exit 2; }
full=0
if [ $# -eq 2 ] && [ "$1" = "--full" ]; then full=1; shift; fi
[ $# -eq 1 ] || die "usage: run.sh [--full] <scratch-dir>"
here=$(cd -P "$(dirname "$0")" && pwd -P)
repo=$(cd -P "$here/../../../../.." && pwd -P)
[ -f "$repo/scripts/apply-patches.sh" ] || die "repository root not found from $here"

# 1. The scratch path, checked before anything is created.
base=$(basename -- "$1")
case "$base" in ""|.|..|/) die "refusing scratch dir $1 (its last component must be a plain name)";; esac
parent=$(dirname -- "$1")
[ -d "$parent" ] || die "the parent of the scratch dir ($parent) does not exist"
out="$(cd -P "$parent" && pwd -P)"
out="${out%/}/$base"
[ ! -L "$out" ] || die "refusing scratch dir $out (a symlink)"
home_c=$(cd -P "$HOME" && pwd -P)
within() { [ "$2" = "/" ] || [ "$1" = "$2" ] || case "$1" in "$2"/*) true;; *) false;; esac; }
within "$out" "$repo" && die "refusing scratch dir $out (inside the repository $repo)"
within "$repo" "$out" && die "refusing scratch dir $out (contains the repository)"
within "$home_c" "$out" && die "refusing scratch dir $out (/, \$HOME or an ancestor)"
if [ -e "$out" ]; then
  [ -d "$out" ] || die "refusing scratch dir $out (exists and is not a directory)"
  [ -z "$(ls -A "$out")" ] || die "refusing scratch dir $out (exists and is not empty)"
fi

# 2. The recorded original code must equal 7caec76 (fails on drift of the two files).
pin=7caec762799bece6fba38e4298b8ca7db8bac12c
git -C "$repo" cat-file -e "$pin^{commit}" 2>/dev/null || die "commit $pin not in the repository"
orig_mr=$(git -C "$repo" show "$pin:crates/rmcp/src/transport/auth/metadata_resolver.rs") \
  || die "git show of metadata_resolver.rs at $pin failed"
[ "$(printf '%s\n' "$orig_mr" | sed -n 227p)" = "#[cfg(test)]" ] \
  || die "metadata_resolver.rs at $pin: line 227 is not the #[cfg(test)] of mod tests"
printf '%s\n' "$orig_mr" | head -226 | cmp -s - "$here/old_body.rs" \
  || die "old_body.rs differs from lines 1-226 of crates/rmcp/src/transport/auth/metadata_resolver.rs at $pin"
# old_wrappers.rs lines 4-13 are auth.rs lines 1401-1410 at the pin (is_loopback_metadata_host),
# de-indented by four spaces and renamed old_is_loopback_metadata_host, pub(super).
orig_auth=$(git -C "$repo" show "$pin:crates/rmcp/src/transport/auth.rs") \
  || die "git show of auth.rs at $pin failed"
want_wr=$(printf '%s\n' "$orig_auth" | sed -n '1401,1410p' | sed -E \
  -e 's/^    //' \
  -e '1s/^fn is_loopback_metadata_host\(/pub(super) fn old_is_loopback_metadata_host(/')
[ "$(printf '%s\n' "$want_wr" | head -1)" = "pub(super) fn old_is_loopback_metadata_host(host: Host<&str>) -> bool {" ] \
  || die "auth.rs at $pin: lines 1401-1410 are not is_loopback_metadata_host"
[ "$(sed -n '4,13p' "$here/old_wrappers.rs")" = "$want_wr" ] \
  || die "old_wrappers.rs lines 4-13 differ from auth.rs lines 1401-1410 at $pin"
[ "$(sed -n '14p' "$here/old_wrappers.rs")" = 'pub(super) fn old_normalize_host(host: &str) -> String { normalize_host(host) }' ] \
  && [ "$(wc -l < "$here/old_wrappers.rs" | tr -d ' ')" -eq 14 ] \
  || die "old_wrappers.rs: line 14 is not the old_normalize_host accessor, or extra lines"

# 3. The patched copy.
mkdir "$out" 2>/dev/null || [ -d "$out" ] || die "cannot create $out"
RMCP_LLBC_DIR="$out/llbc" "$repo/scripts/apply-patches.sh"
f="$out/llbc/work/crates/rmcp/src/transport/auth/metadata_resolver.rs"
grep -q '^pub(super) mod prim {' "$f" || { echo "run.sh: patch 05 not applied to $f" >&2; exit 1; }

# The original file as a child module `old`: inner doc comments `//!` become `//`; the import of
# AuthorizationManager goes one level up; the four fields of MetadataAddressResolver become
# pub(super) so the tests can compare them; with_lookup's guard calls the original
# is_loopback_metadata_host (old_wrappers.rs), so the old side runs no patched code.
old="$out/old_module.rs"
{
  printf '\n#[cfg(test)]\n#[allow(dead_code, unused_imports)]\nmod old {\n'
  sed -E \
    -e 's#^//!#//#' \
    -e 's#^use super::AuthorizationManager;$#use super::super::AuthorizationManager;#' \
    -e 's#^    (base_ip|unfiltered_hosts|base_classes|lookup): #    pub(super) \1: #' \
    -e 's#if AuthorizationManager::is_loopback_metadata_host\(Host::Domain\(domain\)\) =>#if old_is_loopback_metadata_host(Host::Domain(domain)) =>#' \
    "$here/old_body.rs"
  printf '\n'
  cat "$here/old_wrappers.rs"
  printf '}\n'
} > "$old"
[ "$(grep -c '^use super::super::AuthorizationManager;$' "$old")" -eq 1 ] \
  && [ "$(grep -cE '^    pub\(super\) (base_ip|unfiltered_hosts|base_classes|lookup): ' "$old")" -eq 4 ] \
  && [ "$(grep -c 'if old_is_loopback_metadata_host(Host::Domain(domain)) =>' "$old")" -eq 1 ] \
  || { echo "run.sh: old_body.rs did not adapt as expected" >&2; exit 1; }
{ cat "$old"; printf '\n'; cat "$here/diff_tests.rs"; printf '\n'; cat "$here/review_a1_tests.rs"; } >> "$f"

features=request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth,macros
{ cargo --version; rustc --version; } | tee "$out/toolchain.txt"
if [ "$full" -eq 1 ]; then
  args=()
else
  args=(metadata_resolver::diff_tests metadata_resolver::review_a1 --nocapture)
fi
(cd "$out/llbc/work" && cargo test -p rmcp --lib --features "$features" \
  --target-dir "$out/target" -- ${args[@]+"${args[@]}"}) 2>&1 | tee "$out/test.log"
# The 7 differential tests must all have run and passed (in both modes).
n=$(grep -cE '^test transport::auth::metadata_resolver::(diff_tests|review_a1)::[a-z0-9_]+ \.\.\. ok$' "$out/test.log" || true)
[ "$n" -eq 7 ] || { echo "run.sh: expected 7 passing differential tests, found $n" >&2; exit 1; }
if [ "$full" -eq 1 ]; then
  grep -qE '^test result: ok\. [0-9]+ passed; 0 failed' "$out/test.log" \
    || { echo "run.sh: the full library suite did not pass" >&2; exit 1; }
else
  grep -q '^test result: ok\. 7 passed; 0 failed' "$out/test.log" \
    || { echo "run.sh: expected 7 passed tests" >&2; exit 1; }
fi
