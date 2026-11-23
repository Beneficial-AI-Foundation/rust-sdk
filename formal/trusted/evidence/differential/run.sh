#!/usr/bin/env bash
# Differential check of the Base64url and UTF-8 external models against the Rust crates
# (formal/trusted/evidence/README.md, "Differential check"). Not part of any build or CI job.
#
# Usage: run.sh <formal-dir> <scratch-dir>
#   <formal-dir>   the formal/ directory, after `lake build RmcpExternal`
#   <scratch-dir>  a new or empty directory for generated inputs, outputs, a copy of rdiff/ and
#                  the cargo target
# Compares, line by line, the Lean models (Diff.lean.in, run with `lake env lean --run`) with
# base64 0.23.1 `URL_SAFE_NO_PAD` and std `String::from_utf8`/`as_bytes` (rdiff/), on the
# inputs gen.py writes (seeds random.Random(20261123) and random.Random(20261124)) plus
# exhaustive ranges. rdiff/ is copied into <scratch-dir> and built there with `--locked` from
# the committed rdiff/Cargo.lock, so the source tree is never written; the cargo and rustc
# versions used are printed and saved in <scratch-dir>/toolchain.txt. Exits 1 on the first
# mismatch. Writes only inside <scratch-dir>; deletes nothing.
set -euo pipefail
[ $# -eq 2 ] || { echo "usage: run.sh <formal-dir> <scratch-dir>" >&2; exit 2; }
here=$(cd "$(dirname "$0")" && pwd)
formal=$(cd "$1" && pwd)
mkdir -p "$2"
out=$(cd "$2" && pwd)
case "$out" in /|"$HOME"|"$formal"|"$formal"/*|"$here"|"$here"/*)
  echo "run.sh: refusing scratch dir $out" >&2; exit 2;; esac
[ -f "$here/rdiff/Cargo.lock" ] || { echo "run.sh: missing $here/rdiff/Cargo.lock" >&2; exit 2; }
mkdir -p "$out/data" "$out/out" "$out/rdiff/src"
cp "$here/rdiff/Cargo.toml" "$here/rdiff/Cargo.lock" "$out/rdiff/"
cp "$here/rdiff/src/main.rs" "$out/rdiff/src/"
{ (cd "$out/rdiff" && cargo --version && rustc --version); python3 --version; } \
  | tee "$out/toolchain.txt"
python3 -I "$here/gen.py" "$out/data"
(cd "$out/rdiff" && cargo build --release --quiet --locked --target-dir "$out/target")
rust="$out/target/release/rdiff"
lean() { (cd "$formal" && lake env lean --run "$here/Diff.lean.in" "$@"); }
total=0
check() { # <name> <mode> [file]
  local name=$1; shift
  "$rust" "$@" > "$out/out/rust_$name"
  lean "$@" > "$out/out/lean_$name"
  if ! cmp -s "$out/out/rust_$name" "$out/out/lean_$name"; then
    echo "MISMATCH in $name:"; cmp "$out/out/rust_$name" "$out/out/lean_$name" || true; exit 1
  fi
  local n; n=$(wc -l < "$out/out/rust_$name" | tr -d ' ')
  total=$((total + n)); echo "$name: $n comparisons, 0 mismatches"
}
check enc_prefix enc_prefix "$out/data/enc.txt"
check dec dec "$out/data/dec.txt"
check utf8 utf8 "$out/data/utf8.txt"
check cps cps "$out/data/cps.txt"
check enc_exh enc_exh
check utf8_exh utf8_exh
echo "total: $total comparisons, 0 mismatches"
