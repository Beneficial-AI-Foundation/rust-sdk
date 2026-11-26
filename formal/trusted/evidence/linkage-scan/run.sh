#!/usr/bin/env bash
# Negative controls for the shadow scan of scripts/check-original-linkage.sh (step 4).
# Each case cases/<id>.mine.lean is a block of the "unmodified-source" Funs.lean; the "committed"
# Funs.lean is the same block plus cases/<id>.extra.lean, a committed-only declaration that a free
# identifier of the block would resolve to. The scan must reject every case (exit 1): as name
# shadowing, or as a block it cannot read ("cannot be scanned", fail closed).
# limits/<id>.{mine,extra}.lean are forms this pre-check does not read, covered by the elaborated
# comparison (step 5) instead (name resolution through the
# type of a term); they are reported, and do not change the exit status.
# Usage: formal/trusted/evidence/linkage-scan/run.sh <new-or-empty scratch dir outside the repo>
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"; ROOT="$(cd "$HERE/../../../.." && pwd)"
[[ $# -eq 1 ]] || { echo "usage: $0 <scratch-dir>" >&2; exit 2; }
parent="$(cd "$(dirname "$1")" && pwd)" || { echo "parent of $1 must exist" >&2; exit 2; }
case "$parent/" in "$ROOT"/*) echo "refused: $1 is inside the repository" >&2; exit 2;; esac
if [[ -e "$1" ]]; then [[ -d "$1" && -z "$(ls -A "$1")" ]] || { echo "refused: $1 is not a new or empty directory" >&2; exit 2; }; fi
mkdir -p "$1"; W="$(cd "$1" && pwd)"
awk '/^python3 -I - "\$SCR\/out\/Rmcp"/{f=1;next} f&&/^PY$/{exit} f' "$ROOT/scripts/check-original-linkage.sh" > "$W/compare.py"
[[ -s "$W/compare.py" ]] || { echo "could not extract step 4 of check-original-linkage.sh" >&2; exit 1; }
hdr=$'-- header\nimport Aeneas\nopen Aeneas Std Result\nnamespace rmcp'
fail=0; n=0
build() {  # <case-dir> <mine-file> <extra-file>
  local c="$1"; mkdir -p "$c/mine" "$c/theirs"
  for f in Types.lean FunsExternal_Template.lean TypesExternal_Template.lean; do
    printf '%s\n\nend rmcp\n' "$hdr" > "$c/mine/$f"; cp "$c/mine/$f" "$c/theirs/$f"; done
  { printf '%s\n\n' "$hdr"; cat "$2"; printf '\nend rmcp\n'; } > "$c/mine/Funs.lean"
  { printf '%s\n\n' "$hdr"; cat "$2"; printf '\n'; cat "$3"; printf '\nend rmcp\n'; } > "$c/theirs/Funs.lean"
}
for m in "$HERE"/cases/*.mine.lean; do
  id="$(basename "$m" .mine.lean)"; c="$W/$id"; n=$((n+1))
  build "$c" "$m" "$HERE/cases/$id.extra.lean"
  if python3 -I "$W/compare.py" "$c/mine" "$c/theirs" > "$c/out.log" 2>&1; then
    echo "FAIL $id: accepted (shadowing missed)"; fail=1
  elif grep -q "name shadowing by patched code" "$c/out.log"; then echo "ok   $id: rejected"
  elif grep -q "error: cannot be scanned" "$c/out.log"; then echo "ok   $id: refused (cannot be scanned)"
  else echo "FAIL $id: rejected for another reason:"; tail -1 "$c/out.log"; fail=1; fi
done
echo "$n cases"
for m in "$HERE"/limits/*.mine.lean; do
  [[ -e "$m" ]] || continue
  id="$(basename "$m" .mine.lean)"; c="$W/limit-$id"
  build "$c" "$m" "$HERE/limits/$id.extra.lean"
  if python3 -I "$W/compare.py" "$c/mine" "$c/theirs" > "$c/out.log" 2>&1; then
    echo "limit $id: accepted (not read by the pre-check; covered by step 5)"
  else echo "limit $id: rejected ($(tail -1 "$c/out.log" | cut -c1-80))"; fi
done
exit $fail
