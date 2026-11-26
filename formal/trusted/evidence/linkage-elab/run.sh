#!/usr/bin/env bash
# Negative controls for step 5 of scripts/check-original-linkage.sh (the elaborated comparison).
# Each cases/<id>.txt injects committed-only Lean text into a copy of the committed translation
# formal/translation/Rmcp/Funs.lean (before the line ANCHOR, or after `namespace rmcp` for TOP),
# builds it as env1 the way step 5 does, and compares it with env0 of an earlier linkage run.
# EXPECT: pass, or the kinds compare_env.py must report joined by +, in this order: differs (a
# constant or external), instance, exports (an extension's entry count), reducibility.
# ANCHOR: a unique line of Funs.lean to insert before, TOP (after `namespace rmcp`) or END (before
# the final `end rmcp`).
# Usage: run.sh <scratch-dir of a completed check-original-linkage.sh run> <new empty dir outside repo>
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"; ROOT="$(cd "$HERE/../../../.." && pwd)"
LIN="$ROOT/scripts/linkage"
[[ $# -eq 2 ]] || { echo "usage: $0 <linkage-scratch-dir> <new empty dir>" >&2; exit 2; }
DUMP0="$1/env0/dump.jsonl"; [[ -s "$DUMP0" ]] || { echo "no $DUMP0: run scripts/check-original-linkage.sh $1 first" >&2; exit 2; }
parent="$(cd "$(dirname "$2")" && pwd)" || { echo "parent of $2 must exist" >&2; exit 2; }
case "$parent/" in "$ROOT"/*) echo "refused: $2 is inside the repository" >&2; exit 2;; esac
if [[ -e "$2" ]]; then [[ -d "$2" && -z "$(ls -A "$2")" ]] || { echo "refused: $2 is not a new or empty directory" >&2; exit 2; }; fi
mkdir -p "$2"; W="$(cd "$2" && pwd)"
T="$ROOT/formal/translation/Rmcp"
fail=0; n=0
for c in "$HERE"/cases/*.txt; do
  id="$(basename "$c" .txt)"; n=$((n+1)); E="$W/$id"
  expect="$(sed -n 's/^EXPECT: //p;1q' "$c")"
  python3 -I "$LIN/make_env.py" "$ROOT" "$E" "$T/Types.lean" "$T/Funs.lean" \
    "$T/TypesExternal_Template.lean" "$T/FunsExternal_Template.lean"
  python3 -I "$LIN/repair_template.py" "$E/src/Rmcp/FunsExternal.lean" 2>/dev/null
  python3 -I - "$c" "$E/src/Rmcp/Funs.lean" <<'PY'
import sys
case, funs = sys.argv[1:]
lines = open(case, encoding="utf-8").read().split("\n")
anchor = lines[1][len("ANCHOR: "):]
text = "\n".join(lines[2:]).rstrip("\n")
s = open(funs, encoding="utf-8").read()
if anchor == "END":
    i = s.rindex("end rmcp"); s = s[:i] + text + "\n\n" + s[i:]
elif anchor == "TOP":
    i = s.index("namespace rmcp\n") + len("namespace rmcp\n"); s = s[:i] + "\n" + text + "\n\n" + s[i:]
else:
    assert s.count(anchor) == 1, f"anchor not unique: {anchor!r}"
    i = s.index(anchor); s = s[:i] + text + "\n\n" + s[i:]
open(funs, "w", encoding="utf-8").write(s)
PY
  if ! (cd "$E" && lake build Rmcp > build.log 2>&1 && lake env lean --run "$LIN/Dump.lean" dump.jsonl); then
    echo "FAIL $id: the injected translation does not build (see $E/build.log)"; fail=1; continue; fi
  out="$(python3 -I "$LIN/compare_env.py" "$DUMP0" "$E/dump.jsonl" 2>&1)" && rc=0 || rc=$?
  got=pass
  if [[ $rc -ne 0 ]]; then
    kinds=()
    # classify by the exact message prefixes of compare_env.py (review a7-5)
    lines="$(sed -n 's/^\[linkage\] DIFFERS (elaborated): //p' <<<"$out")"
    grep -q '^instance entry ' <<<"$lines" && kinds+=(instance)
    grep -qE '^Rmcp\.[A-Za-z]+ exports [0-9]+ entries of ' <<<"$lines" && kinds+=(exports)
    grep -q '^reducibility ' <<<"$lines" && kinds+=(reducibility)
    grep -vE '^(instance entry |Rmcp\.[A-Za-z]+ exports [0-9]+ entries of |reducibility )' <<<"$lines" | grep -q . \
      && kinds=(differs ${kinds[@]+"${kinds[@]}"})
    got="$(IFS=+; k="${kinds[*]+"${kinds[*]}"}"; echo "${k:-other}")"
  fi
  if [[ "$got" == "$expect" ]]; then echo "ok   $id: $got"
  else echo "FAIL $id: expected $expect, got $got"; echo "$out" | tail -4; fail=1; fi
done
echo "$n cases"; exit $fail
