# Repair the one known Aeneas template printing bug (a fn item used as FnOnce: the template
# prints `A → R → A → R` for `(A → R) → A → R`). Only axioms named `….call_once` of an
# `Insts.CoreOpsFunctionFnOnce…` impl whose printed type has exactly the shape `X → Y → X → Y` are
# rewritten. Why a wrong rewrite cannot make step 5 pass (review a6-3): the same rewrite is applied
# to both environments' templates, it maps distinct printed types to distinct types, and a rewrite
# that does not fit the translation's use of the external makes Rmcp.Funs fail to elaborate, which
# stops step 5.
import re, sys
p = sys.argv[1]
s = open(p, encoding="utf-8").read()
pat = re.compile(r"(axiom (\S+\.Insts\.CoreOpsFunctionFnOnce\S*\.call_once)\s*\n\s*:\s*\n)([^\n]+→[^\n]+→\s*\n[^\n]+)")
done = []
def fix(m):
    ty = " ".join(m.group(3).split())
    parts = [x.strip() for x in ty.split("→")]
    # X → Result Y → X → Result Y
    if len(parts) == 4 and parts[0] == parts[2] and parts[1] == parts[3]:
        done.append(m.group(2))
        return f"{m.group(1)}  ({parts[0]} → {parts[1]}) → {parts[2]} → {parts[3]}"
    return m.group(0)
s2, n = pat.subn(fix, s)
open(p, "w", encoding="utf-8").write(s2)
print(f"[linkage] template repair: {len(done)} of {n} candidate(s) rewritten", file=sys.stderr)
