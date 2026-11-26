"""Compare the elaborated unmodified-source translation (E0) with the committed one (E1), both built
with their generated External templates: every non-auxiliary constant of Rmcp.Types/Rmcp.Funs of E0
must exist in E1 with the same module, kind, universe parameters, canonical type and canonical body;
every external of E0 with the same universe parameters and canonical type; and what Rmcp.Types and
Rmcp.Funs export besides constants may differ only as new declarations make it differ: instance
entries (only the SizeOf and @[discriminant] instances generated for a type only E1 has, checked by
class and argument), reducibility entries (only for new constants of the same module), and the entry
counts of the other environment extensions (only those listed in GROW_OK may grow)."""
import json, re, sys
def load(p):
    consts, insts, reds, exts, aux = {}, [], [], {}, {}
    for line in open(p, encoding="utf-8"):
        o = json.loads(line)
        if "c" in o: consts[o["c"]] = o
        elif "aux" in o and "red" not in o: aux[o["aux"]] = o["module"]
        elif "inst" in o: insts.append((o["module"], o["inst"], o["prio"], o["kind"], o["class"], o["arg"]))
        elif "red" in o and not o["aux"]:   # auxiliary constants (`match_N`, `_proof_N`, …) are
            reds.append((o["module"], o["red"], o["status"], o["owner"]))   # renumbered module-wide
        elif "ext" in o: exts[(o["module"], o["ext"])] = o["n"]
    return consts, insts, reds, exts, aux
(c0, i0, r0, x0, a0), (c1, i1, r1, x1, a1) = load(sys.argv[1]), load(sys.argv[2])
if not x0 or not x1 or not c0 or not c1:
    sys.exit("[linkage] error: a dump of the elaborated translation is empty or has no export section")
TR, EXT = {"Rmcp.Types", "Rmcp.Funs"}, {"Rmcp.TypesExternal", "Rmcp.FunsExternal"}
new_types = {n for n, o in c1.items() if o["module"] in TR and o["kind"] == "inductive" and n not in c0}
bad, n_tr, n_ext = [], 0, 0
for n, a in sorted(c0.items()):
    b = c1.get(n)
    if a["module"] in TR:
        n_tr += 1
        if b is None: bad.append(f"{n}: missing in the committed translation"); continue
        for k in ("module", "kind", "lparams", "type", "body"):
            if a[k] != b[k]: bad.append(f"{n}: {k} differs"); break
    elif a["module"] in EXT:
        n_ext += 1
        if b is None or b["module"] not in EXT: bad.append(f"external {n}: missing in the committed templates"); continue
        for k in ("lparams", "type"):
            if a[k] != b[k]: bad.append(f"external {n}: {k} differs"); break
# Extensions whose module entries grow with the committed-only declarations themselves (compiler
# data, declaration ranges, docstrings, namespaces, structure/projection/recursor data, Aeneas'
# trait/loop tables, simp/grind sets of the new declarations), measured on the real translations
# 2026-11-26. Instance and reducibility entries are compared by content below. Any other extension
# with more (or fewer) entries in env1 than in env0 is refused: notation, macros, syntax, `export`,
# default instances, unification hints, coercions and every extension not listed here.
GROW_OK = {   # per module (review a7-3): an extension may grow only where it grows on the real translations
    "Rmcp.Types": {
        "Lean.Compiler.LCNF.UnreachableBranches.functionSummariesExt", "Lean.Compiler.LCNF.baseExt",
        "Lean.Compiler.LCNF.impureSigExt", "Lean.Compiler.LCNF.monoExt", "Lean.Compiler.LCNF.monoTypeExt",
        "Lean.Compiler.implementedByAttr", "Lean.Compiler.inlineAttrs", "Lean.Elab.Term.elabAsElim",
        "Lean.IR.declMapExt", "Lean.Meta.Grind.grindExt", "Lean.Meta.Match.Extension.extension",
        "Lean.Meta.completionBlackListExt", "Lean.Meta.instanceExtension", "Lean.Meta.simpExtension",
        "Lean.auxRecExt", "Lean.declRangeExt", "Lean.docStringExt", "Lean.noConfusionExt",
        "Lean.projectionFnInfoExt", "Lean.protectedExt",
        "_private.Lean.AuxRecursor.0.Lean.sparseCasesOnExt",
        "_private.Lean.Compiler.LCNF.MonoTypes.0.Lean.Compiler.LCNF.trivialStructureInfoExt",
        "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.ctorLayoutExt",
        "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.impureTrivialStructureInfoExt",
        "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.impureTypeExt",
        "_private.Lean.ExtraModUses.0.Lean.extraModUses", "_private.Lean.Namespace.0.Lean.namespacesExt",
        "_private.Lean.OriginalConstKind.0.Lean.privateConstKindsExt",
        "_private.Lean.Structure.0.Lean.structureExt",
        "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt", "reducibilityCore",
        "rustTraitDeclsArray", "rustTypesArray"},
    "Rmcp.Funs": {
        "Aeneas.Std.globalSimpExt", "Lean.Compiler.LCNF.UnreachableBranches.functionSummariesExt",
        "Lean.Compiler.LCNF.baseExt", "Lean.Compiler.LCNF.impureSigExt", "Lean.Compiler.LCNF.monoExt",
        "Lean.Compiler.inlineAttrs", "Lean.IR.declMapExt", "Lean.Meta.Match.Extension.extension",
        "Lean.backwardDefeqAttr", "Lean.declRangeExt", "Lean.docStringExt", "Lean.noncomputableExt",
        "_private.Lean.ExtraModUses.0.Lean.extraModUses", "_private.Lean.Namespace.0.Lean.namespacesExt",
        "_private.Lean.OriginalConstKind.0.Lean.privateConstKindsExt",
        "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt", "reducibilityCore",
        "rustTraitImplsArray", "rust_loop", "rust_loop_body"},
}
for key in sorted(set(x0) | set(x1)):
    a, b = x0.get(key, 0), x1.get(key, 0)
    if a != b and (b < a or key[1] not in GROW_OK.get(key[0], set())):
        bad.append(f"{key[0]} exports {b} entries of {key[1]} where the unmodified source exports {a}")
# Instances (human decision 2026-11-26, review a6-1/a6-2): every instance entry of env0's
# translation modules is in env1 unchanged (name, priority, scoped/global, class, argument); an
# entry only env1 has must be a default-priority global instance that Lean or Aeneas generate for a
# type only env1 has: class SizeOf named `<T>._sizeOf_inst`, or class Aeneas.Std.Discriminant named
# `instDiscriminant…`, with T (the head of its first argument) a committed-only inductive.
from collections import Counter
e0, e1 = Counter(i0), Counter(i1)
gen, passed = 0, set()
for k in (e0 - e1): bad.append(f"instance entry {k[1]} of {k[0]} (priority {k[2]}, {k[3]}) is missing or changed")
for k, cnt in (e1 - e0).items():
    m, n, prio, kind, cls, arg = k
    ok = (prio == 1000 and kind == "global" and arg in new_types and m == "Rmcp.Types" and
          ((cls == "SizeOf" and n == arg + "._sizeOf_inst") or
           (cls == "Aeneas.Std.Discriminant" and n.startswith("instDiscriminant"))))
    if ok: gen += cnt; passed.add(n)
    else: bad.append(f"instance entry {n} (class {cls}, priority {prio}, {kind}) is exported only by the committed {m}")
# New names (review a7-2): Aeneas declares everything under `rmcp.`, plus the root
# `instDiscriminant…` instances of @[discriminant] types; any other constant only env1's translation
# modules declare (auxiliary ones included) could capture a name in downstream code.
names1 = {n: o["module"] for n, o in c1.items()} | a1
names0 = set(c0) | set(a0)
for n, m in sorted(names1.items()):
    base = re.sub(r"^_private\.Rmcp\.(Types|Funs)\.0\.", "", n)   # Lean's private-name prefix
    if m in TR and n not in names0 and not base.startswith("rmcp.") and \
            not (n.startswith("instDiscriminant") and n in passed):
        bad.append(f"{n}: a new name outside `rmcp.` declared by the committed {m}")
# Reducibility of non-auxiliary constants: env0's entries unchanged; a new entry only for a
# constant of that module that env0 lacks. (Auxiliary constants are compared by content where used.)
f0, f1 = Counter(r0), Counter(r1)
for k in (f0 - f1): bad.append(f"reducibility of {k[1]} ({k[2]}) is missing or changed")
for k in (f1 - f0):
    m, n, st, owner = k
    if owner != m or n in c0: bad.append(f"reducibility {st} of {n} set by the committed {m}")
print(f"[linkage] elaborated: {n_tr} constants and {n_ext} externals of the unmodified-source "
      f"translation compared with the committed translation; {gen} generated instances of "
      f"committed-only types")
for x in bad[:50]: print(f"[linkage] DIFFERS (elaborated): {x}")
if bad:
    sys.exit(f"[linkage] error: {len(bad)} elaborated difference(s): the committed translation does "
             "not elaborate the unmodified-source blocks as the unmodified source does, or exports more than "
             "its new declarations (plan Section 19)")
