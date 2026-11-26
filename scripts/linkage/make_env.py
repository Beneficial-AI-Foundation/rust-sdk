"""Create a Lake workspace <dir> that builds four translation modules Rmcp.{TypesExternal,Types,
FunsExternal,Funs} against the Aeneas version of formal/lakefile.toml, reusing the packages already
fetched and built in formal/.lake/packages (packagesDir), so nothing but the four modules is built.
Usage: make_env.py <repo-root> <dir> <Types.lean> <Funs.lean> <TypesExternal> <FunsExternal>"""
import json, os, shutil, sys, tomllib
root, d, types, funs, text, fext = sys.argv[1:]
formal = os.path.join(root, "formal")
pkgs = os.path.join(formal, ".lake", "packages")
# Fail fast unless the packages are built (review a6-4): otherwise Lake would build them inside
# formal/.lake/packages, outside the scratch directory.
for olean in (("aeneas", "backends", "lean", ".lake", "build", "lib", "lean", "Aeneas.olean"),
              ("mathlib", ".lake", "build", "lib", "lean", "Mathlib.olean")):
    if not os.path.isfile(os.path.join(pkgs, *olean)):
        sys.exit(f"[linkage] error: formal/.lake/packages/{'/'.join(olean)} is missing: run "
                 "`lake exe cache get && lake build Aeneas` (or `lake build`) in formal first")
cfg = tomllib.load(open(os.path.join(formal, "lakefile.toml"), "rb"))
req = [r for r in cfg["require"] if r["name"] == "aeneas"]
if len(req) != 1:
    sys.exit("[linkage] error: formal/lakefile.toml must require aeneas exactly once")
r = req[0]
os.makedirs(os.path.join(d, "src", "Rmcp"))
shutil.copy(os.path.join(formal, "lean-toolchain"), d)
m = json.load(open(os.path.join(formal, "lake-manifest.json")))
m["packagesDir"], m["name"] = pkgs, "rmcp_linkage_env"
json.dump(m, open(os.path.join(d, "lake-manifest.json"), "w"), indent=1)
open(os.path.join(d, "lakefile.toml"), "w").write(
    f'name = "rmcp_linkage_env"\npackagesDir = {json.dumps(pkgs)}\n'
    f'[[require]]\nname = "aeneas"\ngit = {json.dumps(r["git"])}\nrev = {json.dumps(r["rev"])}\n'
    f'subDir = {json.dumps(r.get("subDir", "."))}\n'
    '[[lean_lib]]\nname = "Rmcp"\nsrcDir = "src"\n'
    'roots = ["Rmcp.TypesExternal", "Rmcp.Types", "Rmcp.FunsExternal", "Rmcp.Funs"]\n')
for src, name in ((types, "Types"), (funs, "Funs"), (text, "TypesExternal"), (fext, "FunsExternal")):
    shutil.copy(src, os.path.join(d, "src", "Rmcp", name + ".lean"))
