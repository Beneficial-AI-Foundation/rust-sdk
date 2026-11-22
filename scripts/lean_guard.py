#!/usr/bin/env python3
"""Checks of the Lean project in formal/, called by scripts/lean-guard.sh (run with python3 -I).

  lean_guard.py fresh FORMAL        CI, first step: no FORMAL/.lake, nothing tracked by git
                                    under a .lake directory (see check_fresh).
  lean_guard.py lakefile FORMAL     formal/lean-toolchain is LEAN_TOOLCHAIN; formal/lakefile.toml
                                    has exactly the structure of plan Section 5 (see
                                    check_lakefile); no formal/lakefile.lean;
                                    formal/lake-manifest.json pins the recorded commits
                                    (see check_manifest).
  lean_guard.py sources FORMAL      banned words and constructs in the Lean sources, tracked or
                                    nested .lake paths, case variants of .lean (see check_sources).
  lean_guard.py axiom-lock LOCK GOT the trusted axioms written by lean-axiom-audit.lean (GOT)
                                    are exactly those of LOCK, with the same statement hashes
                                    (see check_axiom_lock).
  lean_guard.py build-log FILE      every `warning:`/`error:` line of the `lake build` log is
                                    one of the four recorded Aeneas-library lines.
  lean_guard.py archive PKG ARCHIVE PKG/.lake/build and the Lake release ARCHIVE hold the same
                                    regular files with the same bytes, *.hash and *.trace
                                    excepted (see check_archive).
  lean_guard.py roots FORMAL        prints the audit arguments for lean-axiom-audit.lean:
                                    the trusted modules (roots of RmcpExternal, comma-separated)
                                    on line 1, the roots of the default-target libraries on line 2.
  lean_guard.py leanpath FORMAL     prints LEAN_PATH for the audit: the package library
                                    directories of the manifest, then the project's.
  lean_guard.py buildtree FORMAL    formal/.lake/build/lib/lean holds only modules named Rmcp,
                                    Defs, Proofs, Specs or below them, and no symlink.
  lean_guard.py unpack TAR FORMAL   extracts the CI build artifact into FORMAL/.lake (only
                                    build/ and build.log; see unpack_build).

Exit status: 0 pass, 1 check failed, 2 usage or internal error.
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import tarfile

if sys.version_info < (3, 11):
    sys.exit("lean_guard.py: python3 >= 3.11 is needed (tomllib)")
import tomllib  # noqa: E402


def fail(msgs):
    for m in msgs:
        print(f"[lean-guard] {m}", file=sys.stderr)
    sys.exit(1)


# ---------------------------------------------------------------------------------------
# lakefile

# The five libraries of plan Section 5: srcDir and roots are fixed; leanOptions must be
# exactly { warningAsError = true }; no other key (no moreLeanArgs, weakLeanArgs, globs,
# extraDepTargets, precompileModules, ...).
LIBS = {
    "Rmcp": ("translation", ["Rmcp.Types", "Rmcp.Funs"]),
    "RmcpExternal": ("trusted", ["Rmcp.TypesExternal", "Rmcp.FunsExternal"]),
    "Defs": ("specs", ["Defs"]),
    "Proofs": ("proofs", ["Proofs"]),
    "Specs": ("specs", ["Specs"]),
}
LIB_KEYS = {"name", "srcDir", "roots", "leanOptions"}
PACKAGE_KEYS = {"name", "defaultTargets", "require", "lean_lib"}
REQUIRE_KEYS = {"name", "git", "rev", "subDir"}
REQUIRED_DEFAULTS = {"Defs", "Proofs", "Specs"}


# formal/lake-manifest.json: the commit of every package Lake fetches. The Aeneas entry must
# match the lakefile (url = git, inputRev = rev) and the commit of the pinned tag
# (nightly-2026.08.20-5d08da4, docs/WORKFLOW_AND_PR_GUIDE.md "Pinned toolchain"); the other
# packages (Mathlib and its dependencies, inherited from the Aeneas package) must have the
# commits recorded at S03. Changing the Aeneas rev means updating this table in the same PR.
AENEAS_COMMIT = "5d08da45a405913bbee6fd544e01debf8154ac9d"
# formal/lean-toolchain must be exactly this line (the Lean toolchain of the pinned Aeneas
# rev, backends/lean/lean-toolchain of the bundle, copied by scripts/aeneas-install.sh).
# elan runs whatever toolchain that file names, so it is checked before any `lean`/`lake`
# runs (CI runs `sources` before installing elan). Updated in the same PR as the Aeneas rev.
LEAN_TOOLCHAIN = "leanprover/lean4:v4.31.0"
MANIFEST_PACKAGES = {
    "aeneas": ("https://github.com/AeneasVerif/aeneas", AENEAS_COMMIT),
    "mathlib": ("https://github.com/leanprover-community/mathlib4.git",
                "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"),
    "plausible": ("https://github.com/leanprover-community/plausible",
                  "63045536fe95024e6c18fc7b48e03f506701c5bc"),
    "LeanSearchClient": ("https://github.com/leanprover-community/LeanSearchClient",
                         "c5d5b8fe6e5158def25cd28eb94e4141ad97c843"),
    "importGraph": ("https://github.com/leanprover-community/import-graph",
                    "5c7542ed018c78194f1e2b903eaf6a792b74c03d"),
    "proofwidgets": ("https://github.com/leanprover-community/ProofWidgets4",
                     "24b0d9dc081c5423f8eec7e866c441e5184f29d9"),
    "aesop": ("https://github.com/leanprover-community/aesop",
              "e3cb2f741431ce31bf73549fb52316a57368b06f"),
    "Qq": ("https://github.com/leanprover-community/quote4",
           "f46324995fca5f0483b742e4eb4daec7f4ee50d2"),
    "batteries": ("https://github.com/leanprover-community/batteries",
                  "fa08db58b30eb033edcdab331bba000827f9f785"),
    "Cli": ("https://github.com/leanprover/lean4-cli",
            "92564e5770e4d09f2d86dfbf8ada1e9c715b384c"),
}


def check_manifest(formal, cfg):
    """Errors for formal/lake-manifest.json against the lakefile and MANIFEST_PACKAGES."""
    errs = []
    with open(os.path.join(formal, "lake-manifest.json"), encoding="utf-8") as f:
        man = json.load(f)
    if man.get("name") != "rmcp_formal" or man.get("packagesDir") != ".lake/packages":
        errs.append("lake-manifest.json: name must be rmcp_formal and packagesDir .lake/packages")
    pkgs = man.get("packages")
    if not isinstance(pkgs, list) or not all(isinstance(e, dict) for e in pkgs):
        return errs + ["lake-manifest.json: packages is not a list of objects"]
    got = {e.get("name"): e for e in pkgs}
    if len(got) != len(pkgs) or set(got) != set(MANIFEST_PACKAGES):
        errs.append(f"lake-manifest.json: packages {sorted(map(str, got))}, expected exactly "
                    f"{sorted(MANIFEST_PACKAGES)}")
    for name, (url, rev) in MANIFEST_PACKAGES.items():
        e = got.get(name)
        if e is None:
            continue
        if e.get("type") != "git" or e.get("url") != url or e.get("rev") != rev:
            errs.append(f"lake-manifest.json: {name}: type {e.get('type')!r}, url {e.get('url')!r}, "
                        f"rev {e.get('rev')!r}; expected git, {url}, {rev}")
    req = (cfg.get("require") or [{}])[0]
    a = got.get("aeneas", {})
    if isinstance(req, dict) and (a.get("url"), a.get("inputRev"), a.get("subDir")) != (
            req.get("git"), req.get("rev"), req.get("subDir")):
        errs.append(f"lake-manifest.json: aeneas url/inputRev/subDir {a.get('url')!r}/"
                    f"{a.get('inputRev')!r}/{a.get('subDir')!r} differ from the lakefile "
                    f"{req.get('git')!r}/{req.get('rev')!r}/{req.get('subDir')!r}")
    return errs


def load_lakefile(formal):
    errs = []
    if os.path.lexists(os.path.join(formal, "lakefile.lean")):
        errs.append("formal/lakefile.lean exists (Lake would use it instead of lakefile.toml)")
    with open(os.path.join(formal, "lakefile.toml"), "rb") as f:
        cfg = tomllib.load(f)
    return cfg, errs


def check_toolchain(formal):
    """Errors for formal/lean-toolchain: its content, stripped, must be LEAN_TOOLCHAIN."""
    path = os.path.join(formal, "lean-toolchain")
    if os.path.islink(path) or not os.path.isfile(path):
        return [f"{path}: missing, or not a regular file"]
    with open(path, encoding="utf-8", errors="replace") as f:
        got = f.read().strip()
    if got != LEAN_TOOLCHAIN:
        return [f"lean-toolchain: {got!r}, expected exactly {LEAN_TOOLCHAIN!r} (lean_guard.py, LEAN_TOOLCHAIN)"]
    return []


def check_lakefile(formal):
    cfg, errs = load_lakefile(formal)
    errs += check_toolchain(formal)
    extra = set(cfg) - PACKAGE_KEYS
    if extra:
        errs.append(f"lakefile.toml: package-level key(s) not allowed: {sorted(extra)}")
    if cfg.get("name") != "rmcp_formal":
        errs.append(f"lakefile.toml: package name {cfg.get('name')!r}, expected 'rmcp_formal'")
    reqs = cfg.get("require", [])
    if not (isinstance(reqs, list) and len(reqs) == 1 and isinstance(reqs[0], dict)):
        errs.append("lakefile.toml: expected exactly one [[require]] (aeneas)")
    else:
        r = reqs[0]
        if set(r) - REQUIRE_KEYS:
            errs.append(f"lakefile.toml: [[require]] key(s) not allowed: {sorted(set(r) - REQUIRE_KEYS)}")
        if (r.get("name"), r.get("git"), r.get("subDir")) != (
                "aeneas", "https://github.com/AeneasVerif/aeneas", "backends/lean"):
            errs.append("lakefile.toml: [[require]] must be aeneas from "
                        "https://github.com/AeneasVerif/aeneas, subDir backends/lean")
        if not isinstance(r.get("rev"), str) or not r.get("rev"):
            errs.append("lakefile.toml: [[require]] aeneas has no rev")
    libs = cfg.get("lean_lib", [])
    if not isinstance(libs, list):
        errs.append("lakefile.toml: lean_lib is not an array of tables")
        libs = []
    names = [lib.get("name") for lib in libs if isinstance(lib, dict)]
    if sorted(map(str, names)) != sorted(LIBS) or len(names) != len(libs):
        errs.append(f"lakefile.toml: libraries {names}, expected exactly {sorted(LIBS)}")
    for lib in libs:
        if not isinstance(lib, dict):
            continue
        n = lib.get("name")
        if set(lib) != LIB_KEYS:
            errs.append(f"lakefile.toml: library {n}: keys {sorted(lib)}, expected exactly {sorted(LIB_KEYS)}")
        if lib.get("leanOptions") != {"warningAsError": True}:
            errs.append(f"lakefile.toml: library {n}: leanOptions {lib.get('leanOptions')!r}, "
                        "expected exactly { warningAsError = true }")
        if n in LIBS:
            src, roots = LIBS[n]
            if lib.get("srcDir") != src:
                errs.append(f"lakefile.toml: library {n}: srcDir {lib.get('srcDir')!r}, expected {src!r}")
            if lib.get("roots") != roots:
                errs.append(f"lakefile.toml: library {n}: roots {lib.get('roots')!r}, expected {roots}")
    dt = cfg.get("defaultTargets")
    if not (isinstance(dt, list) and all(isinstance(t, str) for t in dt)
            and set(dt) <= set(LIBS) and REQUIRED_DEFAULTS <= set(dt)):
        errs.append(f"lakefile.toml: defaultTargets {dt!r} must be library names including "
                    f"{sorted(REQUIRED_DEFAULTS)}")
    errs += check_manifest(formal, cfg)
    if errs:
        fail(errs + ["lakefile check failed"])
    print(f"[lean-guard] lean-toolchain: {LEAN_TOOLCHAIN}")
    print(f"[lean-guard] lakefile: the five libraries of plan Section 5, each with exactly "
          f"leanOptions = {{ warningAsError = true }}; defaultTargets {dt}")
    print(f"[lean-guard] lake-manifest.json: {len(MANIFEST_PACKAGES)} packages at the recorded "
          f"commits (aeneas {AENEAS_COMMIT[:8]}, matching the lakefile)")


def audit_roots(formal):
    cfg, errs = load_lakefile(formal)
    if errs:
        fail(errs)
    libs = {lib["name"]: lib for lib in cfg.get("lean_lib", [])}
    trusted = libs.get("RmcpExternal", {}).get("roots", [])
    roots = [r for t in cfg.get("defaultTargets", []) for r in libs[t]["roots"]]
    print(",".join(trusted) if trusted else "-")
    print(" ".join(roots))


def lean_path(formal):
    """Prints the library directories of the packages in formal/lake-manifest.json (in
    manifest order), then formal/.lake/build/lib/lean, ':'-separated, for LEAN_PATH."""
    with open(os.path.join(formal, "lake-manifest.json"), encoding="utf-8") as f:
        man = json.load(f)
    dirs = []
    for e in man["packages"]:
        name, sub = e["name"], e.get("subDir") or ""
        if not re.fullmatch(r"[A-Za-z0-9_-]+", name) or ".." in sub.split("/"):
            fail([f"lake-manifest.json: unexpected package name or subDir {name!r} {sub!r}"])
        dirs.append(os.path.join(formal, ".lake", "packages", name, sub, ".lake", "build", "lib", "lean"))
    dirs.append(os.path.join(formal, ".lake", "build", "lib", "lean"))
    print(":".join(os.path.normpath(d) for d in dirs))


# Module roots of this project; formal/.lake/build/lib/lean may hold nothing else (no
# Init, Lean, Lake, Mathlib, ... module that could stand in for a toolchain or package module).
PROJECT_ROOTS = ("Rmcp", "Defs", "Proofs", "Specs")


def check_build_tree(formal):
    lib = os.path.join(formal, ".lake", "build", "lib", "lean")
    if not os.path.isdir(lib) or os.path.islink(lib):
        fail([f"{lib} is missing or not a directory; run lake build first"])
    errs = []
    for e in sorted(os.listdir(lib)):
        root = e.split(".", 1)[0]
        path = os.path.join(lib, e)
        if root not in PROJECT_ROOTS or (os.path.isdir(path) and e != root):
            errs.append(f"{path}: not a module of this project ({'/'.join(PROJECT_ROOTS)})")
    for dirpath, dirnames, filenames in os.walk(lib):
        for n in dirnames + filenames:
            if os.path.islink(os.path.join(dirpath, n)):
                errs.append(f"{os.path.join(dirpath, n)}: symlink in the build output")
    if errs:
        fail(errs + ["unexpected entries in formal/.lake/build/lib/lean"])


# ---------------------------------------------------------------------------------------
# sources

ID = r"[A-Za-z0-9_'!?]"


def word(w):
    return re.compile(rf"(?<!{ID}){re.escape(w)}(?!{ID})")


# Banned in every hand-written and generated Lean file (comments and docstrings included).
WORDS_ALL = ["warningAsError", "sorry", "sorryAx", "admit", "native_decide", "bv_decide",
             "skipKernelTC", "proofAsSorry", "implemented_by", "extern", "unsafe",
             "ofReduceBool", "ofReduceNat", "trustCompiler"]
RULES_ALL = [(w, word(w)) for w in WORDS_ALL] + [
    # `decide +native`, `-native`, `(native := true)`, `{ native := true }`: the `native`
    # option of decide (kernel reduction replaced by compiled code, axiom Lean.ofReduceBool).
    ("native option (+native/-native)", re.compile(rf"(?:(?<=\s)|(?<=[(\[{{,])|^)[+-]native(?!{ID})", re.M)),
    ("native option (native :=)", re.compile(rf"(?<!{ID})(?<!\.)native\s*:=")),
]
# Hand-written only: generated files carry `set_option linter.* false` (Aeneas emits it).
RULE_LINTER = ("set_option linter.<name> false", re.compile(r"set_option\s+linter\.\S+\s+false"))
# Every hand-written file (trusted/ included) and the generated files: what runs code at
# elaboration time (during `lake build`) or changes the environment or options from a
# metaprogram. Such code could add declarations without a kernel check (caught by the replay
# in `axioms`), but also rewrite sources or build outputs while the build runs, which no later
# check of the build output can detect (formal/README.md, "What CI checks"). None of it is
# needed in specs, definitions, proofs or externals.
#
# META_WORDS was derived from the pinned toolchain and packages (formal/docs/evidence/S03.md,
# fix round 5, W1): every syntax kind whose registered elaborator or macro reaches, through
# constant bodies, `implemented_by` and `_unsafe_rec`, an evaluation primitive
# (Environment.evalConst/evalConstCheck, Meta.evalExpr(')/Term.evalTerm, elabEvalCoreUnsafe,
# IO.Process.spawn/output/run, loadDynlib), or whose macro builds syntax of such a kind, over
# all 8929 built modules of Lean, Lake, Mathlib, Aeneas and the other manifest packages; then
# the keyword of each kind (`#` commands are covered by HASH_CMD). Kinds that only evaluate
# declarations registered through an attribute are covered by ATTR_ALLOWED. Not banned
# (accepted residual, human decision 2026-11-22): tactics whose configuration or rule clauses
# are compiled and run (linarith/nlinarith, aesop and its wrappers, saturate/forward, Aeneas
# step/progress); `discharger` and `preprocessors` (the code-valued linarith fields) are banned.
# Matching is on whole tokens, as Lean tokenizes: a word is hit unless preceded or followed by
# an identifier character (letters, digits, `_`, `'`, `!`, `?`), so `by_elab` must be listed
# itself and `my_elaborate`, `elab_as_elim` or `List.drop` are not hit by `elab`.
META_WORDS = [
    # core: commands, terms and tactics that evaluate code
    "run_cmd", "run_tac", "run_elab", "run_meta", "by_elab", "include_str", "test_extern",
    "register_error_explanation", "show_panel_widgets", "with_panel_widgets", "bv_check",
    "bv_decide?", "autoParam",
    # core: declaring syntax, elaborators, macros, initialisers, options, simprocs
    "elab", "elab_rules", "initialize", "builtin_initialize", "macro", "macro_rules", "syntax",
    "simproc", "dsimproc", "simproc_decl", "builtin_simproc", "register_option",
    "register_simp_attr", "declare_syntax_cat", "declare_simp_like_tactic",
    # Mathlib, Batteries, Qq, Plausible, ProofWidgets, Aeneas
    "eval%", "trace", "success_if_fail_with_msg", "pi_lower_bound", "pi_upper_bound",
    "lrat_proof", "from_lrat", "run_conv", "run_tacq", "by_elabq", "plausible", "bv_tac",
    "initialize_simps_projections", "initialize_simps_projections?", "discharger",
    "preprocessors",
    # environment and option changes from metaprograms
    "addDecl", "addAndCompile", "modifyEnv", "setEnv", "withOptions",
    # the monads and types metaprograms are written in, and the namespace Lean.Elab
    # (also as `Elab` after `open Lean`)
    "IO", "EIO", "BaseIO", "CoreM", "MetaM", "TermElabM", "TacticM", "CommandElabM", "MacroM",
    "SimpM", "DelabM", "CommandElab", "TermElab", "Elab",
]


def meta_word(w):
    # `trace` is the Mathlib tactic; `set_option trace.<class>` stays allowed.
    if w == "trace":
        return re.compile(rf"(?<!{ID})(?<!\.)trace(?!{ID})(?!\.)")
    if w.endswith("%"):
        return re.compile(rf"(?<!{ID}){re.escape(w)}")
    return word(w)


RULES_META = [(w, meta_word(w)) for w in META_WORDS] + [
    ("Lean.Elab", re.compile(rf"(?<!{ID})Lean\.Elab(?!{ID})")),
    # Options under `debug.` (debug.skipKernelTC, debug.proofAsSorry, ...).
    ("debug.<option>", re.compile(rf"(?<!{ID})debug\.")),
]

# `#` commands: every one except these is banned. `#eval`, `#guard`, `#assert` (Aeneas),
# `#register_spec_info` (Aeneas), `#test`/`#sample` (Plausible), `#exit`, `#leansearch`, ...
# run code or have side effects; none is needed outside specs/Drafts/. `#guard_msgs` is
# further restricted by GUARD/GUARD_OK; `#check` and `#print` only elaborate and print.
HASH_CMD = re.compile(r"(?<![A-Za-z0-9_'!?.)\]}])#[A-Za-z_][A-Za-z0-9_'!?]*")
HASH_ALLOWED = {"#check", "#print", "#guard_msgs"}

# Attributes: every one except these is banned (in `@[...]` and `attribute [...]`, after an
# optional `local`/`scoped` or `-`). An attribute can hand its declaration to code that the
# build later runs (KeyedDecls attributes such as command_elab/term_elab/tactic/macro, init,
# simproc, norm_num, positivity, aesop rule builders, linters, delaborators, try?
# suggestion generators, doc roles, ...), so the list is an allowlist of attributes that only
# tag a theorem or definition for an existing procedure, or set reducibility, compiler or
# documentation flags; none evaluates the declaration it is put on. The first group is what
# Aeneas emits in the generated translation (pilot run 3); the rest is ordinary proof use.
# Extending it is a reviewed change of this file.
ATTR_ALLOWED = {
    # Aeneas, generated code
    "reducible", "irreducible", "global_simps", "discriminant", "rust_fun", "rust_type",
    "rust_trait", "rust_trait_impl", "rust_loop", "rust_loop_body", "rust_const",
    "trait_default",
    # Aeneas, proofs (lemma tags read by step/progress, scalar_tac, simp_lists, simp_scalar,
    # bvify, agrind)
    "step", "step_pure", "step_pure_def", "step_simps", "progress", "progress_pure",
    "progress_pure_def", "progress_simps", "scalar_tac", "scalar_tac_simps", "scalar_tac_nonlin",
    "simp_lists", "simp_lists_simps", "simp_scalar", "bvify", "bvify_simps", "agrind",
    # Lean core and Mathlib: simp sets and lemma tags, instances, reducibility, compiler hints
    "simp", "instance", "semireducible", "inline", "noinline", "specialize", "ext", "simps",
    "norm_cast", "push_cast", "grind", "congr", "refl", "symm", "trans", "gcongr", "fun_prop",
    "match_pattern", "elab_as_elim", "induction_eliminator", "cases_eliminator",
    "inherit_doc", "deprecated", "nolint", "pp_nodot", "expose", "wf_preprocess",
}
ATTR_START = re.compile(r"@\[|(?<![A-Za-z0-9_'!?.])attribute\s*\[")
ATTR_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?.]*")


def attr_blocks(text):
    """(position, content) of every `@[...]` and `attribute [...]` (brackets nested, string
    literals skipped)."""
    for m in ATTR_START.finditer(text):
        i, depth, start = m.end(), 1, m.end()
        while i < len(text) and depth:
            c = text[i]
            if c == '"':
                i += 1
                while i < len(text) and text[i] != '"':
                    i += 2 if text[i] == "\\" else 1
            elif c in "([{":
                depth += 1
            elif c in ")]}":
                depth -= 1
            i += 1
        yield m.start(), text[start:i - 1]


def attr_names(content):
    """Attribute names in the content of `@[...]`: the first identifier of each top-level
    comma-separated entry after `local`/`scoped`/`-`; None for an entry without one."""
    entries, depth, cur, i = [], 0, "", 0
    while i < len(content):
        c = content[i]
        if c == '"':
            j = i + 1
            while j < len(content) and content[j] != '"':
                j += 2 if content[j] == "\\" else 1
            cur += content[i:j + 1]
            i = j + 1
            continue
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        if c == "," and depth == 0:
            entries.append(cur)
            cur = ""
        else:
            cur += c
        i += 1
    entries.append(cur)
    names = []
    for e in entries:
        e = e.strip()
        e = re.sub(r"^(?:(?:local|scoped)\s+)?-?\s*", "", e)
        m = ATTR_NAME.match(e)
        names.append(m.group(0) if m else None)
    return names


RULE_AXIOM = ("axiom (outside trusted/)", word("axiom"))
GUARD = re.compile(r"#guard_msgs(?![A-Za-z0-9_'!?])")
# The only accepted form, in specs/Specs.lean and specs/Specs/: `#guard_msgs in` (no option:
# `(drop …)` would swallow messages, `(error)` etc. would let info pass) followed, on the same
# or the next line, by exactly one `#print axioms <name>` and the end of that line.
GUARD_OK = re.compile(r"#guard_msgs[ \t]+in[ \t]*(?:\r?\n[ \t]*)?#print[ \t]+axioms[ \t]+\S+[ \t]*(?:\r?\n|\Z)")

SKIP_DIRS = {".lake"}


def tracked_lake_paths(formal):
    """Paths tracked by git under FORMAL with a `.lake` component, or None if FORMAL is not
    in a git work tree (or git is missing). Lake loads a committed
    `.lake/config/<idx>/lakefile.olean` (with its trace) as compiled configuration at its first
    command, before any guard could look at it, so nothing under a `.lake` directory may be
    committed."""
    try:
        r = subprocess.run(["git", "-C", formal, "ls-files", "-z", "--", "."],
                           capture_output=True, check=False)
    except OSError:
        return None
    if r.returncode != 0:
        return None
    paths = [p for p in r.stdout.decode("utf-8", "replace").split("\0") if p]
    return [p for p in paths if ".lake" in p.split("/")]


def check_fresh(formal):
    """CI, first step after checkout (before elan or any Lake command): FORMAL/.lake must not
    exist and git must track nothing under a `.lake` directory below FORMAL."""
    errs = []
    if os.path.lexists(os.path.join(formal, ".lake")):
        errs.append(f"{os.path.join(formal, '.lake')} exists in a fresh checkout (committed Lake state?)")
    tracked = tracked_lake_paths(formal)
    if tracked is None:
        errs.append(f"{formal} is not in a git work tree (git ls-files failed)")
    else:
        errs += [f"{p}: tracked by git under a .lake directory" for p in tracked]
    if errs:
        fail(errs + ["fresh-checkout check failed"])
    print("[lean-guard] fresh checkout: no formal/.lake, nothing tracked under a .lake directory")


def lineno(text, pos):
    return text.count("\n", 0, pos) + 1


def check_sources(formal):
    formal = os.path.abspath(formal)
    errs, nfiles = [], 0
    tracked = tracked_lake_paths(formal)
    if tracked is None:
        print("[lean-guard] note: not a git work tree; the check of tracked .lake paths is skipped")
    else:
        errs += [f"{p}: tracked by git under a .lake directory" for p in tracked]
    for dirpath, dirnames, filenames in os.walk(formal):
        rel_dir = os.path.relpath(dirpath, formal)
        if rel_dir == ".":
            dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        for d in list(dirnames):
            if d == ".lake":
                errs.append(f"{os.path.join(rel_dir, d)}: .lake directory below formal/ (only formal/.lake is Lake's)")
                dirnames.remove(d)
        for d in list(dirnames):
            if os.path.islink(os.path.join(dirpath, d)):
                errs.append(f"{os.path.join(rel_dir, d)}: symlinked directory under formal/")
                dirnames.remove(d)
        for fn in filenames:
            path = os.path.join(dirpath, fn)
            rel = os.path.normpath(os.path.join(rel_dir, fn))
            if not fn.endswith(".lean"):
                if fn.lower().endswith(".lean"):
                    errs.append(f"{rel}: Lean file name with a case variant of .lean")
                continue
            if os.path.islink(path):
                errs.append(f"{rel}: symlinked Lean file under formal/")
                continue
            if rel.startswith("specs/Drafts/"):
                continue
            nfiles += 1
            with open(path, encoding="utf-8", errors="replace") as f:
                text = f.read()
            generated = rel.startswith("translation/")
            template = generated and fn.endswith("_Template.lean")
            rules = list(RULES_ALL) + RULES_META
            if not generated:
                rules.append(RULE_LINTER)
            if not template and not rel.startswith("trusted/"):
                rules.append(RULE_AXIOM)
            for name, rx in rules:
                for m in rx.finditer(text):
                    errs.append(f"{rel}:{lineno(text, m.start())}: banned: {name}")
            for m in HASH_CMD.finditer(text):
                if m.group(0) not in HASH_ALLOWED:
                    errs.append(f"{rel}:{lineno(text, m.start())}: banned: {m.group(0)} (only "
                                f"{', '.join(sorted(HASH_ALLOWED))} are allowed)")
            for pos, content in attr_blocks(text):
                for n in attr_names(content):
                    if n not in ATTR_ALLOWED:
                        errs.append(f"{rel}:{lineno(text, pos)}: banned: attribute {n or content.strip()!r} "
                                    "(not in ATTR_ALLOWED)")
            in_specs = rel == "specs/Specs.lean" or rel.startswith("specs/Specs/")
            for m in GUARD.finditer(text):
                # Prose: `#guard_msgs` written in backticks cannot be a command (a backtick
                # before `#` does not parse in Lean), so it is skipped.
                if text[m.start() - 1:m.start()] == "`" and text[m.end():m.end() + 1] == "`":
                    continue
                ln = lineno(text, m.start())
                if not in_specs:
                    errs.append(f"{rel}:{ln}: #guard_msgs is allowed only in specs/Specs.lean and specs/Specs/")
                elif not GUARD_OK.match(text, m.start()):
                    errs.append(f"{rel}:{ln}: #guard_msgs must be exactly `#guard_msgs in` followed by "
                                "one `#print axioms <name>` line (no options, no drop)")
    if errs:
        fail(errs + ["banned words or constructs in Lean sources (see scripts/lean-guard.sh, 'sources')"])
    print(f"[lean-guard] sources: {nfiles} Lean file(s) checked; no banned words or constructs")


# ---------------------------------------------------------------------------------------
# build log

# The four warnings Lake replays from the pinned Aeneas library (formal/docs/evidence/S03.md).
ALLOWED_LOG_LINES = {
    "warning: Aeneas/Std/Slice.lean:363:4: declaration uses `sorry`",
    "warning: Aeneas/Std/Slice.lean:586:8: declaration uses `sorry`",
    "warning: Aeneas/Std/StringIter.lean:12:4: declaration uses `sorry`",
    "warning: Aeneas/Std/StringIter.lean:15:4: declaration uses `sorry`",
}
LOG_FLAG = re.compile(r"warning:|error:")


def check_build_log(path):
    if not os.path.isfile(path) or os.path.getsize(path) == 0:
        fail([f"build log {path} is missing or empty", "build-log check failed"])
    with open(path, encoding="utf-8", errors="replace") as f:
        lines = f.read().splitlines()
    bad, allowed = [], 0
    for i, line in enumerate(lines, 1):
        if not LOG_FLAG.search(line):
            continue
        if line.rstrip("\r") in ALLOWED_LOG_LINES:
            allowed += 1
        else:
            bad.append(f"{path}:{i}: {line}")
    if not any(line.startswith("Build completed successfully") for line in lines):
        bad.append(f"{path}: no 'Build completed successfully' line")
    if bad:
        fail(bad + ["build log has warning/error lines other than the four recorded Aeneas lines"])
    print(f"[lean-guard] build log: only the recorded Aeneas warnings ({allowed} line(s))")


# ---------------------------------------------------------------------------------------
# Aeneas archive vs installed build

# Lake's own bookkeeping, rewritten locally after unpacking (not compared).
SKIP_EXT = (".hash", ".trace")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def check_archive(pkg_lake, archive):
    """Every regular file of ARCHIVE except *.hash/*.trace (oleans incl. .olean.private and
    .olean.server, .ilean, .ir, .c, .json, shared libraries, ...) must be present in
    PKG/.lake/build with the same bytes, and the build must hold no other file (no symlink,
    no file missing from the archive), *.hash/*.trace excepted."""
    build = os.path.join(pkg_lake, "build")
    in_archive, errs = {}, []
    with tarfile.open(archive, "r:gz") as tf:
        for mem in tf.getmembers():
            name = os.path.normpath(mem.name)
            if mem.isdir() or name.endswith(SKIP_EXT):
                continue
            if not mem.isfile():
                errs.append(f"{name}: archive member is not a regular file or directory")
                continue
            in_archive[name] = sha(tf.extractfile(mem).read())
    present = set()
    for dirpath, dirnames, filenames in os.walk(build):
        for d in dirnames:
            if os.path.islink(os.path.join(dirpath, d)):
                errs.append(f"{os.path.relpath(os.path.join(dirpath, d), build)}: symlink in the Aeneas build")
        for fn in filenames:
            path = os.path.join(dirpath, fn)
            rel = os.path.normpath(os.path.relpath(path, build))
            if fn.endswith(SKIP_EXT):
                continue
            if os.path.islink(path) or not os.path.isfile(path):
                errs.append(f"{rel}: not a regular file in the Aeneas build")
                continue
            present.add(rel)
            with open(path, "rb") as f:
                got = sha(f.read())
            if rel not in in_archive:
                errs.append(f"{rel}: in the Aeneas build but not in the release archive")
            elif in_archive[rel] != got:
                errs.append(f"{rel}: differs from the release archive")
    for rel in sorted(set(in_archive) - present):
        errs.append(f"{rel}: in the release archive but missing from the Aeneas build")
    if errs:
        fail(errs[:20] + [f"{len(errs)} difference(s) between the Aeneas build and {os.path.basename(archive)}"])
    print(f"[lean-guard] Aeneas build: {len(present)} file(s) identical to {os.path.basename(archive)} "
          f"(every regular file except *.hash, *.trace)")


def unpack_build(tar, formal):
    """Extracts the build artifact TAR (made in CI job `build` with
    `tar -C formal/.lake -cf TAR build build.log`) into FORMAL/.lake: only regular files and
    directories under build/ and the file build.log, no absolute or `..` path, no link or
    device; FORMAL/.lake/build and build.log must not exist yet."""
    dest = os.path.join(formal, ".lake")
    for n in ("build", "build.log"):
        if os.path.lexists(os.path.join(dest, n)):
            fail([f"{os.path.join(dest, n)} already exists; unpack into a fresh checkout"])
    errs, members = [], []
    with tarfile.open(tar, "r:") as tf:
        for m in tf.getmembers():
            name = m.name
            parts = name.split("/")
            ok_path = (not name.startswith("/") and ".." not in parts
                       and (parts[0] == "build" or name == "build.log"))
            if not ok_path:
                errs.append(f"{name}: outside build/ and build.log")
            elif not (m.isfile() or m.isdir()) or (m.isdir() and name == "build.log"):
                errs.append(f"{name}: not a regular file or directory")
            else:
                members.append(m)
        if errs:
            fail(errs[:20] + [f"build artifact {tar} rejected ({len(errs)} member(s))"])
        os.makedirs(dest, exist_ok=True)
        tf.extractall(dest, members=members, filter="data")
    print(f"[lean-guard] build artifact: {len(members)} member(s) unpacked into {dest}")


# ---------------------------------------------------------------------------------------
# trusted-axiom lock

LOCK_LINE = re.compile(r"(\S+) sha256:([0-9a-f]{64})")


def check_axiom_lock(lock, got):
    """LOCK (formal/trusted/axioms.lock): lines `<axiom name> sha256:<hex>`, `#` comments and
    blank lines ignored. GOT (written by lean-axiom-audit.lean): lines `<name> TAB <canonical
    statement>` for every axiom declared in the roots of RmcpExternal. The set of names must
    be the same, and for each the sha256 of the canonical statement (UTF-8) must be the one
    in the lock."""
    want, errs = {}, []
    with open(lock, encoding="utf-8") as f:
        for i, line in enumerate(f, 1):
            s = line.strip()
            if not s or s.startswith("#"):
                continue
            m = LOCK_LINE.fullmatch(s)
            if not m or m.group(1) in want:
                errs.append(f"{lock}:{i}: not `<name> sha256:<64 hex>` or a duplicate name: {s}")
                continue
            want[m.group(1)] = m.group(2)
    have = {}
    with open(got, encoding="utf-8") as f:
        for line in f.read().splitlines():
            name, sep, stmt = line.partition("\t")
            if not sep:
                errs.append(f"{got}: malformed line {line!r}")
                continue
            have[name] = sha(stmt.encode("utf-8"))
    for n in sorted(set(have) - set(want)):
        errs.append(f"trusted axiom {n} is not in {os.path.basename(lock)} "
                    f"(after review, add the line: {n} sha256:{have[n]})")
    for n in sorted(set(want) - set(have)):
        errs.append(f"{os.path.basename(lock)} lists {n}, which is not an axiom of the RmcpExternal roots")
    for n in sorted(set(want) & set(have)):
        if want[n] != have[n]:
            errs.append(f"trusted axiom {n}: statement hash {have[n]} differs from the lock ({want[n]})")
    if errs:
        fail(errs + ["trusted axioms differ from formal/trusted/axioms.lock"])
    print(f"[lean-guard] trusted axioms: {len(have)}, matching {os.path.basename(lock)}")


COMMANDS = {"fresh": (check_fresh, 1), "axiom-lock": (check_axiom_lock, 2),
            "lakefile": (check_lakefile, 1), "sources": (check_sources, 1),
            "build-log": (check_build_log, 1), "archive": (check_archive, 2),
            "roots": (audit_roots, 1), "leanpath": (lean_path, 1),
            "buildtree": (check_build_tree, 1), "unpack": (unpack_build, 2)}


def main(argv):
    if not argv or argv[0] not in COMMANDS or len(argv) - 1 != COMMANDS[argv[0]][1]:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    fn, _ = COMMANDS[argv[0]]
    try:
        fn(*argv[1:])
    except (OSError, ValueError, tomllib.TOMLDecodeError, tarfile.TarError, KeyError, TypeError) as e:
        print(f"[lean-guard] error: {e}", file=sys.stderr)
        sys.exit(2)


if __name__ == "__main__":
    main(sys.argv[1:])
