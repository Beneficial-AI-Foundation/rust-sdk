/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Lean
import Lean.Replay
import Lake.Build.Trace

/-!
# Axiom audit and kernel replay of the built Lean project

Run by `scripts/lean-guard.sh axioms` after `lake build`, as
`lean --run scripts/lean-axiom-audit.lean <libdir> <trusted> <axout> <root>...` with the
toolchain's own `lean` binary (not `lake env`; `LEAN_PATH` = toolchain library, package
libraries, project build, and no dynamic-loader variables, set by `lean-guard.sh`):

- `<libdir>`: the project's own build directory (`formal/.lake/build/lib/lean`);
- `<trusted>`: comma-separated modules whose axioms are trusted (the roots of the
  `RmcpExternal` library), or `-` for none;
- `<axout>`: file the audit writes the trusted axioms to, one line per axiom,
  `<name> TAB <canonical statement>` (see `canonical`), sorted by name; `lean-guard.sh` then
  compares them with the committed lock `formal/trusted/axioms.lock` (`lean_guard.py
  axiom-lock`);
- `<root>...`: the library roots to audit (their `.olean` must be under `<libdir>`).

It imports the roots with `loadExts := false` (only the constant tables of the `.olean` files
are read; no environment extension, initializer or other code of an imported module runs) and
takes every module of the import closure whose `.olean` lies under `<libdir>` (every module of
this project that the roots reach). It exits with 1 if

1. a module under `<libdir>` is not named `Rmcp`, `Defs`, `Proofs`, `Specs` or below them, or
   a module with such a name resolves outside `<libdir>`;
2. the Lake trace of a project module (`X.trace` beside `X.olean`) does not record exactly
   one source file `<srcDir>/<module path>.lean`, or that file under the `formal/` directory
   four levels above `<libdir>` does not have the recorded text hash: the `.olean` is stale
   (the source changed after the last successful build). This guards local runs. It is no check
   against forged build output (a forged trace passes it); check 4 rejects forged output
   the kernel does not accept, but nothing here proves it was compiled from these sources;
3. a constant declared in a project module depends on an axiom other than `propext`,
   `Classical.choice`, `Quot.sound` and the axioms declared in the trusted modules (collected
   transitively through types and values, as `#print axioms` does, but without the per-module
   cache stored in the `.olean` files); this includes `sorryAx` and `Lean.ofReduceBool`
   (`native_decide`, `decide +native`);
4. the kernel rejects a project constant when all of them are replayed
   (`Lean.Environment.replay`, as `leanchecker` does) into a base environment imported from
   the non-project modules that project modules import. This catches declarations added
   without a kernel check (`debug.skipKernelTC`, `addDecl` from a metaprogram) and `.olean`
   files altered after elaboration. The base environment must not contain a project module
   (otherwise those constants would be in the base and not replayed). `replay` checks
   constructors and recursors against those the kernel generates for the replayed inductive
   types, and skips `unsafe` and `partial` constants; a safe constant cannot use one (the
   kernel would reject it as an unknown constant), and their number is printed.
-/

open Lean

namespace AxiomAudit

abbrev M := ReaderT Environment (StateM (NameMap NameSet))

/-- Axioms `c` depends on, memoised. A constant on a cycle (inductive and constructors)
sees an empty set for itself while it is being computed, as in `Lean.collectAxioms`. -/
partial def axiomsOf (c : Name) : M NameSet := do
  if let some s := (← get).find? c then return s
  modify (·.insert c {})
  let env ← read
  let ofExpr (e : Expr) : M NameSet :=
    e.getUsedConstants.foldlM (init := {}) fun acc d => return acc.append (← axiomsOf d)
  let s ← match env.find? c with
    | some (.axiomInfo v)  => pure ((← ofExpr v.type).insert c)
    | some (.defnInfo v)   => pure ((← ofExpr v.type).append (← ofExpr v.value))
    | some (.thmInfo v)    => pure ((← ofExpr v.type).append (← ofExpr v.value))
    | some (.opaqueInfo v) => pure ((← ofExpr v.type).append (← ofExpr v.value))
    | some (.quotInfo _)   => pure {}
    | some (.ctorInfo v)   => ofExpr v.type
    | some (.recInfo v)    => ofExpr v.type
    | some (.inductInfo v) =>
        v.ctors.foldlM (init := ← ofExpr v.type) fun acc d => return acc.append (← axiomsOf d)
    | none => pure {}
  modify (·.insert c s)
  return s

/-- Whether `p` lies under the directory `dir`, both canonicalised (symlinks resolved). -/
def underDir (dir : String) (p : System.FilePath) : IO Bool := do
  let d := (← IO.FS.realPath dir).toString
  let q := (← IO.FS.realPath p).toString
  return q.startsWith (if d.endsWith "/" then d else d ++ "/")

/-- Source directories of the five libraries (plan Section 5), relative to `formal/`. -/
def srcDirs : List String := ["translation", "trusted", "specs", "proofs"]

/-- `none` if the Lake trace next to `olean` (`X.trace` beside `X.olean`) records exactly one
source file, `<srcDir>/<module path>.lean` for a library source directory, and the file of
that name under `formalDir` has the recorded text hash; otherwise the reason. Lake records
the hash of the source it compiled, so a mismatch means that the source changed after the
last successful build (stale `.olean`). Only the relative part of the recorded (absolute)
path is used, so a build checked in another checkout of the same commit passes. -/
def staleReason (formalDir : String) (mod : Name) (olean : System.FilePath) :
    IO (Option String) := do
  let trace := olean.withExtension "trace"
  unless ← trace.pathExists do return some s!"no Lake trace {trace}"
  let some json := (Json.parse (← IO.FS.readFile trace)).toOption
    | return some s!"unreadable Lake trace {trace}"
  let inputs := (json.getObjValD "inputs").getArr?.toOption.getD #[]
  let modPath := "/".intercalate (mod.components.map (·.toString)) ++ ".lean"
  let mut srcs : Array (String × String) := #[]
  for e in inputs do
    if let .ok #[.str path, .str h] := e.getArr? then
      if path.endsWith ".lean" then srcs := srcs.push (path, h)
  let #[(path, h)] := srcs
    | return some s!"Lake trace {trace} records {srcs.size} source file(s), expected one"
  let some dir := srcDirs.find? (fun d => path.endsWith ("/" ++ d ++ "/" ++ modPath))
    | return some s!"Lake trace records the source {path}, not <srcDir>/{modPath}"
  let src : System.FilePath := formalDir ++ "/" ++ dir ++ "/" ++ modPath
  unless ← src.pathExists do return some s!"the source {src} does not exist"
  let now := (← Lake.computeTextFileHash src).toString
  if now != h then
    return some s!"{src} changed after the build (hash {now}, built from {h})"
  return none

/-- Canonical text of a universe level (structural; parameters by name). -/
partial def canonLevel : Level → String
  | .zero => "0"
  | .succ l => s!"(s {canonLevel l})"
  | .max a b => s!"(m {canonLevel a} {canonLevel b})"
  | .imax a b => s!"(i {canonLevel a} {canonLevel b})"
  | .param n => s!"(p {n.toString (escape := true)})"
  | .mvar _ => "?"

/-- Canonical structural text of an expression, for the trusted-axiom lock: constants by full
name with their universe levels, bound variables as de Bruijn indices, binder info kept,
binder names and metadata dropped. Two statements have the same text iff they are the same
`Expr` up to binder names and metadata, so the text (and its sha256, taken by `lean_guard.py`)
does not depend on pretty-printer options, notation or the platform. -/
partial def canonical : Expr → String
  | .bvar i => s!"#{i}"
  | .fvar _ | .mvar _ => "?"
  | .sort l => s!"(S {canonLevel l})"
  | .const n ls => s!"(C {n.toString (escape := true)}{String.join (ls.map (" " ++ canonLevel ·))})"
  | .app f a => s!"(A {canonical f} {canonical a})"
  | .lam _ t b bi => s!"(L {repr bi} {canonical t} {canonical b})"
  | .forallE _ t b bi => s!"(P {repr bi} {canonical t} {canonical b})"
  | .letE _ t v b _ => s!"(E {canonical t} {canonical v} {canonical b})"
  | .lit (.natVal n) => s!"(N {n})"
  | .lit (.strVal s) => s!"(T {s.quote})"
  | .mdata _ e => canonical e
  | .proj s i e => s!"(J {s.toString (escape := true)} {i} {canonical e})"

end AxiomAudit

/-- Top-level names of this project's modules (the five libraries of plan Section 5). -/
def projectRoots : List Name := [`Rmcp, `Defs, `Proofs, `Specs]

open AxiomAudit in
def main (args : List String) : IO UInt32 := do
  let libDir :: trustedArg :: axOut :: roots@(_ :: _) := args
    | IO.eprintln "usage: lean --run lean-axiom-audit.lean <libdir> <trusted|-> <axout> <root>..."
      return 2
  initSearchPath (← findSysroot)
  let trusted : List Name :=
    if trustedArg == "-" then [] else (trustedArg.splitOn ",").map String.toName
  let roots := roots.map String.toName
  for r in roots do
    let some p ← (some <$> findOLean r) <|> pure none
      | IO.eprintln s!"[axiom-audit] error: root {r} is not built (no .olean in the search path); run lake build first"
        return 1
    unless (← p.pathExists) do
      IO.eprintln s!"[axiom-audit] error: root {r} is not built ({p} missing); run lake build first"
      return 1
    unless (← underDir libDir p) do
      IO.eprintln s!"[axiom-audit] error: root {r} resolves to {p}, outside {libDir}"
      return 1
  -- `loadExts := false`: only constant tables are read; no imported code runs.
  let env ← importModules (roots.toArray.map ({ module := · })) {} (loadExts := false)
  -- Modules of this project reached from the roots.
  let mut ours : Std.HashSet Nat := {}
  let mut trustedIdx : Std.HashSet Nat := {}
  let mut misplaced : Array String := #[]
  let names := env.header.moduleNames
  for h : i in [0:names.size] do
    let p ← findOLean names[i]
    let inLib ← underDir libDir p
    let projName := projectRoots.contains names[i].getRoot
    if inLib != projName then
      misplaced := misplaced.push s!"{names[i]} ({p})"
    if inLib then
      ours := ours.insert i
      if trusted.contains names[i] then trustedIdx := trustedIdx.insert i
  unless misplaced.isEmpty do
    for m in misplaced do
      IO.eprintln s!"[axiom-audit] {m}: a project module must be named {projectRoots} or below and \
        lie under {libDir}, and no other module may"
    IO.eprintln s!"[axiom-audit] error: {misplaced.size} module(s) with a misplaced name or .olean"
    return 1
  -- Every project .olean was built from the current source (stale-build check).
  let some formalDir := (← IO.FS.realPath libDir).parent >>= (·.parent) >>= (·.parent) >>= (·.parent)
    | IO.eprintln s!"[axiom-audit] error: {libDir} is not <formal>/.lake/build/lib/lean"
      return 1
  let formalDir := formalDir.toString
  let mut stale : Array String := #[]
  for i in ours.toArray.qsort (· < ·) do
    if let some why ← staleReason formalDir names[i]! (← findOLean names[i]!) then
      stale := stale.push s!"{names[i]!}: {why}"
  unless stale.isEmpty do
    for s in stale do IO.eprintln s!"[axiom-audit] {s}"
    IO.eprintln "[axiom-audit] error: stale or unverifiable build; run lake build (successfully) first"
    return 1
  for t in trusted do
    unless names.contains t do
      IO.eprintln s!"[axiom-audit] note: trusted module {t} is not reached from the roots"
  -- Allowed axioms: Lean's three standard axioms and those declared in trusted modules.
  let mut allowed : NameSet := ({} : NameSet).insert ``propext |>.insert ``Classical.choice
    |>.insert ``Quot.sound
  let mut consts : Array Name := #[]
  let mut trustedAx : Array String := #[]
  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  for (c, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? c then
      if ours.contains idx.toNat then
        consts := consts.push c
        newConsts := newConsts.insert c ci
        if trustedIdx.contains idx.toNat && ci matches .axiomInfo _ then
          allowed := allowed.insert c
          let lps := " ".intercalate (ci.levelParams.map (·.toString (escape := true)))
          trustedAx := trustedAx.push
            s!"{c.toString (escape := true)}\t(U [{lps}] {canonical ci.type})"
  let sorted := consts.qsort Name.lt
  let check : M (Array (Name × Array Name)) :=
    sorted.foldlM (init := #[]) fun acc c => do
      let axs := (← axiomsOf c).toArray.qsort Name.lt
      let extra := axs.filter (!allowed.contains ·)
      return if extra.isEmpty then acc else acc.push (c, extra)
  let bad : Array (Name × Array Name) := (check.run env).run' {}
  for (c, extra) in bad do
    let m : Name := match env.getModuleIdxFor? c with
      | some i => names[i.toNat]!
      | none => Name.anonymous
    IO.eprintln s!"[axiom-audit] {m}: {c} depends on {extra.toList}"
  unless bad.isEmpty do
    IO.eprintln s!"[axiom-audit] error: {bad.size} constant(s) depend on disallowed axioms"
    return 1
  -- Kernel replay. Base: the non-project modules imported by project modules (and their
  -- closure, which must not reach a project module).
  let mut baseImports : Array Import := #[]
  for i in ours.toArray.qsort (· < ·) do
    for imp in env.header.moduleData[i]!.imports do
      if let some j := names.idxOf? imp.module then
        if !ours.contains j && !baseImports.any (·.module == imp.module) then
          baseImports := baseImports.push { module := imp.module }
  let base ← importModules baseImports {} (loadExts := false)
  for m in base.header.moduleNames do
    if ← underDir libDir (← findOLean m) then
      IO.eprintln s!"[axiom-audit] error: the dependency closure {baseImports.map (·.module)} \
        contains the project module {m}"
      return 1
  let skipped : Nat := newConsts.fold (init := 0) fun n _ ci =>
    if ci.isUnsafe || ci.isPartial then n + 1 else n
  if let .error e ← (base.replay newConsts).toBaseIO then
    IO.eprintln s!"[axiom-audit] kernel replay: {e}"
    IO.eprintln "[axiom-audit] error: the kernel rejects a project constant on replay"
    return 1
  IO.FS.writeFile axOut (String.join ((trustedAx.qsort (· < ·)).toList.map (· ++ "\n")))
  IO.println s!"[axiom-audit] {sorted.size} constant(s) in {ours.size} project module(s): \
    no axiom outside {allowed.toList}"
  IO.println s!"[axiom-audit] kernel replay of {sorted.size - skipped} constant(s) onto \
    {baseImports.size} dependency import(s): accepted ({skipped} unsafe/partial skipped)"
  return 0
