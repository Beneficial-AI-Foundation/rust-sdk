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
`lean --run scripts/lean-axiom-audit.lean <libdir> <trusted> <axout> <nativeout> <root>...`
with the toolchain's own `lean` binary (not `lake env`; `LEAN_PATH` = toolchain library,
package libraries, project build, and no dynamic-loader variables, set by `lean-guard.sh`):

- `<libdir>`: the project's own build directory (`formal/.lake/build/lib/lean`);
- `<trusted>`: comma-separated modules whose axioms are trusted (the roots of the
  `RmcpExternal` library), or `-` for none;
- `<axout>`: file the audit writes the trusted axioms to (every axiom declared in a trusted
  module of the import closure), one line per axiom,
  `<used|unused> TAB <name> TAB <canonical statement>` (see `canonical` and "Audit scope"
  below), sorted by name; `lean-guard.sh` then compares them with the committed lock
  `formal/trusted/axioms.lock` (`lean_guard.py axiom-lock`);
- `<nativeout>`: file the audit writes the native-code axioms to (see "Native-code axioms"
  below): one line `module TAB <name>` per module of the import closure, then one line
  `native TAB <used|unused> TAB <name> TAB <declaring module> TAB <canonical statement>` per
  native-code axiom reached by any project constant; `lean-guard.sh` compares them with the
  committed lock `formal/trusted/native-axioms.lock` (`lean_guard.py native-lock`);
- `<root>...`: the library roots to audit (their `.olean` must be under `<libdir>`).

Native-code axioms (human decision 2026-11-22, as in the SPQR project's
`scripts/AuditHeadline.lean`): an axiom whose name has a `_native` component (what
`decide +native` and `native_decide` declare, `<decl>._native.decide.ax_<n>`) or that is
`Lean.trustCompiler` trusts the Lean compiler and native code, not only the kernel. Such
axioms are a separately classified trust item. The pinned Aeneas `toStr (s : String)
(h : s.toByteArray.size ≤ U32.max := by decide +native)` leaves one for every string literal
of the translation. The audit accepts a native-code axiom that a project constant depends on
only if (a) it has no universe parameters and its statement is exactly the `toStr` side
condition of one string literal, `decide ("…".toByteArray.size ≤ Aeneas.Std.U32.max) = true`
(see `toStrSideCondition`), (b) it is declared in a root of the generated `Rmcp` library
(`Rmcp.Types` or `Rmcp.Funs`, see `rmcpRoots`; so a hand-written `Aeneas.Std.toStr "x"` in
`Proofs`, `Specs`, `Defs` or a trusted module fails), and (c) if it is `used` (see "Audit
scope" below), `lean_guard.py native-lock` then finds it in `formal/trusted/native-axioms.lock`
with the same module and statement hash. Any native-code axiom reachable from any project
constant (by `reachableAxioms`, see "Audit scope") that fails (a) or (b) fails the audit,
whether or not it is listed or `used`. A native-code axiom declared in a trusted module is
classified as native, not as trusted (and fails by (b)).

Audit scope (human decision 2026-11-23 for `axioms.lock`; the lead applied the same rule to
`native-axioms.lock`): an axiom is `used` if it is reachable from some constant declared in a
module of the `Defs`, `Proofs` or `Specs` library (a module named `Defs`, `Proofs`, `Specs`
or below them, see `specRoots`; every constant of such a module counts, including private
helpers, instances and auxiliary declarations), transitively through any constant, including
the generated `Rmcp.Types`/`Rmcp.Funs` definitions and the externals; otherwise `unused`.
Reachability is computed by `reachableAxioms` (one walk with a single visited set, no
per-constant cache, whole inductive blocks), so the `used` set does not depend on the order
of the constants and contains every axiom `#print axioms` reports for those constants
(an over-approximation: it can contain more, for example an axiom that only another type of
a mutual block mentions). `#print axioms` (`Lean.collectAxioms`) itself can miss an axiom: the
per-module result it stores in the `.olean` files is computed with one cache for the whole
module, which keeps, for a constant entered while its inductive/constructor cycle is open,
the incomplete set computed then; this happens on any such cycle, a non-mutual inductive type
and its constructors as well as a mutual block (`#print axioms` of the constructor
`rmcp.model.request_state.Keys.Single` omits the `HashMap` and `RandomState` axioms that `Keys`
reports). The walk keeps no such cache.
Both locks need to cover only the `used` axioms (`lean_guard.py` reports the `unused` ones
and accepts a lock entry for a declared but `unused` axiom). So importing `Rmcp.Funs` into a
proof module does not require locking the externals that no theorem depends on. The scope
applies to the locks only: checks 1 to 5 below, and the `toStr`-form and `Rmcp`-module
restrictions on native-code axioms, cover every project constant (including all of
`Rmcp.Types`/`Rmcp.Funs`) and every native-code axiom that the same walk reaches from all
project constants (the set `all` of check 3). Consequence: the statement of a declared
trusted axiom that is not locked and not `used` (today all 41 placeholder externals) can
change, or the axiom can vanish, without the audit failing, also in an ordinary PR; only the
source diff of `trusted/` and the informational list printed by `lean_guard.py` show it.

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
3. the set `all` of the axioms reachable from all constants declared in project modules
   (`reachableAxioms` over every project constant at once: one walk, independent of the order
   of the constants, a superset of what `#print axioms` reports for each of them; not the
   per-module cache stored in the `.olean` files) contains an axiom other than `propext`,
   `Classical.choice`, `Quot.sound`, the axioms declared in the trusted modules and the
   native-code axioms; this includes `sorryAx` and `Lean.ofReduceBool`; or `all` contains a
   native-code axiom whose statement is not the `toStr` side condition of a string literal or
   that is not declared in `Rmcp.Types`/`Rmcp.Funs` (the native-code axioms classified and
   compared with the lock are exactly those of `all`). The memoised `axiomsOf` is used only to
   name, in the error messages, the constants that depend on a disallowed axiom as
   `#print axioms` collects; an axiom in `all` that none of them names is reported as reached
   only through the wider edges of the walk, and both counts are printed;
4. the kernel rejects a project constant when all of them are replayed
   (`Lean.Environment.replay`, as `leanchecker` does) into a base environment imported from
   the non-project modules that project modules import. This catches declarations added
   without a kernel check (`debug.skipKernelTC`, `addDecl` from a metaprogram) and `.olean`
   files altered after elaboration. The base environment must not contain a project module
   (otherwise those constants would be in the base and not replayed). `replay` checks
   constructors and recursors against those the kernel generates for the replayed inductive
   types, and skips `unsafe` and `partial` constants; a safe constant cannot use one (the
   kernel would reject it as an unknown constant), and their number is printed;
5. a trusted module (`<trusted>`) declares a constant whose name, with a private prefix
   removed, has the first component `rmcp` (every constant of the module's constant table, so
   also auxiliary and realized ones such as `rmcp.x.eq_1` or `rmcp.x_def`), or adds any alias
   (the `export` command; read from the module's entries of `Lean.aliasExtension`, which the
   import fills also with `loadExts := false`). The generated `Rmcp.Funs` works inside
   `namespace rmcp` and names the externals and Aeneas library functions unqualified, so such a
   name would take precedence over the one the generated code means. `lean_guard.py sources`
   checks the same on the source text. Checks 1, 2 and 5 run before 3, and 3 before 4.
-/

open Lean

namespace AxiomAudit

abbrev M := ReaderT Environment (StateM (NameMap NameSet))

/-- Axioms `c` depends on, memoised. A constant on a cycle (inductive and constructors)
sees an empty set for itself while it is being computed, as in `Lean.collectAxioms`, so the
cached set of a constant entered while its cycle is open can be incomplete and depends on the
order of the calls. Used only to name constants in the error messages of check 3 (which is
decided by `reachableAxioms`). -/
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

/-- Every axiom reachable from the constants `starts`, by one depth-first walk with a single
visited set and no per-constant result cache, so the result does not depend on the order in
which constants are visited (unlike `axiomsOf`, and unlike `Lean.collectAxioms` behind
`#print axioms`, whose cached result for a constant reached on a cycle can be incomplete). The
same cases as `axiomsOf`, widened to whole inductive blocks: types and values of definitions,
theorems and opaque constants; the type of an axiom (and the axiom itself); for an inductive
type its type, its constructors, the other types of its (mutual) block and its recursor; for a
constructor its type and its inductive type; for a recursor its type and the types of its
block. The result is therefore a superset of what `#print axioms` reports for each start
(an over-approximation; it can include an axiom of a constructor or recursor of a block that
the start does not mention). Used for check 3 and the native-code axioms (from all project
constants) and for the audit scope (`used`, from the `Defs`/`Proofs`/`Specs` constants). -/
def reachableAxioms (env : Environment) (starts : Array Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut axs : NameSet := {}
  let mut stack : Array Name := starts
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if visited.contains c then continue
    visited := visited.insert c
    let next : Array Name := match env.find? c with
      | some (.axiomInfo v)  => v.type.getUsedConstants
      | some (.defnInfo v)   => v.type.getUsedConstants ++ v.value.getUsedConstants
      | some (.thmInfo v)    => v.type.getUsedConstants ++ v.value.getUsedConstants
      | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
      | some (.quotInfo _)   => #[]
      | some (.ctorInfo v)   => v.type.getUsedConstants.push v.induct
      | some (.recInfo v)    => v.type.getUsedConstants ++ v.all.toArray
      | some (.inductInfo v) =>
          (v.type.getUsedConstants ++ v.ctors.toArray ++ v.all.toArray).push (mkRecName c)
      | none => #[]
    if env.find? c matches some (.axiomInfo _) then axs := axs.insert c
    for d in next do
      unless visited.contains d do stack := stack.push d
  return axs

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

/-- Native-code axioms, as `isNativeAxiom` of the SPQR project's `scripts/AuditHeadline.lean`:
`Lean.trustCompiler`, or a name with a `_native` component (`<decl>._native.decide.ax_<n>`,
declared by `decide +native` and `native_decide`). -/
def isNativeAxiom (n : Name) : Bool :=
  n == `Lean.trustCompiler || n.components.contains `_native

/-- The statement that `decide +native` proves for the side condition of the pinned Aeneas
`toStr (s : String) (h : s.toByteArray.size ≤ U32.max := by decide +native)` on the string
literal `s`: `@Eq.{1} Bool (@decide (@LE.le.{0} Nat instLENat n Aeneas.Std.U32.max)
(Nat.decLe n Aeneas.Std.U32.max)) true` with `n = ByteArray.size (String.toByteArray s)`.
`Aeneas.Std.U32.max` is named with a single backtick: this script does not import Aeneas. -/
def toStrSideCondition (s : String) : Expr :=
  let n := mkApp (mkConst ``ByteArray.size) (mkApp (mkConst ``String.toByteArray) (mkStrLit s))
  let max := mkConst `Aeneas.Std.U32.max
  let le := mkApp4 (mkConst ``LE.le [Level.zero]) (mkConst ``Nat) (mkConst ``instLENat) n max
  mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool)
    (mkApp2 (mkConst ``Decidable.decide) le (mkApp2 (mkConst ``Nat.decLe) n max))
    (mkConst ``Bool.true)

/-- `some s` if `ci` is an axiom without universe parameters whose statement is exactly
`toStrSideCondition s` (compared by `canonical` text, so up to metadata only); else `none`. -/
def toStrLiteral? (ci : ConstantInfo) : Option String := do
  let .axiomInfo v := ci | none
  guard v.levelParams.isEmpty
  let #[_, d, _] := v.type.getAppArgs | none
  let #[p, _] := d.getAppArgs | none
  let #[_, _, n, _] := p.getAppArgs | none
  let #[b] := n.getAppArgs | none
  let #[.lit (.strVal s)] := b.getAppArgs | none
  guard (canonical v.type == canonical (toStrSideCondition s))
  return s

/-- Whether `n` (with a private prefix `_private.<module>.0.` removed) is `rmcp` or below it. -/
def inRmcpNamespace (n : Name) : Bool :=
  n.getRoot == `rmcp || (privateToUserName n).getRoot == `rmcp

end AxiomAudit

/-- Top-level names of this project's modules (the five libraries of plan Section 5). -/
def projectRoots : List Name := [`Rmcp, `Defs, `Proofs, `Specs]

/-- The roots of the generated `Rmcp` library: the only modules whose native-code axioms
(Aeneas `toStr` side conditions of string literals) are accepted. -/
def rmcpRoots : List Name := [`Rmcp.Types, `Rmcp.Funs]

/-- Top-level names of the modules of the `Defs`, `Proofs` and `Specs` libraries: the axioms
that their constants depend on are the ones the locks must cover (audit scope). -/
def specRoots : List Name := [`Defs, `Proofs, `Specs]

open AxiomAudit in
def main (args : List String) : IO UInt32 := do
  let libDir :: trustedArg :: axOut :: nativeOut :: roots@(_ :: _) := args
    | IO.eprintln "usage: lean --run lean-axiom-audit.lean <libdir> <trusted|-> <axout> \
        <nativeout> <root>..."
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
  -- Check 5: nothing in the trusted modules is named in the namespace `rmcp` (constants, also
  -- private, auxiliary and realized ones), and they add no alias (`export`).
  let mut nsBad : Array String := #[]
  for (c, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? c then
      if trustedIdx.contains idx.toNat && inRmcpNamespace c then
        nsBad := nsBad.push s!"{names[idx.toNat]!}: constant {c} is in the namespace rmcp"
  for i in trustedIdx.toArray.qsort (· < ·) do
    let entries := PersistentEnvExtension.getModuleEntries
      (aliasExtension : PersistentEnvExtension AliasEntry AliasEntry (List AliasEntry × AliasState))
      env i
    for (a, e) in entries do
      nsBad := nsBad.push s!"{names[i]!}: alias {a} → {e} (`export`; none is allowed in a \
        trusted module{if inRmcpNamespace a then ", and this one is in the namespace rmcp" else ""})"
  unless nsBad.isEmpty do
    for s in nsBad.qsort (· < ·) do IO.eprintln s!"[axiom-audit] {s}"
    IO.eprintln s!"[axiom-audit] error: {nsBad.size} name(s) of a trusted module in the namespace \
      rmcp or added as an alias (the generated Rmcp.Funs works inside `namespace rmcp`, so such a \
      name would take precedence over the one the generated code means)"
    return 1
  -- Allowed axioms: Lean's three standard axioms and those declared in trusted modules.
  let mut allowed : NameSet := ({} : NameSet).insert ``propext |>.insert ``Classical.choice
    |>.insert ``Quot.sound
  let mut consts : Array Name := #[]
  let mut trustedAx : Array (Name × String) := #[]
  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  for (c, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? c then
      if ours.contains idx.toNat then
        consts := consts.push c
        newConsts := newConsts.insert c ci
        if trustedIdx.contains idx.toNat && ci matches .axiomInfo _ && !isNativeAxiom c then
          allowed := allowed.insert c
          let lps := " ".intercalate (ci.levelParams.map (·.toString (escape := true)))
          trustedAx := trustedAx.push
            (c, s!"{c.toString (escape := true)}\t(U [{lps}] {canonical ci.type})")
  let sorted := consts.qsort Name.lt
  let modOf (c : Name) : Name := match env.getModuleIdxFor? c with
    | some i => names[i.toNat]!
    | none => Name.anonymous
  -- Check 3: `all` = every axiom reachable from any project constant (one walk, see
  -- `reachableAxioms`; independent of the order of the constants). It decides check 3 and
  -- which native-code axioms are classified (accepted only in the `toStr` form, then checked
  -- against the lock). The memoised `axiomsOf` only names, in the messages, the constants
  -- that depend on a disallowed axiom.
  let all := reachableAxioms env sorted
  let disallowed := (all.toArray.filter fun a => !allowed.contains a && !isNativeAxiom a).qsort
    Name.lt
  unless disallowed.isEmpty do
    let perConst : M (Array (Name × Array Name)) :=
      sorted.foldlM (init := #[]) fun acc c => do
        let extra := (← axiomsOf c).toArray.qsort Name.lt
          |>.filter fun a => !allowed.contains a && !isNativeAxiom a
        return if extra.isEmpty then acc else acc.push (c, extra)
    let bad : Array (Name × Array Name) := (perConst.run env).run' {}
    for (c, extra) in bad do
      IO.eprintln s!"[axiom-audit] {modOf c}: {c} depends on {extra.toList}"
    let named : NameSet := bad.foldl (fun s (_, e) => e.foldl (·.insert ·) s) {}
    let walkOnly := disallowed.filter (!named.contains ·)
    unless walkOnly.isEmpty do
      IO.eprintln s!"[axiom-audit] project constants reach the disallowed axiom(s) \
        {walkOnly.toList} only through the wider edges of the walk (another type, constructor or \
        recursor of an inductive block that a constant mentions), which `#print axioms` does \
        not follow"
    IO.eprintln s!"[axiom-audit] error: {disallowed.size} disallowed axiom(s) reached by project \
      constants ({bad.size} constant(s) depend on one as `#print axioms` collects; \
      {walkOnly.size} axiom(s) reached only through the wider edges of the walk)"
    return 1
  -- `used`: the axioms reachable from the constants declared in a `Defs`/`Proofs`/`Specs`
  -- module (audit scope, human decision 2026-11-23; see the module docstring), by the same walk.
  let used := reachableAxioms env (sorted.filter fun c => specRoots.contains (modOf c).getRoot)
  let usage (n : Name) : String := if used.contains n then "used" else "unused"
  let natives := (all.toArray.filter isNativeAxiom).qsort Name.lt
  let mut nativeLines : Array String := #[]
  let mut nativeShown : Array String := #[]
  let mut nativeBad : Array Name := #[]
  for n in natives do
    match env.find? n >>= toStrLiteral? with
    | some s =>
      if rmcpRoots.contains (modOf n) then
        nativeLines := nativeLines.push s!"native\t{usage n}\t{n.toString (escape := true)}\t\
          {(modOf n).toString (escape := true)}\t(U [] {canonical (env.find? n).get!.type})"
        nativeShown := nativeShown.push s!"{n} ({modOf n}, {usage n}): toStr side condition of \
          {s.quote}"
      else
        nativeBad := nativeBad.push n
        IO.eprintln s!"[axiom-audit] {modOf n}: native-code axiom {n} has the toStr form but is \
          declared outside the generated modules {rmcpRoots}; only those may be locked"
    | none =>
      nativeBad := nativeBad.push n
      IO.eprintln s!"[axiom-audit] {modOf n}: native-code axiom {n} is not the Aeneas toStr \
        side condition `decide (\"…\".toByteArray.size ≤ Aeneas.Std.U32.max) = true` of a \
        string literal; only those may be locked (formal/trusted/native-axioms.lock)"
  unless nativeBad.isEmpty do
    IO.eprintln s!"[axiom-audit] error: {nativeBad.size} native-code axiom(s) of another form or \
      declared outside {rmcpRoots}"
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
  let axLines := (trustedAx.qsort (fun a b => a.2 < b.2)).toList.map fun (c, l) =>
    s!"{usage c}\t{l}\n"
  IO.FS.writeFile axOut (String.join axLines)
  let modLines := names.toList.map fun m => s!"module\t{m.toString (escape := true)}\n"
  IO.FS.writeFile nativeOut (String.join (modLines ++ nativeLines.toList.map (· ++ "\n")))
  IO.println s!"[axiom-audit] {sorted.size} constant(s) in {ours.size} project module(s): \
    no axiom outside [propext, Classical.choice, Quot.sound], the {trustedAx.size} trusted \
    axiom(s) of the RmcpExternal roots and the native-code axioms below"
  let usedTrusted := trustedAx.filter (used.contains ·.1)
  IO.println s!"[axiom-audit] trusted axioms (roots of RmcpExternal) in the closure: \
    {trustedAx.size}, of which {usedTrusted.size} used by a constant of {specRoots} \
    (checked next against axioms.lock)"
  IO.println s!"[axiom-audit] native-code axioms reached (Aeneas toStr side conditions, \
    checked next against native-axioms.lock): {natives.size}, of which \
    {(natives.filter used.contains).size} used by a constant of {specRoots}"
  for l in nativeShown do IO.println s!"[axiom-audit]   {l}"
  IO.println s!"[axiom-audit] kernel replay of {sorted.size - skipped} constant(s) onto \
    {baseImports.size} dependency import(s): accepted ({skipped} unsafe/partial skipped)"
  return 0
