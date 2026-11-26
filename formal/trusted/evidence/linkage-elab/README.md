# Negative controls for the elaborated linkage comparison

Step 5 of `scripts/check-original-linkage.sh` decides whether the Phase 2 targets are `ORIGINAL`.
It was added by the human decisions of 2026-11-26, "compare elaborated Lean" and "refuse
committed-only instances", after the round-5 review of the patch-05 translation stage. It was
extended after the round-6 review (a6-1, a6-2) and the round-7 review (a7-1 to a7-3; human
decision 2026-11-26 "enforce in script, then sign off"). It builds the unmodified-source translation (env0)
and the committed one (env1) as Lean environments, each with its own generated External templates.
It then requires:

- every non-auxiliary constant of `Rmcp.Types` and `Rmcp.Funs` of env0 to exist in env1 with the
  same module, kind, universe parameters, type and body. The comparison uses a canonical form: no
  binder names, hygiene or metadata, and every auxiliary constant replaced by its content. The
  auxiliary constants are internal names such as `_proof_N`/`_sizeOf_N`, matchers `match_N` and
  theorems; a theorem is replaced by its statement.
- every external of env0 to have the same universe parameters and type in env1.
- what `Rmcp.Types`/`Rmcp.Funs` export besides constants to differ only as the new declarations
  make it differ:
  - **Instance entries.** env0's entries must be unchanged: name, priority, scoped or global,
    class, and the head of the first argument. A new entry is allowed only if it has the default
    priority, is global, is declared in `Rmcp.Types`, and is either class `SizeOf` named
    `<T>._sizeOf_inst` or class `Aeneas.Std.Discriminant` named `instDiscriminant…`. In both cases
    T, the head of the argument, must be an inductive that only env1 has.
  - **Reducibility.** env0's non-auxiliary constants must keep their reducibility. A new entry is
    allowed only for a new constant of the same module.
  - **Other environment extensions.** The number of module entries of every persistent extension
    must stay the same. Only the extensions in `GROW_OK` of `compare_env.py` may grow, and only in
    the module where they were measured to grow on the real translations. For example, the
    instance extension may grow only in `Rmcp.Types`. Notation, macros, syntax, `export`,
    unification hints and any unknown extension may not grow.
  - A dump with no export section is refused.
- every constant that only env1's translation modules declare, auxiliary ones included, to be
  under `rmcp.` or to be a generated root `instDiscriminant…` instance that passed the instance
  rule. Lean's private prefix `_private.Rmcp.{Types,Funs}.0.` is ignored for this check.

Gates: step 5 runs Lean on committed code, so code that acts at build time could forge what it
reads, for example an `initialize` that writes the dump or a `run_cmd` that spoofs an instance
entry. Step 5 therefore first runs `scripts/lean-guard.sh sources` and stops if it fails; that
check bans `initialize`, `run_cmd`, `#eval`, `IO`, `macro_rules` and `implemented_by`, and refuses
attributes outside `ATTR_ALLOWED`. The other gate is the CI stale-translation check: the
committed translation must be exactly Aeneas output. `run.sh` bypasses lean-guard, so the
reviewer's build-time attacks (round 7: x1 `initialize`, x3 `run_cmd`) are not cases here; the
lean-guard gate refuses them.

Stated limits:

1. The hand-written `formal/trusted/Rmcp/*.lean` (the trusted base). Both environments use the
   templates, because the trusted models use `Type` where the templates use `Type _`.
2. Entries of the growing extensions that committed code attaches to existing constants
   (`attribute [simp]`, `[inline]`, `[implemented_by]`, `[elab_as_elim]`, …). They change proof
   automation, compilation or elaboration hints, not what any constant is. In practice
   `scripts/lean-guard.sh sources` narrows this limit: `implemented_by` is banned in every
   Lean file. `simp`, `inline`, `grind` and `elab_as_elim` are in `ATTR_ALLOWED` and remain
   within the limit. The limit also covers the reducibility hints of
   auxiliary constants, which step 5 ignores (the kernel ignores reducibility).

Lean itself refuses a global reducibility change of a constant from another module, so there is no
case for it. Tools: `scripts/linkage/`.

`run.sh <linkage-scratch-dir> <new empty dir>` injects the text of each `cases/<id>.txt` into a copy
of the committed `Funs.lean`, at the case's `ANCHOR:`:

- a line: the text goes before that line;
- `TOP`: right after `namespace rmcp`;
- `END`: before the final `end rmcp`.

In all three cases the text lands inside `namespace rmcp` unless the case closes it. `run.sh` then
builds the copy as env1 the way step 5 does and compares it with `env0/dump.jsonl` of a completed
linkage run. Each case's `EXPECT:` line is `pass`, or the kinds `compare_env.py` must report, joined
by `+`:

- `differs`: a constant or external differs, or a new name lies outside `rmcp.`;
- `instance`: an instance entry is new or changed;
- `exports`: an extension's entry count changed;
- `reducibility`: a reducibility entry is new or changed.

`run.sh` classifies the output by the exact message prefixes of `compare_env.py` and exits 1
unless every case matches.

| Case | Injected committed-only text | Expected | Origin |
|---|---|---|---|
| e0-control | an unrelated helper `def` | pass | control |
| e1-shadow-def | `def …metadata_resolver.transport.auth.AuthorizationManager.embedded_ipv4` before `AddressClass.of` | differs | name shadowing (reviews a1–b4) |
| e2-indented-def | an indented `def transport.auth.core.net.ip_addr.Ipv4Addr.is_private` | differs | a5-1 |
| e3-root-prefix | `def _root_.rmcp.transport.auth.AuthorizationManager.core.net.ip_addr.Ipv4Addr.is_private` | differs | a5-2 |
| e4-instance-hijack | a high-priority `HAnd (UScalar ty)` instance | differs+instance+exports | a5-3 |
| e5-instance-unused | a high-priority `HAdd Usize` instance that no unmodified block uses | instance+exports | a5-3, human decision "refuse" |
| e6-same-line-def | a shadowing `def` on the same line after another `def` | differs | a5-1 |
| e7-open-no-effect | `namespace evil.…`/`open evil`, which does not change resolution | pass | control (no false refusal) |
| e8-export | `export Evil (g)` of a root `Evil.g`, outside `namespace rmcp` | differs+exports | a6-2 |
| e9-reducibility-own | `attribute [irreducible]` on the existing `transport.auth.AuthorizationManager.embedded_ipv4` | reducibility | a6-2 |
| a6-x1-spoof-discriminant | a high-priority `HAdd U32` instance named `_root_.instDiscriminantEvil`, plus a new structure | differs+instance+exports | a6-1 |
| a6-x2-spoof-sizeof | a high-priority `HAdd U32` instance named `Evil._sizeOf_inst` (structure `Evil` without generated SizeOf) | instance+exports | a6-1 |
| a6-x2b-unsafe-inductive | the same for an `unsafe inductive Evil` | instance+exports | a6-1 |
| a6-x2c-prop-structure | the same for an `inductive EvilP : Prop` | instance+exports | a6-1 |
| a6-x3-scoped-instance | a high-priority `scoped instance` of `HAdd U32` | instance+exports | a6-2 |
| a6-x4-attr-instance-imported | `attribute [instance 10000] lexOrd` (an imported constant) | instance+exports | a6-2 |
| a6-x5-macro-rules | `macro_rules` turning `+` into `HSub.hSub` | exports | a6-2 |
| a6-x7-local-notation | `local notation "true" => Bool.false` before `is_disallowed_metadata_ipv4` | differs+exports | a6-2 |
| a7-x4-root-name-capture | `def _root_.Theorems.metadata_resolver.rmcp.transport.auth.AuthorizationManager.is_disallowed_metadata_ipv4` | differs | a7-2 |
| a7-root-theorem | `theorem _root_.Theorems.evilLemma : True` | differs | a7-2 |

Several expectations gained kinds with the round-7 rules. A new name outside `rmcp.` now counts
as `differs` (e8, a6-x1). The instance extension may grow only in `Rmcp.Types`, so an instance
injected into `Funs.lean` also counts as `exports` (e4, e5, a6-x1 to a6-x4).

Results, 2026-11-26:

- Scratch commit `2172dd3`: the first 8 cases (e0–e7), 8/8 as expected.
- Scratch commit `960d6ce`: the first 8 cases (e0–e7), 8/8 as expected.
- After round 6, scratch commit `c400112`, on `960d6ce`:
  - `scripts/check-original-linkage.sh` exit 0. Template repair rewrote 1 of 1 candidate on each
    side. env0 has 520 constants and 41 externals, all identical in the committed translation, and
    40 generated instances of committed-only types.
  - Then `run.sh`: 18 cases, all as expected.
- **Final run after round 7**, scratch commit `5bb9384`, on `c400112`:
  - `scripts/check-original-linkage.sh` exit 0, with `scripts/lean-guard.sh sources` passing
    inside it. env0 has 520 constants and 41 externals, all identical, and there are 40 generated
    instances.
  - Then `run.sh`: 20 cases, all as expected.
