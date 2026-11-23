# Incorporating the W batch (S06 + S10): one procedure

This is the single procedure for moving the 16 `request_state_wire` statements into the project
once the human has reviewed them: S06's 11 (W01–W06, W12–W15, `frame_roundtrip`) and S10's 5
(W07–W11). They share one staged spec file, `formal/specs/Drafts/Staged/RequestStateWire.lean`,
so they are incorporated together, in one change. It supersedes the separate "How to
incorporate" sections of `evidence/S06.md` and `evidence/S10.md`.

Until then the STAGED rules hold: no proof module is imported by a library root, no record says
`proof: CHECKED`, and the statements stay in `formal/specs/Drafts/RequestStateWire.lean`.

How to run it: every step below is a `bash` block. Run the blocks in order, each in a fresh
shell started anywhere inside the repository (each block `cd`s to the repository root), with
`set -e -o pipefail` in effect (`bash -e -o pipefail <block>`), and stop at the first non-zero
exit. `WORK` is a scratch directory for the procedure's own files (default
`/tmp/wbatch-incorporation`). Step 5 is a human action and has no block. The blocks were run
literally, in this order, in a scratch copy of the repository; see "Simulation record" at the
end.

## Prerequisite (human, before step 0): commit the signed-off state

The signed-off statement text has to be in git history before the draft is deleted in step 3,
and `git mv` in step 1 needs the staged file to be tracked (today `formal/specs/Drafts/Staged/`
and `formal/proofs/Proofs/` are untracked). The 16 statements are already committed, unchanged,
in `formal/specs/Drafts/RequestStateWire.lean` at `adce319`; the working-tree edits to that file
since `adce319` are docstrings only (`git diff adce319 -- formal/specs/Drafts/RequestStateWire.lean`
touches only docstrings: the module docstring and the `b64_len_spec`, `component_count_spec`,
`transcript_v1_spec` and `frame_spec` docstrings). Commit the current state so the
exact signed-off file, the staged file and the proofs are in history, and cite that commit in the
records (step 4 reads it from `$WORK/signoff-commit`).

Order: you may run steps 0 and 0b (read-only) before Step P, so that a mismatch is caught before
the commit. After step 7, the final commit must `git add formal/proofs/Proofs.lean` and
`formal/specs/Specs.lean` explicitly if they are untracked (`git commit -a` would miss them), plus
the new spec file and the 15 records.

Note: the repository's pre-commit hook (`.githooks/pre-commit`, `core.hooksPath = .githooks`)
runs `cargo +nightly fmt --all` and then `git add -u`, so the commit also takes every other
modified tracked file in the working tree. Commit everything that is meant to be in it.

```bash
# Step P — commit the signed-off state (human)
cd "$(git rev-parse --show-toplevel)"
WORK="${WORK:-/tmp/wbatch-incorporation}"; mkdir -p "$WORK"
git add formal/specs/Drafts/RequestStateWire.lean formal/specs/Drafts/Staged/RequestStateWire.lean \
  formal/proofs/Proofs/Model/RequestStateWire formal/docs/evidence/S06.md \
  formal/docs/evidence/S10.md formal/docs/review
git commit -q -m "verification: S06 and S10 proofs staged (signed-off W statements)"
git rev-parse --short HEAD > "$WORK/signoff-commit"
echo "signed-off state: $(cat "$WORK/signoff-commit")"
```

## Step 0: text identity of the 16 statements, before anything moves

`recall` checks only that the restated type is definitionally equal to the proved one, so a
recalled statement whose text differs from the signed-off one (for example `drop 8` for
`drop expiryLen`) would still pass. The checker compares the text of each statement in the draft,
the staged file and the proof files at their current paths, with comments removed, the prefix
`rmcp.model.request_state_wire.` removed and whitespace collapsed. It must print
`16/16 identical` and exit 0; record its output. Stop if it does not.

```bash
# Step 0 — text identity checker (16 names)
cd "$(git rev-parse --show-toplevel)"
WORK="${WORK:-/tmp/wbatch-incorporation}"; mkdir -p "$WORK"
cat > "$WORK/textid.py" <<'EOF'
# Text identity of the S06 and S10 statements: signed-off draft vs staged recall vs proof files.
# Usage: python3 -I textid.py <repo>   (exit 0 iff all names identical)
import re, sys, glob, pathlib
R = pathlib.Path(sys.argv[1]) / "formal"
NAMES = ["b64_len_spec","key_length_ok_spec","check_kid_len_spec","bytes_eq_spec","next_dot_spec",
         "component_count_spec","version_of_spec","parse_rs1_spec","parse_rs2_spec",
         "transcript_v1_spec","transcript_v2_spec","decode_expiry_spec","is_expired_spec",
         "open_frame_spec","frame_spec","frame_roundtrip"]
PFX = "rmcp.model.request_state_wire."
def strip_comments(t):
    t = re.sub(r"/-.*?-/", " ", t, flags=re.S)          # block and doc comments
    return re.sub(r"--[^\n]*", " ", t)
def stmt(text, kw, name):
    t = strip_comments(text)
    end = r":=" if kw == "theorem" else r"(?=#guard_msgs|\brecall\b|\Z)"
    m = re.search(r"\b%s\s+(?:%s)?%s\b(.*?)%s" % (kw, re.escape(PFX), re.escape(name), end), t, re.S)
    return None if not m else " ".join(m.group(1).replace(PFX, "").split())
draft  = (R/"specs/Drafts/RequestStateWire.lean").read_text()
staged = (R/"specs/Drafts/Staged/RequestStateWire.lean").read_text()
proofs = "\n".join(p.read_text() for p in sorted((R/"proofs/Proofs/Model/RequestStateWire").glob("*.lean")))
ok = 0
for n in NAMES:
    d, s, p = stmt(draft, "theorem", n), stmt(staged, "recall", n), stmt(proofs, "theorem", n)
    same = d is not None and d == s == p
    ok += same
    print(("same " if same else "DIFF ") + n + ("" if same else f"\n  draft={d}\n  staged={s}\n  proof={p}"))
print(f"{ok}/{len(NAMES)} identical"); sys.exit(0 if ok == len(NAMES) else 1)
EOF
python3 -I "$WORK/textid.py" "$PWD"
```

## Step 0b: guard the staged text at its final path, before anything moves

`scripts/lean-guard.sh sources` skips `formal/specs/Drafts/`, so the staged file's text
(docstrings and comments included: the bans are textual, e.g. the word for a postulate outside
`trusted/`, the placeholder-proof word, the metaprogramming words) is first checked when it
leaves `Drafts/`. This step checks it before the move: it copies `formal/` (without `.lake/`)
and `scripts/` into a fresh scratch directory under `$WORK`, puts the staged file at its final
path `formal/specs/Specs/Model/RequestStateWire.lean` there, and runs `sources` on that copy (the
copy is not a git work tree, so the git-tracking check is skipped with a note). It must exit 0;
otherwise reword the staged docstring (e.g. "trusted base" or "assumption") and repeat steps 0
and 0b. The header that step 1 writes is checked again by `sources` in step 7.

```bash
# Step 0b — guard the staged file at its final path, in a scratch copy
cd "$(git rev-parse --show-toplevel)"
WORK="${WORK:-/tmp/wbatch-incorporation}"; mkdir -p "$WORK"
G="$(mktemp -d "$WORK/guard-precheck.XXXXXX")"
rsync -a --exclude /.lake formal/ "$G/formal/"
rsync -a scripts/ "$G/scripts/"
mkdir -p "$G/formal/specs/Specs/Model"
cp formal/specs/Drafts/Staged/RequestStateWire.lean "$G/formal/specs/Specs/Model/RequestStateWire.lean"
"$G/scripts/lean-guard.sh" sources
```

## Step 1: move the staged file into `Specs` and rewrite its header once

Moves `formal/specs/Drafts/Staged/RequestStateWire.lean` to
`formal/specs/Specs/Model/RequestStateWire.lean`, replaces everything before the line
`open Aeneas Aeneas.Std Result` (copyright header, imports, staging docstring) by the header
below, and checks that everything from that line on (the `open`s and the 16 `recall` blocks with
their axiom checks) is byte-for-byte what was staged. The `Specs` file imports `Defs`, `Proofs`
and `Mathlib.Tactic.Recall` (option A of step 6; under option B the third import moves to
`Defs.lean`).

```bash
# Step 1 — move the staged spec file and rewrite its header
cd "$(git rev-parse --show-toplevel)"
WORK="${WORK:-/tmp/wbatch-incorporation}"; mkdir -p "$WORK"
S=formal/specs/Drafts/Staged/RequestStateWire.lean
F=formal/specs/Specs/Model/RequestStateWire.lean
sed -n '/^open Aeneas Aeneas.Std Result$/,$p' "$S" > "$WORK/staged-body.lean"
test "$(grep -c '^recall ' "$WORK/staged-body.lean")" -eq 16
mkdir -p formal/specs/Specs/Model
git mv "$S" "$F"
cat > "$WORK/header.lean" <<'EOF'
/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Defs
import Proofs
import Mathlib.Tactic.Recall

/-!
# Spec file for crates/rmcp/src/model/request_state_wire.rs

Statements of the fifteen public wire functions of `crates/rmcp/src/model/request_state_wire.rs`
(plan Section 2.1, W01–W15) and of the composition theorem `frame_roundtrip`, in Rust source
order with the composition theorem last. Each is restated with `recall` from its proof in
`Proofs/Model/RequestStateWire/` and followed by the assumptions its proof depends on, checked by
`#print axioms` under `#guard_msgs`. The statements were signed off by the spec owner on
2026-11-23 (evidence/S05.md); their signed-off text is in `specs/Drafts/RequestStateWire.lean`
at commit `adce319`, removed when they were incorporated (docs/review/W-batch-incorporation.md).

Translated configuration (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
features `--no-default-features --features request-state`, with `overflow-checks=true` and
`debug-assertions=true` (every cargo call gets `--config profile.dev.overflow-checks=true` and
`--config profile.dev.debug-assertions=true`, plan Section 1), so arithmetic overflow panics,
which Aeneas models as failure. Aeneas `nightly-2026.08.20-5d08da4`; the translation base is
local commit `adce319` (S04a part 2), not yet a pinned fork commit. Line numbers refer to
`request_state_wire.rs` at `adce319`.

Definitions used: `Defs.Wire` (`b64Len`, `minKeyLength`, `maxKidLen`, `dot`, `components`,
`versionV1`, `versionV2`, `transcriptV1`, `transcriptV2`, `beNat`, `toInt64`, `Expired`,
`expiryLen`, `bodyExpiry`, `frameBytes`).

Opaque functions: the four functions of the module `prim` (`hmac_sha256`, `hmac_sha256_verify`,
`b64_encode_into`, `b64_decode`) are not translated from Rust; they are opaque and modelled in
`trusted/Rmcp/FunsExternal.lean` (plan Sections 2.1 and 4). No statement here mentions them.

Not translated from this file: the derived `Debug` impls of `KidError`, `Version`, `Rs1Parts`,
`Rs2Parts` and `FrameError` (Charon `exclude` in `crates/rmcp/Cargo.toml`). No function of this
file is in the excluded list of plan Section 2.3.
-/

EOF
cat "$WORK/header.lean" "$WORK/staged-body.lean" > "$F"
sed -n '/^open Aeneas Aeneas.Std Result$/,$p' "$F" | diff - "$WORK/staged-body.lean"
test "$(grep -c '^recall ' "$F")" -eq 16
test "$(grep -c '^#guard_msgs in$' "$F")" -eq 16
```

## Step 2: add the modules to the library roots

Adds `Common` and the 15 target modules to `formal/proofs/Proofs.lean` and the spec module to
`formal/specs/Specs.lean`, and replaces the docstring sentence `Empty until S06.` in both. The
script stops if an anchor is missing (for example if another step already edited these lines);
then add the same imports by hand and adapt the sentence.

```bash
# Step 2 — library roots
cd "$(git rev-parse --show-toplevel)"
python3 -I - <<'EOF'
import pathlib
mods = ["Common", "B64Len", "KeyLengthOk", "CheckKidLen", "BytesEq", "NextDot", "ComponentCount",
        "VersionOf", "ParseRs1", "ParseRs2", "TranscriptV1", "TranscriptV2", "DecodeExpiry",
        "IsExpired", "OpenFrame", "Frame"]
p = pathlib.Path("formal/proofs/Proofs.lean"); t = p.read_text()
assert t.count("import Defs\n") == 1 and t.count("Empty until S06.") == 1
t = t.replace("import Defs\n", "import Defs\n" + "".join(
    f"import Proofs.Model.RequestStateWire.{m}\n" for m in mods))
t = t.replace("Empty until S06.", "Imports the `request_state_wire`\nproofs (S06, S10): `Common` and the 15 target modules.")
p.write_text(t)
q = pathlib.Path("formal/specs/Specs.lean"); u = q.read_text()
assert u.count("import Proofs\n") == 1 and u.count("Empty until S06.") == 1
u = u.replace("import Proofs\n", "import Proofs\nimport Specs.Model.RequestStateWire\n")
u = u.replace("Empty until S06.", "Spec files:\n`Specs.Model.RequestStateWire` (W01–W15, `frame_roundtrip`).")
q.write_text(u)
EOF
grep -c '^import Proofs.Model.RequestStateWire\.' formal/proofs/Proofs.lean
grep -n '^import' formal/specs/Specs.lean
```

## Step 3: remove the 16 statements from the draft and delete the emptied file

The draft holds exactly these 16 theorems and nothing else, so removing them empties it; the file
is deleted. Its signed-off text stays in git history: the statements at `adce319`, the exact
file at the prerequisite commit (`$WORK/signoff-commit`).

```bash
# Step 3 — delete the emptied draft
cd "$(git rev-parse --show-toplevel)"
D=formal/specs/Drafts/RequestStateWire.lean
WORK="${WORK:-/tmp/wbatch-incorporation}"
grep '^theorem ' "$D" | awk '{print $2}' | sort > "$WORK/draft-theorems.txt"
printf '%s\n' b64_len_spec key_length_ok_spec check_kid_len_spec bytes_eq_spec next_dot_spec \
  component_count_spec version_of_spec parse_rs1_spec parse_rs2_spec transcript_v1_spec \
  transcript_v2_spec decode_expiry_spec is_expired_spec open_frame_spec frame_spec \
  frame_roundtrip | sort | diff - "$WORK/draft-theorems.txt"
git rm -q "$D"
test ! -e "$D"
```

## Step 4: records W01–W15

For each of the 15 records in `formal/docs/functions/`: `proof: CHECKED` (the
`# proof staged: …` comment line is dropped), `theorem` (full name), `prover`
(`"AI: Claude Code, claude-opus-5-5"`), `axioms: [propext, Classical.choice, Quot.sound]` (the
`#print axioms` list in the spec file), `evidence` (adds `evidence/S06.md` for S06's IDs,
`evidence/S10.md` for S10's, and this file; the comment cites `adce319` and the prerequisite
commit), `generated_symbol` and `source_line` (the line of the `pub fn` at `adce319`, as in each
proof file's docstring). W15 notes that `frame_roundtrip` (not an ID) is proved in the same
file. The script stops if a record does not have the expected staged lines.

```bash
# Step 4 — records
cd "$(git rev-parse --show-toplevel)"
WORK="${WORK:-/tmp/wbatch-incorporation}"
C="$(cat "$WORK/signoff-commit")" python3 -I - <<'EOF'
import os, pathlib
C = os.environ["C"]
P = "rmcp.model.request_state_wire."
# id: (function, source line at adce319, evidence file)
T = {"W01": ("b64_len", 33, "S06"), "W02": ("key_length_ok", 39, "S06"),
     "W03": ("check_kid_len", 54, "S06"), "W04": ("bytes_eq", 65, "S06"),
     "W05": ("next_dot", 80, "S06"), "W06": ("component_count", 92, "S06"),
     "W07": ("version_of", 115, "S10"), "W08": ("parse_rs1", 137, "S10"),
     "W09": ("parse_rs2", 165, "S10"), "W10": ("transcript_v1", 183, "S10"),
     "W11": ("transcript_v2", 193, "S10"), "W12": ("decode_expiry", 205, "S06"),
     "W13": ("is_expired", 210, "S06"), "W14": ("open_frame", 225, "S06"),
     "W15": ("frame", 239, "S06")}
for i, (fn, line, ev) in T.items():
    p = pathlib.Path(f"formal/docs/functions/{i}.yaml")
    lines = p.read_text().split("\n")
    def sub(old_prefix, new):
        k = [j for j, l in enumerate(lines) if l.startswith(old_prefix)]
        assert len(k) == 1, (i, old_prefix)
        lines[k[0]] = new
    sub("source_line: null", f"source_line: {line}  # `pub fn {fn}` at adce319")
    sub("generated_symbol: null", f"generated_symbol: {P}{fn}")
    sub("proof: OPEN", "proof: CHECKED")
    staged = [j for j, l in enumerate(lines) if l.startswith("# proof staged:")]
    assert len(staged) == 1, i
    del lines[staged[0]]
    thm = f"theorem: {P}{fn}_spec"
    if i == "W15":
        thm += f"  # also {P}frame_roundtrip (not an ID), same proof and spec file"
    sub("theorem: null", thm)
    sub("axioms: []", "axioms: [propext, Classical.choice, Quot.sound]  "
        "# as printed by `#print axioms` in the spec file")
    sub("evidence: [formal/docs/evidence/S01.md, formal/docs/evidence/S05.md]",
        "evidence: [formal/docs/evidence/S01.md, formal/docs/evidence/S05.md, "
        f"formal/docs/evidence/{ev}.md, formal/docs/review/W-batch-incorporation.md]  "
        f"# S01 records; S05 spec drafts; {ev} proof; signed-off statement text: adce319 "
        f"(statements), {C} (exact draft file, deleted at incorporation)")
    sub("prover: null", 'prover: "AI: Claude Code, claude-opus-5-5"  '
        '# person, or "AI: <tool>, <model>"; not the AI spec drafter')
    p.write_text("\n".join(lines))
print("15 records updated")
EOF
test "$(grep -l '^proof: CHECKED$' formal/docs/functions/W*.yaml | wc -l | tr -d ' ')" -eq 15
if grep -n '^# proof staged' formal/docs/functions/W*.yaml; then exit 1; fi
```

## Step 5: board (human only)

`formal/docs/board.yaml`: S06 and S10 move to `ACCEPTED` only when the human decides; the human
sets `ACCEPTED` (`docs/WORKFLOW_AND_PR_GUIDE.md`, "Status Records and Evidence"). No agent and no
script edits these two states. In the same change the human (or the lead, on the human's
decision) updates the coverage lines of `formal/docs/STATUS.md`. No command.

## Step 6: the layering exception for `Mathlib.Tactic.Recall` (human decides)

`recall` is a Mathlib command that `Defs` and `Proofs` do not bring into scope, so something must
import `Mathlib.Tactic.Recall`. The layering tables (plan Section 5, "Lean libraries";
`docs/STYLE_GUIDE.md`, "Library layering") let `Specs` import only `Defs` and `Proofs`. Two
options; the human decides which:

- **Option A (simulated below):** `Specs` imports `Mathlib.Tactic.Recall` directly (as in the
  step 1 header). Both tables get the extra entry in the `Specs` row; the block below makes the
  edit.
- **Option B:** import `Mathlib.Tactic.Recall` in `formal/specs/Defs.lean` (`Defs` may already
  import Mathlib, so neither table changes) and drop the line `import Mathlib.Tactic.Recall` from
  the step 1 header. Then `Defs` (and so every statement and proof) carries a command that only
  the spec files use. The commands are in the `text` block after the option A block; they were
  not part of the literal run.

```bash
# Step 6 — option A: record the exception in both layering tables
cd "$(git rev-parse --show-toplevel)"
python3 -I - <<'EOF'
import pathlib
edits = {
  "docs/MCP_SDK_Verification_Master_Plan_EN.md":
    ("| `Specs` | `specs` | `Specs.*` | `Defs`, `Proofs` |",
     "| `Specs` | `specs` | `Specs.*` | `Defs`, `Proofs`, `Mathlib.Tactic.Recall` (the `recall` command) |"),
  "docs/STYLE_GUIDE.md":
    ("| `Specs` | `specs` | One spec file per Rust source file: `recall` of each accepted statement and its axioms | `Defs`, `Proofs` |",
     "| `Specs` | `specs` | One spec file per Rust source file: `recall` of each accepted statement and its axioms | `Defs`, `Proofs`, `Mathlib.Tactic.Recall` (the `recall` command) |"),
}
for f, (old, new) in edits.items():
    p = pathlib.Path(f); t = p.read_text()
    assert t.count(old) == 1, f
    p.write_text(t.replace(old, new))
print("layering tables updated")
EOF
grep -n 'Mathlib.Tactic.Recall' docs/MCP_SDK_Verification_Master_Plan_EN.md docs/STYLE_GUIDE.md
```

```text
# Step 6 — option B instead of option A (not run in the simulation)
# in formal/specs/Defs.lean, after its last import line:
import Mathlib.Tactic.Recall
# in formal/specs/Specs/Model/RequestStateWire.lean, delete the line:
import Mathlib.Tactic.Recall
```

## Step 7: the full guard, once

```bash
# Step 7 — full build and guard
cd "$(git rev-parse --show-toplevel)/formal"
set -o pipefail; lake build 2>&1 | tee .lake/build.log
cd ..
scripts/lean-guard.sh sources
scripts/lean-guard.sh build-log formal/.lake/build.log
scripts/lean-guard.sh axioms
```

All four must exit 0: the build log has only the four recorded Aeneas warnings, and the audit
reports no trusted or native-code assumption used by `Defs`/`Proofs`/`Specs`.

## Simulation record

Run on 2026-11-23 in a fresh scratch copy `/tmp/wbatch-sim/repo` of the repository working tree
(with `.git`; `target/`, `.llbc/`, `.aeneas/` left out; `formal/.lake` copied as APFS clones,
not linked), `WORK=/tmp/wbatch-sim/work`. A runner extracted every `bash` block of this file, in
order, and ran each one unchanged with `bash -e -o pipefail -c <block>` from the copy's root. The
prerequisite commit was made in the copy's own git history only (the repository's history is
unchanged).

| Step | Command | Exit | Result |
|---|---|---|---|
| P | `git add …; git commit …` (block "Step P") | 0 | commit `9f3832e` in the scratch history (pre-commit hook ran) |
| 0 | `python3 -I "$WORK/textid.py" "$PWD"` | 0 | `16/16 identical` |
| 0b | `"$G/scripts/lean-guard.sh" sources` on the copy with the staged file at its final path | 0 | 34 Lean files, no banned words or constructs |
| 1 | `git mv …`, header + staged body, `diff`, `grep -c` | 0 | body after `open Aeneas …` byte-identical to the staged one; 16 `recall`, 16 `#guard_msgs in` |
| 2 | `python3 -I -` (roots) | 0 | 16 `import Proofs.Model.RequestStateWire.*`; `import Specs.Model.RequestStateWire` |
| 3 | name list `diff`, `git rm -q` | 0 | the draft held exactly the 16 theorems; deleted |
| 4 | `python3 -I -` (records), `grep` checks | 0 | `15 records updated`; 15 × `proof: CHECKED`; no `# proof staged` line |
| 5 | (human; no command) | — | — |
| 6 | `python3 -I -` (option A tables) | 0 | `Specs` row of both tables lists `Mathlib.Tactic.Recall` |
| 7 | `lake build 2>&1 \| tee .lake/build.log` | 0 | `Build completed successfully (1726 jobs)`, 19.8 s for the whole block |
| 7 | `scripts/lean-guard.sh sources` | 0 | 34 Lean files, no banned words or constructs |
| 7 | `scripts/lean-guard.sh build-log formal/.lake/build.log` | 0 | only the recorded Aeneas warnings (4 lines) |
| 7 | `scripts/lean-guard.sh axioms` | 0 | 1044 constants in 26 project modules; kernel replay accepted; 0 trusted and 0 native-code assumptions used by `Defs`/`Proofs`/`Specs` |

Also checked in the copy afterwards: every line of the new spec file and of both roots is at most
100 characters, and the 15 records still parse as YAML.

Option B variant (same copy, after the run; not part of the literal run): `import
Mathlib.Tactic.Recall` added after the last import of `formal/specs/Defs.lean` and removed from
the spec file; `lake build` (1726 jobs), `sources`, `build-log` and `axioms` (1044 constants,
kernel replay accepted) all exit 0.

Negative check of step 0b (separate scratch copy `/tmp/wbatch/neg0b`): with the banned postulate
word written into one line of the staged docstring, step 0b exits 1 (`banned: … (outside
trusted/)` at the final path), while `lake env lean` of the staged file would not notice.
Negative check of the statement checks: see `evidence/S10.md` (one-token change gives `15/16`).
