#!/usr/bin/env bash
# Linkage check for the Phase 2 targets (docs/MCP_SDK_Verification_Master_Plan_EN.md, Section 19).
#
# What it shows, in two parts:
#  (a) The SDK source is upstream (origin/main 7caec76), checked on the committed tree (HEAD):
#      the tree of crates/rmcp/src is PINNED_SRC_TREE; every other tracked file under crates/
#      plus the root Cargo.toml (mode, blob id, path) hashes to PINNED_CRATES_DIGEST, leaving out
#      only crates/rmcp/Cargo.toml; and that manifest, with its [package.metadata.charon] table
#      removed, hashes to PINNED_MANIFEST_DIGEST (so no [lib] path, feature or dependency differs
#      from upstream). The working tree has no change, deletion, untracked, skip-worktree or
#      assume-unchanged file under crates/, Cargo.toml or formal/translation/.
#  (b) The translation does not depend on any translation patch: translated from that source with
#      NO patch applied, every block of Funs.lean, Types.lean and the two External templates equals
#      a block of the committed formal/translation/, up to the `Source: '…', lines …` docstring
#      field (patch 01 shifts the line numbers of model.rs by two), with every block holding at
#      most one declaration.
# A Phase 2 record may say `linkage: ORIGINAL` only while this passes on its commit. Not covered
# (stated in plan Section 19): a patch that changes the BODY of an `opaque` SDK item reached by a
# Phase 2 target is invisible to any comparison of translations (only its signature is
# translated); the script therefore requires the SDK-side opaque list to be exactly
# rmcp::transport::auth::AuthorizationManager (a type with no body; SDK_OPAQUE below), no SDK item
# excluded, and no unmodified-source External template citing crates/rmcp/src (the SDK_OPAQUE
# test only sees entries starting with `rmcp::`; an impl-first pattern such as `{impl … for
# rmcp::…}` is caught by the template check instead, S23 review 2026-11-24); a committed-only
# (patched) declaration that could shadow a name used in a Phase 2 block also fails. Not pinned:
# dependency resolution beyond PINNED_DEPS (workspace members outside crates/ take part in it;
# both sides of the comparison share it, and the stale-translation check requires a clean tree).
#
# How: copy the tracked files into <scratch-dir>/src, rewrite only the copy's
# [package.metadata.charon] (drop the Phase 1 start points rmcp::model::request_state{,_wire},
# which exist only with patch 01; drop the opaque function entries ...::request_state_wire::prim
# and ...::request_state::_::now_ms; keep the other exclude entries outside
# rmcp::model::request_state*; keep hide_marker_traits), then run scripts/aeneas-translate.sh on
# that copy with RMCP_NO_PATCHES=1 and RMCP_TARGET_SET=phase2 into <scratch-dir>/out, so every
# toolchain, environment, dependency, glob and target check of the real translation applies.
#
# Usage: scripts/check-original-linkage.sh <scratch-dir>
#   <scratch-dir>  outside the repository; new, empty, or an earlier run's (marker
#                  .rmcp-linkage-dir). src/ and out/ are replaced; llbc/ is the translate
#                  script's work directory (its work/, out/ and cargo-home/ are replaced by it,
#                  target/ is kept as a build cache).
# Writes only inside <scratch-dir>.
set -euo pipefail

# Tree id of crates/rmcp/src at upstream origin/main 7caec762799bece6fba38e4298b8ca7db8bac12c
# (`git rev-parse 7caec76:crates/rmcp/src`). Changing the pinned commit changes this value.
PINNED_SRC_TREE="4efe696aeae5f3c4ba89a3c83145a93f901feaa2"
# sha256 of the `git ls-tree -r <rev> -- crates Cargo.toml` lines without crates/rmcp/Cargo.toml
# (203 lines at 7caec76), and sha256 of crates/rmcp/Cargo.toml parsed with tomllib, its
# [package.metadata.charon] table removed, serialised with json.dumps(sort_keys=True); both equal
# at 7caec76 and at the S22 commit. Stored here because CI checks out at depth 1.
PINNED_CRATES_DIGEST="0be33db37cc195f951ca4c2095ffe5091edcb24de7aeef8bfb6f998914706c84"
PINNED_MANIFEST_DIGEST="75e978b5c8d0e0e549cdff137a2db03de4464ef58f047b213ef2d8af866ecb4e"

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
log() { printf '[linkage] %s\n' "$*"; }
die() { printf '[linkage] error: %s\n' "$*" >&2; exit 1; }

[[ $# -eq 1 ]] || die "usage: $0 <scratch-dir>"
# shellcheck source=scripts/llbc-dir-guard.sh
source "$ROOT/scripts/llbc-dir-guard.sh"   # canon_path, within

# Scratch directory guard (its own, not check_llbc_dir; <scratch-dir>/llbc goes through that one
# inside aeneas-translate.sh). The path is checked before anything is created.
base="$(basename "$1")"
[[ -n "$base" && "$base" != "." && "$base" != ".." && "$base" != "/" ]] \
  || die "refused scratch directory $1 (its last component must be a plain name)"
parent="$(dirname "$1")"
[[ -d "$parent" ]] || die "the parent of the scratch directory ($parent) does not exist"
SCR="$(canon_path "$parent")/$(basename "$1")"
[[ ! -L "$SCR" ]] || SCR="$(canon_path "$SCR")"
ROOT_C="$(canon_path "$ROOT")"
within "$SCR" "$ROOT_C" && die "the scratch directory ($SCR) must lie outside the repository"
within "$ROOT_C" "$SCR" && die "the scratch directory ($SCR) contains the repository"
HOME_C="$(canon_path "$HOME")"
[[ "$SCR" != "/" ]] && ! within "$HOME_C" "$SCR" || die "refused scratch directory $SCR (/, \$HOME or an ancestor)"
if [[ -e "$SCR" ]]; then
  [[ -d "$SCR" ]] || die "$SCR exists and is not a directory"
  if [[ -n "$(ls -A "$SCR")" && ! -f "$SCR/.rmcp-linkage-dir" ]]; then
    die "$SCR is not empty and has no marker .rmcp-linkage-dir from an earlier run"
  fi
fi
mkdir -p "$SCR"
touch "$SCR/.rmcp-linkage-dir"
for d in src out; do
  [[ ! -L "$SCR/$d" ]] || die "$SCR/$d is a symlink"
  rm -rf "${SCR:?}/$d"
done

# (a) The SDK source is the pinned upstream tree, unchanged in the working tree.
got_tree="$(git -C "$ROOT" rev-parse HEAD:crates/rmcp/src)" || die "git rev-parse failed"
[[ "$got_tree" == "$PINNED_SRC_TREE" ]] \
  || die "crates/rmcp/src at HEAD is tree $got_tree, not the pinned upstream tree $PINNED_SRC_TREE (7caec76)"
digests="$(cd "$ROOT" && python3 -I -c '
import hashlib, json, subprocess, tomllib
out = subprocess.run(["git", "ls-tree", "-r", "HEAD", "--", "crates", "Cargo.toml"],
                     capture_output=True, text=True, check=True).stdout
lines = [l for l in out.splitlines() if l.split("\t", 1)[1] != "crates/rmcp/Cargo.toml"]
print(hashlib.sha256(("\n".join(lines) + "\n").encode()).hexdigest())
man = subprocess.run(["git", "show", "HEAD:crates/rmcp/Cargo.toml"],
                     capture_output=True, text=True, check=True).stdout
d = tomllib.loads(man)
d.get("package", {}).get("metadata", {}).pop("charon", None)
print(hashlib.sha256(json.dumps(d, sort_keys=True).encode()).hexdigest())
')" || die "computing the source digests failed"
read -r got_crates got_manifest <<<"$(tr '\n' ' ' <<<"$digests")"
[[ "$got_crates" == "$PINNED_CRATES_DIGEST" ]] \
  || die "the tracked files under crates/ and Cargo.toml (without crates/rmcp/Cargo.toml) differ from upstream 7caec76 (digest $got_crates)"
[[ "$got_manifest" == "$PINNED_MANIFEST_DIGEST" ]] \
  || die "crates/rmcp/Cargo.toml outside [package.metadata.charon] differs from upstream 7caec76 (digest $got_manifest)"
dirty="$(git -C "$ROOT" status --porcelain --untracked-files=all -- crates Cargo.toml formal/translation)"
[[ -z "$dirty" ]] || { printf '%s\n' "$dirty" >&2; die "uncommitted, deleted or untracked files under crates/, Cargo.toml or formal/translation/"; }
hidden="$(git -C "$ROOT" ls-files -v -- crates Cargo.toml formal/translation | grep -E '^([a-z]|S) ' || true)"
[[ -z "$hidden" ]] || { printf '%s\n' "$hidden" >&2; die "skip-worktree or assume-unchanged files under crates/, Cargo.toml or formal/translation/"; }
log "source is upstream 7caec76 (src tree $PINNED_SRC_TREE, crates digest and manifest digest pinned); working tree clean"

# 1. The tracked files of the repository (formal/ is not needed for the translation).
command -v rsync >/dev/null || die "rsync not found"
git -C "$ROOT" ls-files -z -- . ':!:formal' | rsync -a --from0 --files-from=- "$ROOT/" "$SCR/src/" \
  || die "copying the tracked files failed (a tracked file missing from the working tree?)"
log "copied the tracked files of $ROOT (without formal/) to $SCR/src"

# 2. Rewrite the copy's [package.metadata.charon].
python3 -I - "$SCR/src/crates/rmcp/Cargo.toml" <<'PY'
import json, re, sys, tomllib
path = sys.argv[1]
text = open(path, encoding="utf-8").read()
meta = tomllib.loads(text)["package"]["metadata"]["charon"]
unknown = set(meta) - {"start_from", "exclude", "opaque", "hide_marker_traits"}
if unknown:
    sys.exit(f"[package.metadata.charon] has keys the rewrite does not handle: {sorted(unknown)}")
phase1 = {"rmcp::model::request_state", "rmcp::model::request_state_wire"}
if not phase1 <= set(meta["start_from"]):
    sys.exit("start_from lacks the Phase 1 modules rmcp::model::request_state{,_wire}")
start = [s for s in meta["start_from"] if s not in phase1]
if not start:
    sys.exit("start_from has no Phase 2 entries")
opaque = [o for o in meta["opaque"] if o not in (
    "rmcp::model::request_state_wire::prim", "rmcp::model::request_state::_::now_ms")]
exclude = [e for e in meta["exclude"] if not e.startswith("rmcp::model::request_state")]
hide = meta.get("hide_marker_traits", False)
def arr(xs):
    return "[\n" + "".join(f"  {json.dumps(x)},\n" for x in xs) + "]"
block = ("[package.metadata.charon]\n"
         "# Rewritten by scripts/check-original-linkage.sh (unmodified source, Phase 2 only).\n"
         f"start_from = {arr(start)}\nhide_marker_traits = {'true' if hide else 'false'}\n"
         f"exclude = {arr(exclude)}\nopaque = {arr(opaque)}\n")
m = re.search(r"^\[package\.metadata\.charon\]\n.*?(?=^\[)", text, re.S | re.M)
if not m:
    sys.exit("no [package.metadata.charon] table followed by another table")
new = text[:m.start()] + block + "\n" + text[m.end():]
# The SDK-side settings the Phase 2 translation was reviewed with (plan Section 19): the only
# opaque SDK item is the type AuthorizationManager (no body), nothing of the SDK is excluded,
# marker traits hidden. Any change needs the affected records reassessed (a new opaque or
# excluded SDK item hides its body from this check) and an edit of this list in a reviewed PR.
SDK_OPAQUE = ["rmcp::transport::auth::AuthorizationManager"]
if [o for o in opaque if o.startswith("rmcp::")] != SDK_OPAQUE or exclude != ["serde", "serde_core"] \
        or hide is not True:
    sys.exit(f"[package.metadata.charon] SDK-side settings differ from the reviewed ones "
             f"(opaque SDK items {[o for o in opaque if o.startswith('rmcp::')]}, exclude {exclude}, "
             f"hide_marker_traits {hide}); reassess the Phase 2 records (plan Section 19) and update "
             "SDK_OPAQUE in scripts/check-original-linkage.sh in a reviewed PR")
check = tomllib.loads(new)["package"]["metadata"]["charon"]   # the rewrite must parse back
assert (check["start_from"] == start and check["opaque"] == opaque and check["exclude"] == exclude
        and check["hide_marker_traits"] == hide)
open(path, "w", encoding="utf-8").write(new)
print(f"[linkage] start_from: {len(start)} Phase 2 entries; exclude: {exclude}; "
      f"opaque: {len(opaque)} entries; hide_marker_traits = {hide}")
PY

# 3. Translate the unmodified copy with the real translation script.
log "translating the unmodified source (RMCP_NO_PATCHES=1, RMCP_TARGET_SET=phase2)"
RMCP_SOURCE_ROOT="$SCR/src" RMCP_LLBC_DIR="$SCR/llbc" RMCP_TRANSLATION_DEST="$SCR/out" \
  RMCP_NO_PATCHES=1 RMCP_TARGET_SET=phase2 "$ROOT/scripts/aeneas-translate.sh" \
  || die "translation of the unmodified source failed"

# 4. Compare with the committed translation. The two External templates are git-ignored files of
# formal/translation/Rmcp/ written by aeneas-translate.sh (in CI by the regeneration step just
# before; locally by the last run).
python3 -I - "$SCR/out/Rmcp" "$ROOT/formal/translation/Rmcp" <<'PY'
import os, re, sys
scratch, committed = sys.argv[1:]
src = re.compile(r"Source: '([^']*)', lines [0-9:-]+")
macro_src = re.compile(r"macro invocation at: '([^']*)', lines [0-9:-]+")
ALLOWED_SRC = ("crates/rmcp/src/", "/rustc/", "/cargo/registry/")
head = re.compile(r"^(?:@\[.*?\]\s*)*(?:noncomputable |private |partial |unsafe )*"
                  r"(def|theorem|axiom|opaque|structure|inductive|class|instance|abbrev|impl_def)\b\s*(\S*)",
                  re.M | re.S)
HEADER = re.compile(r"^(--|/-|module$|import |public import |@\[expose\] public section$|open |set_option |namespace |end |noncomputable section|section)")
def blocks(path):
    raw = open(path, encoding="utf-8").read()
    # Aeneas >= nightly-2026.11.24 adds "this code is generated from a macro invocation at: '…',
    # lines …" to the Source field; its line numbers shift with patch 01 like the Source lines.
    norm = macro_src.sub("macro invocation at: <normalised>", src.sub("Source: <normalised>", raw))
    return raw, [b for b in norm.split("\n\n") if b.strip()]
def heads(b):
    return [h[1] or "?" for h in head.findall(b)]
FILES = ("Funs.lean", "Types.lean", "FunsExternal_Template.lean", "TypesExternal_Template.lean")
all_theirs, all_mine = set(), set()
for fname in FILES:
    for d, acc in ((committed, all_theirs), (scratch, all_mine)):
        p = os.path.join(d, fname)
        if os.path.exists(p):
            for b in blocks(p)[1]:
                acc.update(heads(b))
EXTRA = all_theirs - all_mine   # declared only in the committed (patched) translation, any file
bad = 0
for fname in FILES:
    mine_path, theirs_path = os.path.join(scratch, fname), os.path.join(committed, fname)
    for p in (mine_path, theirs_path):
        if not os.path.exists(p):
            sys.exit(f"[linkage] error: {p} missing (the templates: run scripts/aeneas-translate.sh first)")
    raw, mine = blocks(mine_path)
    for path in src.findall(raw) + macro_src.findall(raw):   # both cited paths (N13)
        if "Template" in fname and path.startswith("crates/rmcp/src/"):
            sys.exit(f"[linkage] error: {fname} of the unmodified source declares an SDK item as "
                     f"external ({path!r}): its body is hidden from this check; reassess the Phase 2 "
                     "records (plan Section 19)")
        if not path.startswith(ALLOWED_SRC):
            sys.exit(f"[linkage] error: {fname} of the unmodified source cites the source path {path!r}, "
                     f"outside {ALLOWED_SRC}")
    _, theirs = blocks(theirs_path)
    have, names = set(theirs), set()
    for b in theirs:
        names.update(heads(b))
    extra = EXTRA
    # Lean resolves an identifier inside `def a.b.c.f` against the namespaces a.b.c, a.b, a and
    # the root: a committed-only declaration named <prefix>.<identifier> could change what an
    # unmodified block means while its text stays the same (plan Section 19). Fail on any such
    # candidate (token-based, so conservative).
    for b in mine:
        hs = heads(b)
        if not hs:
            continue
        parts = hs[0].split(".")
        prefixes = [".".join(parts[:k]) for k in range(len(parts) - 1, 0, -1)] + [""]
        for tok in set(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", b)):
            segs = tok.split(".")
            # an identifier a.b.c can resolve to a declaration named <pre>.a, <pre>.a.b or
            # <pre>.a.b.c (a shorter one followed by field access), for each enclosing namespace
            for k in range(1, len(segs) + 1):
                for pre in prefixes:
                    cand = ".".join(([pre] if pre else []) + segs[:k])
                    if cand in extra:
                        sys.exit(f"[linkage] error: in {fname}, `{tok}` in {hs[0]} may resolve to the "
                                 f"committed-only declaration `{cand}` (name shadowing by patched "
                                 "code; plan Section 19)")
    same = 0
    for b in mine:
        hs = heads(b)
        if len(hs) > 1:
            sys.exit(f"[linkage] error: a block of the unmodified-source {fname} holds {len(hs)} "
                     f"declarations ({', '.join(hs)}); the comparison needs one per block")
        if not hs and not all(HEADER.match(l) or not l.strip() for l in b.splitlines()):
            sys.exit(f"[linkage] error: a block of the unmodified-source {fname} has no declaration "
                     f"and is not a header or footer: {b.splitlines()[0][:100]!r}")
        if b in have:
            same += 1
            continue
        bad += 1
        n = hs[0] if hs else b.splitlines()[0][:100]
        print(f"[linkage] {'DIFFERS' if hs and n in names else 'MISSING'} in committed {fname}: {n}")
    print(f"[linkage] {fname}: {len(mine)} blocks from the unmodified source, {same} identical")
if bad:
    sys.exit(f"[linkage] error: {bad} block(s) of the unmodified-source translation differ or are "
             "missing; the Phase 2 linkage is not ORIGINAL (plan Section 19)")
print("[linkage] OK: the Phase 2 translation does not depend on any translation patch")
PY
