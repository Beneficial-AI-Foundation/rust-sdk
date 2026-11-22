# Path helpers for scripts/apply-patches.sh and scripts/aeneas-translate.sh (sourced, not run).
#
# check_llbc_dir ROOT LLBC SRC: refuses a work directory (RMCP_LLBC_DIR) that the scripts must
# not write into. They run `rsync --delete` into LLBC/work and `rm -rf` on LLBC/out and
# LLBC/cargo-home, so LLBC (canonicalised: symlinks, `.`, `..`) must not be `/`, $HOME, the
# repository, or contain any of them; must not contain the source workspace SRC or lie in it
# (except SRC/.llbc, which the copy skips); and, if it exists, must be empty, the repository's
# own `.llbc` (git-ignored, written only by these scripts), or hold the marker file
# `.rmcp-llbc-dir` that this function writes into every directory it accepts. Its fixed
# subdirectories work/, out/, cargo-home/, target/ must not be symlinks.

# Canonical form of a path that may not exist yet: the longest existing prefix with
# symlinks resolved (pwd -P), then the remaining components with `.` and `..` resolved
# lexically (they do not exist, so they are not symlinks). Nothing is created.
canon_path() {
  local p="$1" rest="" comp out
  [[ "$p" == /* ]] || p="$PWD/$p"
  while [[ ! -d "$p" ]]; do
    rest="$(basename "$p")${rest:+/$rest}"
    p="$(dirname "$p")"
  done
  out="$(cd "$p" && pwd -P)"
  local IFS=/
  for comp in $rest; do
    case "$comp" in
      ""|.) ;;
      ..) out="$(dirname "$out")" ;;
      *) out="${out%/}/$comp" ;;
    esac
  done
  printf '%s\n' "$out"
}

# within A B: A equals B or lies under it (every path lies under /).
within() { [[ "$2" == "/" || "$1" == "$2" || "$1" == "$2"/* ]]; }

LLBC_MARKER=".rmcp-llbc-dir"

# check_llbc_dir ROOT LLBC SRC; on success prints the canonical LLBC and writes the marker.
check_llbc_dir() {
  local root_c llbc_c src_c home_c sub first
  root_c="$(canon_path "$1")"
  llbc_c="$(canon_path "$2")"
  src_c="$(canon_path "$3")"
  [[ "$llbc_c" != "/" ]] || { echo "RMCP_LLBC_DIR is /" >&2; return 1; }
  if [[ -n "${HOME:-}" ]]; then
    home_c="$(canon_path "$HOME")"
    ! within "$home_c" "$llbc_c" || { echo "RMCP_LLBC_DIR ($llbc_c) is or contains \$HOME ($home_c)" >&2; return 1; }
  fi
  ! within "$root_c" "$llbc_c" || { echo "RMCP_LLBC_DIR ($llbc_c) is or contains the repository ($root_c)" >&2; return 1; }
  ! within "$src_c" "$llbc_c" || { echo "RMCP_LLBC_DIR ($llbc_c) is or contains the source workspace ($src_c)" >&2; return 1; }
  if within "$llbc_c" "$src_c" && [[ "$llbc_c" != "$src_c/.llbc" && "$llbc_c" != "$src_c/.llbc/"* ]]; then
    echo "RMCP_LLBC_DIR ($llbc_c) lies inside the source workspace ($src_c) but not in its .llbc/" >&2
    return 1
  fi
  if [[ -e "$llbc_c" || -L "$llbc_c" ]]; then
    [[ -d "$llbc_c" ]] || { echo "RMCP_LLBC_DIR ($llbc_c) is not a directory" >&2; return 1; }
    if [[ ! -f "$llbc_c/$LLBC_MARKER" && "$llbc_c" != "$root_c/.llbc" ]]; then
      first="$(find "$llbc_c" -mindepth 1 -maxdepth 1 -print -quit)"
      [[ -z "$first" ]] || {
        echo "RMCP_LLBC_DIR ($llbc_c) exists, is not empty and has no $LLBC_MARKER (it was not created by these scripts): $first" >&2
        return 1
      }
    fi
    for sub in work out cargo-home target; do
      [[ ! -L "$llbc_c/$sub" ]] || { echo "$llbc_c/$sub is a symlink" >&2; return 1; }
    done
  fi
  mkdir -p "$llbc_c"
  : > "$llbc_c/$LLBC_MARKER"
  printf '%s\n' "$llbc_c"
}
