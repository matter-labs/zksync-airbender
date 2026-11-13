#!/usr/bin/env bash
# Fetch the pinned lean-sail (the Lean library the generated Sail model needs) and apply our patches.
# lean-sail has no licence upstream, so it is NOT committed here: this script recreates it on demand.
#   sail/fetch-lean-sail.sh [dest]   # default dest: lean/sail-rv32/lean-sail (gitignored); no-op if already current
#   sail/fetch-lean-sail.sh --rev    # print the pinned commit
set -euo pipefail

LEANSAIL_REPO=https://github.com/rems-project/lean-sail.git
LEANSAIL_REV=c816ea7ad03cce98d51acee252540fd4215fede8   # tag v6 (2026-09-18), upstream toolchain v4.29.0

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
[[ "${1:-}" == "--rev" ]] && { echo "$LEANSAIL_REV"; exit 0; }
DEST="${1:-$HERE/../lean/sail-rv32/lean-sail}"
PATCHES=("$HERE"/patches/lean-sail-*.patch)

# stamp = pinned rev + hash of our patches: refetch only when either changes
stamp="$LEANSAIL_REV $(cat "${PATCHES[@]}" | git hash-object --stdin)"
[[ -f "$DEST/.fetched" && "$(cat "$DEST/.fetched")" == "$stamp" ]] && exit 0

echo ">> fetch lean-sail $LEANSAIL_REV -> $DEST" >&2
rm -rf "$DEST"; mkdir -p "$DEST"
git -C "$DEST" init -q
git -C "$DEST" remote add origin "$LEANSAIL_REPO"
git -C "$DEST" fetch -q --depth 1 origin "$LEANSAIL_REV"
git -C "$DEST" checkout -q FETCH_HEAD
[[ "$(git -C "$DEST" rev-parse HEAD)" == "$LEANSAIL_REV" ]] || { echo "lean-sail rev mismatch" >&2; exit 1; }
for p in "${PATCHES[@]}"; do
  echo ">> apply $(basename "$p")" >&2; git -C "$DEST" apply --whitespace=nowarn "$p"
done
rm -rf "$DEST/.git"
echo "$stamp" > "$DEST/.fetched"
