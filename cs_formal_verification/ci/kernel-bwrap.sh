#!/usr/bin/env bash
# Keep Lake's sandbox and expose the pinned circuit inputs outside the Lean package as read-only data.
set -euo pipefail

compiled="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../cs/compiled_circuits" && pwd)"
bwrap="$(command -v bwrap)"
arguments=()
while (( $# )) && [[ "$1" != -- ]]; do
  arguments+=("$1")
  shift
done
if (( $# == 0 )); then
  echo "The sandbox command must follow --." >&2
  exit 2
fi
shift
exec "$bwrap" "${arguments[@]}" --ro-bind "$compiled" "$compiled" -- "$@"
