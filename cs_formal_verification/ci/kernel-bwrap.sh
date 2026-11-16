#!/usr/bin/env bash
# Keep Lake's sandbox and expose the pinned circuit inputs outside the Lean package as read-only data.
set -euo pipefail

compiled="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../cs/compiled_circuits" && pwd)"
bwrap="$(command -v bwrap)"
arguments=()
exporting=false
while (( $# )) && [[ "$1" != -- ]]; do
  if (( $# >= 3 )) && [[ "$1" == --setenv && "$2" == LAKE_CHECK_EXPORT && "$3" == 1 ]]; then
    exporting=true
  fi
  arguments+=("$1")
  shift
done
if (( $# == 0 )); then
  echo "The sandbox command must follow --." >&2
  exit 2
fi
shift
if [[ "$exporting" == true && -n "${KERNEL_EXPORT_PATH:-}" ]]; then
  # Publish only a complete sandbox export. Stdout still goes to Lake's own audit.
  partial="${KERNEL_EXPORT_PATH}.part"
  trap 'rm -f -- "$partial"' EXIT
  "$bwrap" "${arguments[@]}" --ro-bind "$compiled" "$compiled" -- "$@" | tee "$partial"
  mv -- "$partial" "$KERNEL_EXPORT_PATH"
  exit 0
fi
exec "$bwrap" "${arguments[@]}" --ro-bind "$compiled" "$compiled" -- "$@"
