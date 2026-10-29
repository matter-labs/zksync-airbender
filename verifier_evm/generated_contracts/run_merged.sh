#!/bin/sh
# Build and test the committed L1 wrap verifier projects after regenerating contracts and calldata.
set -eu
SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if [ "$#" -gt 1 ] || { [ "$#" -eq 1 ] && [ "$1" != "--no-gas" ]; }; then
  echo "usage: run_merged.sh [--no-gas]" >&2
  exit 1
fi
cd "$SCRIPT_DIR/l1_wrap_2p21"
for p in merged_f1 negative/f1_wrong_final_pc; do
  ( cd "$p" && forge build >/dev/null )
done
( cd merged_f1 && forge test -vv )
