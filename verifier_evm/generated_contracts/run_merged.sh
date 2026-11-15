#!/bin/sh
# Build and test the committed L1 wrap verifier projects after regenerating contracts and calldata.
set -eu
SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if [ "$#" -ne 0 ]; then
  echo "usage: run_merged.sh" >&2
  exit 1
fi
cd "$SCRIPT_DIR/l1_wrap"
for p in merged negative/wrong_final_pc; do
  ( cd "$p" && forge build >/dev/null )
done
( cd merged && forge test -vv )
