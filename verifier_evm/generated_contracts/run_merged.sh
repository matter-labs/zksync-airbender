#!/bin/sh
# Build the L1 wrap verifier and ignored controls after regenerating contracts and calldata.
set -eu
SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if [ "$#" -ne 0 ]; then
  echo "usage: run_merged.sh" >&2
  exit 1
fi
for mode in pessimistic_conjecture ethproofs_soundcalc; do
  (
    cd "$SCRIPT_DIR/$mode"
    for p in merged negative/wrong_final_pc negative/external_pow negative/batching_pow negative/query_pow_* negative/folding_pow_* negative/ood_pow_*; do
      ( cd "$p" && forge build >/dev/null )
    done
    cd merged
    forge test -vv
  )
done
