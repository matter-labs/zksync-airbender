#!/bin/sh
# Single-transaction proxy: build the two-tx and single-tx verifier projects and the proxy
# harness, run the proxy forge tests, then (unless --no-gas) measure the two-tx pair and the
# proxy transaction as raw anvil transactions (single_tx_gas.py; JSON written to <out.json>).
# Prereq: generated sources and calldata are current (`run_two_tx.sh` steps 1, or the
# generate_contracts / flatten_calldata ignored tests).
#
#   ./run_single_tx.sh 2p21 18546 gas.json   # full run on a task-owned port
#   ./run_single_tx.sh 2p21 --no-gas         # build + forge tests only
set -eu
SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
. "$SCRIPT_DIR/version.sh"
select_version "${1:?usage: run_single_tx.sh <2p21> <anvil-port|--no-gas> [out.json]}"
GAS_ARG=${2:?usage: run_single_tx.sh <2p21> <anvil-port|--no-gas> [out.json]}
cd "$CONTRACTS_ROOT"
for p in gkr gkr_negative whir two_tx single_tx/gkr single_tx/gkr_negative single_tx/whir \
  single_tx/f1/gkr single_tx/f1/gkr_negative single_tx/f1/gkr_wrong_setup_cap single_tx/f1/whir single_tx/instrumented/gkr_v0 \
  single_tx/instrumented/gkr_f1 single_tx/instrumented/whir_v0 single_tx/instrumented/whir_f1 \
  single_tx/harness; do
  ( cd "$p" && forge build >/dev/null )
done
( cd single_tx/harness && forge test -vv )
if [ "$GAS_ARG" != "--no-gas" ]; then
  python3 "$SCRIPT_DIR/single_tx_gas.py" "$AB_EVM_VERSION" "$GAS_ARG" "${3:?usage: run_single_tx.sh <2p21> <anvil-port> <out.json>}" "$DATA_ROOT"
fi
