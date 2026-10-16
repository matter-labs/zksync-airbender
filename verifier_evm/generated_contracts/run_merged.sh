#!/bin/sh
# Merged single-transaction verifiers of a version: build every generated project, run the
# Foundry suites (v0 and F1 positive/negative, F1 ↔ v0 oracle, EIP-170 size tests), then
# (unless --no-gas) the EIP-170 deployment gate and the raw-transaction gas on a task-owned anvil
# (merged_gas.py; JSON written to <out.json>). Prereq: generated sources and calldata are current
# (`cargo test -p verifier_evm --release --test generate_contracts -- --ignored` and
# `--test flatten_calldata -- --ignored`). Exits non-zero when any forge test failed.
#
#   ./run_merged.sh 2p21 18546 gas.json   # full run on a task-owned port
#   ./run_merged.sh 2p21 --no-gas         # build + forge tests only
set -eu
SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
. "$SCRIPT_DIR/version.sh"
select_version "${1:?usage: run_merged.sh <2p21> <anvil-port|--no-gas> [out.json]}"
GAS_ARG=${2:?usage: run_merged.sh <2p21> <anvil-port|--no-gas> [out.json]}
cd "$CONTRACTS_ROOT"
for p in merged merged_f1 negative/v0_wrong_final_pc negative/f1_wrong_final_pc \
  negative/f1_wrong_setup_cap instrumented/v0 instrumented/f1; do
  ( cd "$p" && forge build >/dev/null )
done
( cd merged_f1 && forge build --sizes | grep -E 'GkrWhirVerifier' ) || true
status=0
( cd merged && forge test -vv ) || status=$?
if [ "$GAS_ARG" != "--no-gas" ]; then
  python3 "$SCRIPT_DIR/merged_gas.py" "$AB_EVM_VERSION" "$GAS_ARG" "${3:?usage: run_merged.sh <2p21> <anvil-port> <out.json>}" "$DATA_ROOT"
fi
exit "$status"
