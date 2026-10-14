#!/bin/sh
# End-to-end: (re)generate the GKR + WHIR + Registry Solidity from the circuit artifact,
# regenerate the verifier calldata from the proof, compile each verifier in its own Foundry
# project (both via_ir now, but separate projects so each has its own optimizer_runs), run the
# two-transaction cross-check (GKR committed state == WHIR committed state), and report the
# compiler options, deployed bytecode sizes, and REAL per-tx gas (raw anvil txs, no harness
# memcopy over-count).
#
#   ./run_two_tx.sh 2p22 18545    # full run on a task-owned port
#   ./run_two_tx.sh 2p21 --no-gas # skip the anvil raw-tx gas step
set -eu
SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
. "$SCRIPT_DIR/version.sh"
select_version "${1:?usage: run_two_tx.sh <2p22|2p21> <anvil-port|--no-gas>}"
GAS_ARG=${2:?usage: run_two_tx.sh <2p22|2p21> <anvil-port|--no-gas>}
cd "$CONTRACTS_ROOT"

# 1. generate the verifier sources + the calldata (production Rust functions; no fixtures)
echo "== generating verifiers + calldata from the circuit artifact + proof =="
( cd "$SCRIPT_DIR/.." && cargo test -q -p verifier_evm --test generate_contracts -- --ignored >/dev/null )
( cd "$SCRIPT_DIR/.." && cargo test -q -p verifier_evm --test flatten_calldata >/dev/null )

# 2. compile each verifier in its own project (different backends), + the registry
echo "== compiling GKR (via_ir) / WHIR (via_ir) / Registry =="
( cd gkr    && forge build >/dev/null )
( cd whir   && forge build >/dev/null )
( cd two_tx && forge build >/dev/null )

# 3. two-transaction cross-check (deterministic; forge in-harness gas is over-counted)
echo "== two-transaction cross-check =="
( cd two_tx && forge test --match-contract GkrWhirTwoTxTest -vv )

# 4. compiler options actually used
echo "== compiler options =="
for p in gkr whir; do
  art=$(find "$p/out" -name '*Verifier.json' | head -1)
  ver=$(jq -r '.metadata.compiler.version' "$art")
  ir=$(jq -r '.metadata.settings.viaIR // false' "$art")
  opt=$(jq -r '.metadata.settings.optimizer | "optimizer=\(.enabled) runs=\(.runs)"' "$art")
  printf "  %-4s : solc %s  viaIR=%s  %s\n" "$(echo "$p" | tr a-z A-Z)" "$ver" "$ir" "$opt"
done

# 5. bytecode sizes + real per-tx gas (raw anvil transactions)
[ "$GAS_ARG" = "--no-gas" ] && exit 0
echo "== deployed bytecode sizes + real per-tx gas (Prague / EIP-7623) =="
"$SCRIPT_DIR/raw_tx_gas.sh" "$AB_EVM_VERSION" "$GAS_ARG"
