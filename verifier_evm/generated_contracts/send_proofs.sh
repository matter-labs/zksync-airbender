#!/bin/sh
# Send the two proof transactions (the GKR verification, then the WHIR verification) to
# already-deployed verifier contracts. The proof bytes are the transactions' calldata, read from
# the versioned data root (regenerate with `cargo test -p verifier_evm --test flatten_calldata -- --ignored` after a new
# proof). The verifier addresses come from OUTSIDE the script — arguments or environment — since
# they are a property of the deployment (see ./deploy.sh), not of this repository.
#
#   ./send_proofs.sh <2p21> <gkr-address> <whir-address>
#   GKR_ADDR=0x… WHIR_ADDR=0x… ./send_proofs.sh <2p21>
#
# Each verifier marks its committed state to the registry whose address is baked into its code;
# the two marks matching under the registry's rules is the on-chain GKR<->WHIR link.
set -eu
SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
. "$SCRIPT_DIR/version.sh"
select_version "${1:?usage: send_proofs.sh <2p21> <gkr-address> <whir-address>}"
shift

# ---- configuration: edit for the target network ------------------------------------------------
RPC=${RPC:-http://127.0.0.1:8545}
KEY=${KEY:-0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80}
# ------------------------------------------------------------------------------------------------

GKR_ADDR=${1:-${GKR_ADDR:-}}
WHIR_ADDR=${2:-${WHIR_ADDR:-}}
if [ -z "$GKR_ADDR" ] || [ -z "$WHIR_ADDR" ]; then
  echo "usage: $0 <2p21> <gkr-address> <whir-address>   (or set GKR_ADDR / WHIR_ADDR)" >&2
  exit 1
fi

# Foundry reads both payloads from disk and signs/broadcasts the transactions.
# The WHIR hex string is larger than Linux's single-argument limit.
echo "== sending proof transactions =="
GKR_ADDR="$GKR_ADDR" WHIR_ADDR="$WHIR_ADDR" PROOF_SENDER_KEY="$KEY" \
GKR_CALLDATA_PATH="$DATA_ROOT/gkr_full_calldata.hex" \
WHIR_CALLDATA_PATH="$DATA_ROOT/proth120_whir_calldata_from_proof.hex" \
  forge script --root "$SCRIPT_DIR/sender" "$SCRIPT_DIR/sender/script/SendProofs.s.sol:SendProofs" \
    --rpc-url "$RPC" --broadcast --slow
echo "== both verification transactions succeeded =="
