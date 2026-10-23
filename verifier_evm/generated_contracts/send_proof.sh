#!/bin/sh
# Send the single verification transaction to an already-deployed v0 GkrWhirVerifier. The proof
# bytes (GKR stream ‖ WHIR proof stream) are the transaction's calldata, read from the version's
# debug_data (regenerate with `cargo test -p verifier_evm --release --test flatten_calldata --
# --ignored` after a new proof). The
# verifier address comes from OUTSIDE the script — argument or environment — since it is a
# property of the deployment (see ./deploy.sh), not of this repository. A successful transaction
# (status 1) means the whole GKR+WHIR verification passed and the verifier reported
# `(publicInput, auxInput, setupCommitment)` to its registry (`markVerified`); the same tuple is
# the call's return data.
#
#   ./send_proof.sh <2p21> <verifier-address>
#   VERIFIER_ADDR=0x… ./send_proof.sh <2p21>
set -eu
SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
. "$SCRIPT_DIR/version.sh"
select_version "${1:?usage: send_proof.sh <2p21> <verifier-address>}"

# ---- configuration: edit for the target network ------------------------------------------------
RPC=http://127.0.0.1:8545
KEY=0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
# ------------------------------------------------------------------------------------------------

VERIFIER_ADDR=${2:-${VERIFIER_ADDR:-}}
if [ -z "$VERIFIER_ADDR" ]; then
  echo "usage: $0 <2p21> <verifier-address>   (or set VERIFIER_ADDR)" >&2
  exit 1
fi

cd_hex="0x$(cat "$DATA_ROOT/merged_calldata.hex")"
bytes=$(( (${#cd_hex} - 2) / 2 ))

echo "== sending the verification transaction =="
out=$(cast send "$VERIFIER_ADDR" "$cd_hex" --private-key $KEY --rpc-url $RPC --json)
used=$(printf '%s' "$out" | jq -r '.gasUsed')
status=$(printf '%s' "$out" | jq -r '.status')
tx=$(printf '%s' "$out" | jq -r '.transactionHash')
printf "  gasUsed = %s  status = %s  calldata = %d bytes  tx = %s\n" "$used" "$status" "$bytes" "$tx"
if [ "$status" != "0x1" ] && [ "$status" != "1" ]; then
  echo "ERROR: verification transaction reverted" >&2
  exit 1
fi
echo "== verification transaction succeeded =="
