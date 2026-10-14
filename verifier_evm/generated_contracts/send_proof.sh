#!/bin/sh
# Send the single verification transaction to an already-deployed GkrWhirVerifier. The proof
# bytes (GKR stream ‖ WHIR proof stream) are the transaction's calldata, read from ../debug_data
# (regenerate with `cargo test -p verifier_evm --test flatten_calldata` after a new proof). The
# verifier address comes from OUTSIDE the script — argument or environment — since it is a
# property of the deployment (see ./deploy.sh), not of this repository. A successful transaction
# (status 1) means the whole GKR+WHIR verification passed; the verifier emits
# `Verified(public_input, setup_commitment)`.
#
#   ./send_proof.sh <verifier-address>
#   VERIFIER_ADDR=0x… ./send_proof.sh
set -e
cd "$(dirname "$0")"

# ---- configuration: edit for the target network ------------------------------------------------
RPC=http://127.0.0.1:8545
KEY=0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
# ------------------------------------------------------------------------------------------------

VERIFIER_ADDR=${1:-$VERIFIER_ADDR}
if [ -z "$VERIFIER_ADDR" ]; then
  echo "usage: $0 <verifier-address>   (or set VERIFIER_ADDR)" >&2
  exit 1
fi

cd_hex="0x$(cat ../debug_data/merged_calldata.hex)"
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
