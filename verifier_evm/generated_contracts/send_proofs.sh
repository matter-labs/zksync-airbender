#!/bin/sh
# Send the two proof transactions (the GKR verification, then the WHIR verification) to
# already-deployed verifier contracts. The proof bytes are the transactions' calldata, read from
# ../debug_data (regenerate with `cargo test -p verifier_evm --test flatten_calldata` after a new
# proof). The verifier addresses come from OUTSIDE the script — arguments or environment — since
# they are a property of the deployment (see ./deploy.sh), not of this repository.
#
#   ./send_proofs.sh <gkr-address> <whir-address>
#   GKR_ADDR=0x… WHIR_ADDR=0x… ./send_proofs.sh
#
# Each verifier marks its committed state to the registry whose address is baked into its code;
# the two marks matching under the registry's rules is the on-chain GKR<->WHIR link.
set -e
cd "$(dirname "$0")"

# ---- configuration: edit for the target network ------------------------------------------------
RPC=http://127.0.0.1:8545
KEY=0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
# ------------------------------------------------------------------------------------------------

GKR_ADDR=${1:-$GKR_ADDR}
WHIR_ADDR=${2:-$WHIR_ADDR}
if [ -z "$GKR_ADDR" ] || [ -z "$WHIR_ADDR" ]; then
  echo "usage: $0 <gkr-address> <whir-address>   (or set GKR_ADDR / WHIR_ADDR)" >&2
  exit 1
fi

gkr_cd="0x$(cat ../debug_data/gkr_full_calldata.hex)"
whir_cd="0x$(cat ../debug_data/proth120_whir_calldata_from_proof.hex)"

send_proof() {
  name=$1; addr=$2; cd=$3
  bytes=$(( (${#cd} - 2) / 2 ))
  out=$(cast send "$addr" "$cd" --private-key $KEY --rpc-url $RPC --json)
  used=$(printf '%s' "$out" | jq -r '.gasUsed')
  status=$(printf '%s' "$out" | jq -r '.status')
  tx=$(printf '%s' "$out" | jq -r '.transactionHash')
  printf "  %-4s : gasUsed = %s  status = %s  calldata = %d bytes  tx = %s\n" \
    "$name" "$used" "$status" "$bytes" "$tx"
  if [ "$status" != "0x1" ] && [ "$status" != "1" ]; then
    echo "ERROR: $name verification transaction reverted" >&2
    exit 1
  fi
}

echo "== sending proof transactions =="
send_proof GKR  "$GKR_ADDR"  "$gkr_cd"
send_proof WHIR "$WHIR_ADDR" "$whir_cd"
echo "== both verification transactions succeeded =="
