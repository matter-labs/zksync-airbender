#!/bin/sh
# Real per-transaction gas for the generated GKR + WHIR verifiers, measured with RAW anvil
# transactions (proof bytes are tx calldata, paid via intrinsic/EIP-7623 — never memory-copied,
# so no forge-harness over-count). Reads the compiled deployedBytecode from the sibling projects'
# out/ and the calldata from ../debug_data. Prereq: forge build in gkr/ and whir/, forge build in
# two_tx/ (or the two-tx test) for the registry artifact.
set -e
cd "$(dirname "$0")"
RPC=http://127.0.0.1:8545
KEY=0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
GKR=0x0000000000000000000000000000000061110001
WHIR=0x0000000000000000000000000000000011170001
REG=0x00000000000000000000000000000000CafE0001

gkr_code=$(jq -r '.deployedBytecode.object' gkr/out/GkrVerifier.sol/GKRVerifier.json)
whir_code=$(jq -r '.deployedBytecode.object' whir/out/WhirVerifier.sol/WhirVerifier.json)
reg_code=$(jq -r '.deployedBytecode.object' two_tx/out/GkrWhirRegistry.sol/GkrWhirRegistry.json)

echo "== deployed bytecode sizes =="
printf "  GKR  verifier : %d bytes\n" $(( (${#gkr_code} - 2) / 2 ))
printf "  WHIR verifier : %d bytes\n" $(( (${#whir_code} - 2) / 2 ))
printf "  Registry      : %d bytes\n" $(( (${#reg_code} - 2) / 2 ))

pkill -f "anvil.*8545" 2>/dev/null || true
anvil --hardfork prague --port 8545 --silent &
ANVIL=$!
trap 'kill $ANVIL 2>/dev/null' EXIT
until cast block-number --rpc-url $RPC >/dev/null 2>&1; do sleep 0.3; done

cast rpc anvil_setCode $GKR  "$gkr_code"  --rpc-url $RPC >/dev/null
cast rpc anvil_setCode $WHIR "$whir_code" --rpc-url $RPC >/dev/null
cast rpc anvil_setCode $REG  "$reg_code"  --rpc-url $RPC >/dev/null

gkr_cd="0x$(cat ../debug_data/gkr_full_calldata.hex)"
whir_cd="0x$(cat ../debug_data/proth120_whir_calldata_from_proof.hex)"

echo "== real per-transaction gas (anvil, Prague / EIP-7623) =="
run() {
  name=$1; addr=$2; cd=$3
  bytes=$(( (${#cd} - 2) / 2 ))
  out=$(cast send "$addr" "$cd" --private-key $KEY --rpc-url $RPC --json)
  used=$(printf '%s' "$out" | jq -r '.gasUsed')
  status=$(printf '%s' "$out" | jq -r '.status')
  printf "  %-4s : gasUsed = %s  (status %s, calldata %d bytes)\n" "$name" "$used" "$status" "$bytes"
}
run GKR  $GKR  "$gkr_cd"
run WHIR $WHIR "$whir_cd"
