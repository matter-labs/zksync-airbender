#!/bin/sh
# Real gas of the single verification transaction, measured with a RAW anvil transaction (the
# proof bytes are the tx calldata, paid via intrinsic/EIP-7623 — never memory-copied, so no
# forge-harness over-count). Reads the compiled deployedBytecode from merged/out/ and the calldata
# from ../debug_data. Prereq: `forge build` in merged/.
set -e
cd "$(dirname "$0")"
RPC=http://127.0.0.1:8545
KEY=0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
VERIFIER=0x00000000000000000000000000000000611B0001

code=$(jq -r '.deployedBytecode.object' merged/out/GkrWhirVerifier.sol/GkrWhirVerifier.json)

echo "== deployed bytecode size =="
printf "  GkrWhirVerifier : %d bytes\n" $(( (${#code} - 2) / 2 ))

pkill -f "anvil.*8545" 2>/dev/null || true
anvil --hardfork prague --port 8545 --silent &
ANVIL=$!
trap 'kill $ANVIL 2>/dev/null' EXIT
until cast block-number --rpc-url $RPC >/dev/null 2>&1; do sleep 0.3; done

cast rpc anvil_setCode $VERIFIER "$code" --rpc-url $RPC >/dev/null

cd_hex="0x$(cat ../debug_data/merged_calldata.hex)"
bytes=$(( (${#cd_hex} - 2) / 2 ))

echo "== real transaction gas (anvil, Prague / EIP-7623) =="
out=$(cast send "$VERIFIER" "$cd_hex" --private-key $KEY --rpc-url $RPC --json)
used=$(printf '%s' "$out" | jq -r '.gasUsed')
status=$(printf '%s' "$out" | jq -r '.status')
printf "  verifier : gasUsed = %s  (status %s, calldata %d bytes)\n" "$used" "$status" "$bytes"
