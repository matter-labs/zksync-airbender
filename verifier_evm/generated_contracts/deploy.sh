#!/bin/sh
# Deterministic deployment of the merged GkrWhirVerifier through the CreateX factory
# (https://github.com/pcaversaccio/createx, pre-deployed on most networks at the fixed address
# below) via `ICreateX.deployCreate2(bytes32 salt, bytes initCode)`, so the address is a pure
# function of (factory, salt, initCode). The verifier is stateless and self-contained (it emits
# `Verified(public_input, setup_commitment)` on success) — there is no registry and nothing to
# initialize, so deployment is a single step: build, deploy, print the created address (from the
# factory's ContractCreation event).
#
# CREATE2 reverts on an address collision — bump SALT to deploy a fresh verifier.
# Feed the printed address to ./send_proof.sh afterwards.
set -e
cd "$(dirname "$0")"

# ---- configuration: edit for the target network ------------------------------------------------
RPC=http://127.0.0.1:8545
KEY=0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
# First 20 bytes zero + 21st byte zero = CreateX's unpermissioned, non-redeploy-protected salt
# flavor (anyone can reproduce the address).
SALT=0x00000000000000000000000000000000000000000000000000616972621b0001
# ------------------------------------------------------------------------------------------------

CREATEX=0xba5Ed099633D3B313e4D5F7bdc1305d3c28ba5Ed

factory_code=$(cast code $CREATEX --rpc-url $RPC)
if [ "$factory_code" = "0x" ]; then
  echo "ERROR: no CreateX factory code at $CREATEX on this RPC." >&2
  echo "       Use a network where CreateX is deployed (or etch/deploy it first)." >&2
  exit 1
fi

echo "== building GkrWhirVerifier =="
( cd merged && forge build >/dev/null )
initcode=$(jq -r '.bytecode.object' merged/out/GkrWhirVerifier.sol/GkrWhirVerifier.json)

echo "== deploying GkrWhirVerifier via CreateX deployCreate2 =="
receipt=$(cast send $CREATEX "deployCreate2(bytes32,bytes)" "$SALT" "$initcode" \
  --private-key $KEY --rpc-url $RPC --json)
status=$(printf '%s' "$receipt" | jq -r '.status')
if [ "$status" != "0x1" ] && [ "$status" != "1" ]; then
  echo "ERROR: deployCreate2 transaction failed (status $status)" >&2
  exit 1
fi
creation_sig=$(cast sig-event "ContractCreation(address indexed newContract, bytes32 indexed salt)")
topic=$(printf '%s' "$receipt" | jq -r --arg sig "$creation_sig" \
  '.logs[] | select(.topics[0] == $sig) | .topics[1]' | head -1)
if [ -z "$topic" ] || [ "$topic" = "null" ]; then
  echo "ERROR: no ContractCreation event in the deployment receipt" >&2
  exit 1
fi
ADDR=$(cast parse-bytes32-address "$topic")
echo "   GkrWhirVerifier : $ADDR"
echo "== done =="
echo "send the proof transaction with:"
echo "   ./send_proof.sh $ADDR"
