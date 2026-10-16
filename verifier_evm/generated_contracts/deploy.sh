#!/bin/sh
# Deterministic deployment of a version's merged v0 GkrWhirVerifier (+ a TestRegistry) through the CreateX
# factory (https://github.com/pcaversaccio/createx, pre-deployed on most networks at the fixed
# address below) via `ICreateX.deployCreate2(bytes32 salt, bytes initCode)`, so every address is a
# pure function of (factory, salt, initCode).
#
# The verifier takes the registry address as its ONLY constructor argument (immutable; must be
# non-zero and have code), so the deployment is two steps: 1. the registry (TestRegistry here —
# substitute the production IVerificationRegistry's initcode/address), 2. the verifier with the
# registry address appended to its initcode. On success the verifier calls
# `registry.markVerified(publicInput, auxInput, setupCommitment)`.
#
# CREATE2 reverts on an address collision — bump the salts to deploy fresh contracts.
# Feed the printed verifier address to ./send_proof.sh afterwards. The F1 verifier additionally
# pins its SetupFrontier data contract's address and code hash: deploy the frontier first and
# generate the F1 verifier with that address.
#
#   ./deploy.sh <2p21>
set -eu
SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
. "$SCRIPT_DIR/version.sh"
select_version "${1:?usage: deploy.sh <2p21>}"
cd "$CONTRACTS_ROOT"

# ---- configuration: edit for the target network ------------------------------------------------
RPC=http://127.0.0.1:8545
KEY=0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
# REGISTRY_SALT / VERIFIER_SALT come from version.sh: first 20 bytes zero + 21st byte zero =
# CreateX's unpermissioned, non-redeploy-protected salt flavor (anyone can reproduce the address).
# An already-deployed registry to bind the verifier to instead of deploying TestRegistry: set the
# version's REGISTRY_ADDR_<VERSION> (version.sh).
# ------------------------------------------------------------------------------------------------

CREATEX=0xba5Ed099633D3B313e4D5F7bdc1305d3c28ba5Ed

factory_code=$(cast code $CREATEX --rpc-url $RPC)
if [ "$factory_code" = "0x" ]; then
  echo "ERROR: no CreateX factory code at $CREATEX on this RPC." >&2
  echo "       Use a network where CreateX is deployed (or etch/deploy it first)." >&2
  exit 1
fi

# deploy_create2 <salt> <initcode> -> prints the created address (from the factory's event)
deploy_create2() {
  receipt=$(cast send $CREATEX "deployCreate2(bytes32,bytes)" "$1" "$2" \
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
  cast parse-bytes32-address "$topic"
}

echo "== building GkrWhirVerifier + TestRegistry =="
( cd merged && forge build >/dev/null )

if [ -z "$REGISTRY_ADDR" ]; then
  echo "== deploying TestRegistry via CreateX deployCreate2 =="
  registry_initcode=$(jq -r '.bytecode.object' merged/out/TestRegistry.sol/TestRegistry.json)
  REGISTRY_ADDR=$(deploy_create2 "$REGISTRY_SALT" "$registry_initcode")
fi
echo "   registry        : $REGISTRY_ADDR"

echo "== deploying GkrWhirVerifier(registry) via CreateX deployCreate2 =="
initcode=$(jq -r '.bytecode.object' merged/out/GkrWhirVerifier.sol/GkrWhirVerifier.json)
ctor_args=$(cast abi-encode "constructor(address)" "$REGISTRY_ADDR")
ADDR=$(deploy_create2 "$VERIFIER_SALT" "${initcode}${ctor_args#0x}")
echo "   GkrWhirVerifier : $ADDR"
pinned=$(cast call "$ADDR" "registry()(address)" --rpc-url $RPC)
if [ "$(printf '%s' "$pinned" | tr 'A-F' 'a-f')" != "$(printf '%s' "$REGISTRY_ADDR" | tr 'A-F' 'a-f')" ]; then
  echo "ERROR: deployed verifier reports registry $pinned, expected $REGISTRY_ADDR" >&2
  exit 1
fi
echo "== done =="
echo "send the proof transaction with:"
echo "   $SCRIPT_DIR/send_proof.sh $AB_EVM_VERSION $ADDR"
