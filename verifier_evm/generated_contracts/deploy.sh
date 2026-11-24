#!/bin/sh
# Requires Foundry v1.9.0 on PATH and a Glamsterdam-capable chain.
# Deterministic deployment of the L1 wrap GkrWhirVerifier (+ a TestRegistry) through the CreateX
# factory (https://github.com/pcaversaccio/createx, pre-deployed on most networks at the fixed
# address below) via `ICreateX.deployCreate2(bytes32 salt, bytes initCode)`, so every address is a
# pure function of (factory, salt, initCode).
#
# The verifier is generated for one registry address and takes NO constructor arguments.
# Regenerate it (tests/generate_contracts.rs) if the registry changes. The default TestRegistry
# address is deterministic for this factory, guarded salt and stable registry initcode.
# Before any deployment, this script checks the selected registry against the generated constant.
# On success the verifier calls `registry.markVerified(publicInput, auxInput)`. A production
# registry must accept only approved verifier addresses (`msg.sender`), each pinned to one
# setup embedded in its runtime code, and compare `auxInput` with the expected chain hash.
#
# CREATE2 reverts on an address collision. Changing the registry salt requires regenerating
# the verifier for the new registry address; the verifier salt can be changed independently.
# Feed the printed verifier address to ./send_proof.sh afterwards.
set -e
cd "$(dirname "$0")"

case "${1:-}" in
  pessimistic_conjecture|ethproofs_soundcalc) MODE=$1; shift ;;
  *) echo "usage: $0 <pessimistic_conjecture|ethproofs_soundcalc>" >&2; exit 1 ;;
esac

# ---- configuration: edit for the target network ------------------------------------------------
RPC=${RPC:-http://127.0.0.1:8545}
KEY=${KEY:-0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80}
# First 20 bytes zero + 21st byte zero = CreateX's unpermissioned, non-redeploy-protected salt
# flavor (anyone can reproduce the address).
REGISTRY_SALT=0x00000000000000000000000000000000000000000000000000616972621b0001
VERIFIER_SALT=0x00000000000000000000000000000000000000000000000000616972621b0002
# An already-deployed registry to bind the verifier to instead of deploying TestRegistry:
REGISTRY_ADDR=${REGISTRY_ADDR:-}
# ------------------------------------------------------------------------------------------------

CREATEX=0xba5Ed099633D3B313e4D5F7bdc1305d3c28ba5Ed

# deploy_create2 <salt> <initcode> -> prints the created address (from the factory's event)
deploy_create2() {
  receipt=$(cast send "$CREATEX" "deployCreate2(bytes32,bytes)" "$1" "$2" \
    --private-key "$KEY" --rpc-url "$RPC" --json)
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
( cd "$MODE/merged" && forge build >/dev/null )

# Read the generated address before sending any transaction. address(0x00...) is an
# integer-to-address literal, avoiding checksum interpretation by Solidity.
GENERATED_REGISTRY=$(sed -n 's/.*constant __TEMPLATE_REGISTRY = address(0x00\([0-9a-f]\{40\}\));.*/0x\1/p' "$MODE/merged/src/GkrWhirVerifier.sol")
if [ -z "$GENERATED_REGISTRY" ]; then
  echo "ERROR: generated registry constant not found; regenerate the verifier." >&2
  exit 1
fi
registry_initcode=$(jq -r '.bytecode.object' "$MODE/merged/out/TestRegistry.sol/TestRegistry.json")
if [ -z "$REGISTRY_ADDR" ]; then
  # CreateX hashes this unpermissioned, cross-chain-unprotected salt before CREATE2:
  # https://github.com/pcaversaccio/createx/blob/main/src/CreateX.sol (_guard).
  guarded_salt=$(cast keccak "$REGISTRY_SALT")
  registry_hash=$(cast keccak "$registry_initcode")
  address_hash=$(cast keccak "0xff${CREATEX#0x}${guarded_salt#0x}${registry_hash#0x}")
  EXPECTED_REGISTRY=0x$(printf '%s' "$address_hash" | tail -c 40)
else
  EXPECTED_REGISTRY=$REGISTRY_ADDR
fi
if [ "$(printf '%s' "$EXPECTED_REGISTRY" | tr 'A-F' 'a-f')" != "$GENERATED_REGISTRY" ]; then
  echo "ERROR: selected registry $EXPECTED_REGISTRY differs from generated $GENERATED_REGISTRY." >&2
  echo "       Regenerate the verifier for the selected registry before deploying." >&2
  exit 1
fi

factory_code=$(cast code "$CREATEX" --rpc-url "$RPC")
if [ "$factory_code" = "0x" ]; then
  echo "ERROR: no CreateX factory code at $CREATEX on this RPC." >&2
  echo "       Use a network where CreateX is deployed (or etch/deploy it first)." >&2
  exit 1
fi

if [ -z "$REGISTRY_ADDR" ]; then
  echo "== deploying TestRegistry via CreateX deployCreate2 =="
  registry_initcode=$(jq -r '.bytecode.object' "$MODE/merged/out/TestRegistry.sol/TestRegistry.json")
  REGISTRY_ADDR=$(deploy_create2 "$REGISTRY_SALT" "$registry_initcode")
fi
echo "   registry        : $REGISTRY_ADDR"

echo "== deploying GkrWhirVerifier() via CreateX deployCreate2 =="
initcode=$(jq -r '.bytecode.object' "$MODE/merged/out/GkrWhirVerifier.sol/GkrWhirVerifier.json")
registry_code=$(cast code "$REGISTRY_ADDR" --rpc-url "$RPC")
if [ "$registry_code" = "0x" ]; then
  echo "ERROR: registry $REGISTRY_ADDR has no code." >&2
  exit 1
fi
ADDR=$(deploy_create2 "$VERIFIER_SALT" "$initcode")
echo "   GkrWhirVerifier : $ADDR"
# The runtime has no getter: compare its bytes with the generated runtime prefix
# plus embedded setup. This also checks that the generated registry constant was deployed.
prefix=$(jq -r '.deployedBytecode.object' "$MODE/merged/out/GkrWhirVerifier.sol/GkrWhirVerifierCode.json")
setup=$(sed -n 's/.*bytes.concat(.*hex"\([0-9a-f]*\)").*/\1/p' "$MODE/merged/src/GkrWhirVerifier.sol")
deployed=$(cast code "$ADDR" --rpc-url "$RPC")
if [ -z "$setup" ] || [ "$deployed" != "0x${prefix#0x}${setup}" ]; then
  echo "ERROR: deployed verifier runtime differs from the generated registry/setup" >&2
  exit 1
fi
echo "== done =="
echo "send the proof transaction with:"
echo "   ./send_proof.sh $MODE $ADDR"
