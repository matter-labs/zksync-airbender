#!/bin/sh
# Deterministic deployment of the two-transaction verifier suite through the CreateX factory
# (https://github.com/pcaversaccio/createx, pre-deployed on most networks at the fixed address
# below). Deployment order matters: the REGISTRY goes first, because both verifiers bake the
# registry address in as a compile-time `address constant` (they `call` it to mark their
# committed state) — after the registry lands, the GKR/WHIR sources are REGENERATED with the
# registry address (`REGISTRY_ADDRESS` env consumed by the verifier_evm `generate_contracts`
# test), rebuilt, and only then deployed.
#
# All three contracts deploy via `ICreateX.deployCreate2(bytes32 salt, bytes initCode)` with the
# SAME salt (set below), so every address is a pure function of (factory, salt, initCode). The
# script never computes CREATE2 addresses. Two-step flow:
#
#   1. Leave REGISTRY_ADDR all-zero and run ./deploy.sh — it deploys ONLY the registry, prints
#      the address the factory reports (ContractCreation event), and exits.
#   2. Substitute that address into REGISTRY_ADDR below and run ./deploy.sh again — it sees the
#      registry code already on-chain, regenerates + builds + deploys the two verifiers.
#
# (A pre-computed REGISTRY_ADDR also works in one run: with no code at the address yet, the
# registry is deployed first and the script checks code actually landed there.)
# CREATE2 reverts on an address collision — bump SALT to deploy a fresh suite; note a failed
# partial run still consumes the salt for the contracts it did deploy.
#
# Feed the (pre-computed) GKR + WHIR addresses to ./send_proofs.sh afterwards.
set -e
cd "$(dirname "$0")"

# ---- configuration: edit for the target network ------------------------------------------------
RPC=http://127.0.0.1:8545
KEY=0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
# One salt for the whole suite. First 20 bytes zero + 21st byte zero = CreateX's unpermissioned,
# non-redeploy-protected salt flavor (anyone can reproduce the addresses).
SALT=0x00000000000000000000000000000000000000000000000000616972621b0001
# The registry's CREATE2 address. All-zero = bootstrap mode: deploy the registry, print its
# address, and exit (substitute the printed address here before the second run).
REGISTRY_ADDR=0x0000000000000000000000000000000000000000
# ------------------------------------------------------------------------------------------------

CREATEX=0xba5Ed099633D3B313e4D5F7bdc1305d3c28ba5Ed

factory_code=$(cast code $CREATEX --rpc-url $RPC)
if [ "$factory_code" = "0x" ]; then
  echo "ERROR: no CreateX factory code at $CREATEX on this RPC." >&2
  echo "       Use a network where CreateX is deployed (or etch/deploy it first)." >&2
  exit 1
fi

# Deploy `initcode` via deployCreate2(SALT, initcode); prints the receipt JSON on stdout and
# fails the script on a reverted tx.
deploy_create2() {
  initcode=$1
  receipt=$(cast send $CREATEX "deployCreate2(bytes32,bytes)" "$SALT" "$initcode" \
    --private-key $KEY --rpc-url $RPC --json)
  status=$(printf '%s' "$receipt" | jq -r '.status')
  if [ "$status" != "0x1" ] && [ "$status" != "1" ]; then
    echo "ERROR: deployCreate2 transaction failed (status $status)" >&2
    exit 1
  fi
  printf '%s' "$receipt"
}

build_registry_initcode() {
  ( cd two_tx && forge build >/dev/null )
  jq -r '.bytecode.object' two_tx/out/GkrWhirRegistry.sol/GkrWhirRegistry.json
}

if [ "$REGISTRY_ADDR" = "0x0000000000000000000000000000000000000000" ]; then
  # ---- bootstrap: deploy the registry, report the address the factory created, exit ----
  echo "== REGISTRY_ADDR is all-zero: deploying ONLY the registry (bootstrap) =="
  receipt=$(deploy_create2 "$(build_registry_initcode)")
  creation_sig=$(cast sig-event "ContractCreation(address indexed newContract, bytes32 indexed salt)")
  topic=$(printf '%s' "$receipt" | jq -r --arg sig "$creation_sig" \
    '.logs[] | select(.topics[0] == $sig) | .topics[1]' | head -1)
  if [ -z "$topic" ] || [ "$topic" = "null" ]; then
    echo "ERROR: no ContractCreation event in the deployment receipt" >&2
    exit 1
  fi
  REG_ADDR=$(cast parse-bytes32-address "$topic")
  echo "   Registry : $REG_ADDR"
  echo ""
  echo "substitute this address into REGISTRY_ADDR in $0 and run it again to"
  echo "regenerate + deploy the GKR and WHIR verifiers."
  exit 0
fi

# ---- full flow: registry known (already deployed, or deployed now if absent) ----
if [ "$(cast code $REGISTRY_ADDR --rpc-url $RPC)" = "0x" ]; then
  echo "== deploying GkrWhirRegistry via CreateX =="
  deploy_create2 "$(build_registry_initcode)" >/dev/null
  if [ "$(cast code $REGISTRY_ADDR --rpc-url $RPC)" = "0x" ]; then
    echo "ERROR: registry deployed, but no code at REGISTRY_ADDR=$REGISTRY_ADDR —" >&2
    echo "       the address does not match this (factory, salt, initCode)." >&2
    exit 1
  fi
else
  echo "== registry code already on-chain at $REGISTRY_ADDR — reusing =="
fi
echo "   Registry : $REGISTRY_ADDR"

# Regenerate the verifier sources with the registry address, rebuild.
echo "== regenerating GKR/WHIR sources with REGISTRY_ADDRESS=$REGISTRY_ADDR =="
( cd .. && REGISTRY_ADDRESS=$REGISTRY_ADDR cargo test -q -p verifier_evm --test generate_contracts >/dev/null )
( cd gkr  && forge build >/dev/null )
( cd whir && forge build >/dev/null )

# Deploy both verifiers with the same salt.
echo "== deploying verifiers via CreateX =="
deploy_create2 "$(jq -r '.bytecode.object' gkr/out/GkrVerifier.sol/GKRVerifier.json)" >/dev/null
echo "   GKR      : deployed"
deploy_create2 "$(jq -r '.bytecode.object' whir/out/WhirVerifier.sol/WhirVerifier.json)" >/dev/null
echo "   WHIR     : deployed"

echo "== done =="
echo "send the proof transactions with your pre-computed verifier addresses:"
echo "   ./send_proofs.sh <gkr-address> <whir-address>"
