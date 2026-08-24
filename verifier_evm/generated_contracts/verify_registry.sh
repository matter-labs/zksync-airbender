#!/bin/sh
# Etherscan source/bytecode verification for the deployed GkrWhirRegistry, via forge.
# Runs `forge verify-contract` from the two_tx Foundry project (the one that built and
# deployed the registry), so the compiler version, optimizer settings and metadata hash
# match the on-chain creation bytecode exactly. The registry has no constructor args.
#
#   ./verify_registry.sh <registry-address>
#   REGISTRY_ADDR=0x… ./verify_registry.sh
#
# The GKR/WHIR verifier sources are deployment-specific (the registry address is baked in
# as a constant), so verify them the same way from their own projects if needed:
#   ( cd gkr  && forge verify-contract <addr> src/GkrVerifier.sol:GKRVerifier   … )
#   ( cd whir && forge verify-contract <addr> src/WhirVerifier.sol:WhirVerifier … )
set -e
cd "$(dirname "$0")"

# ---- configuration: edit for the target network ------------------------------------------------
ETHERSCAN_API_KEY=YOUR_ETHERSCAN_API_KEY
CHAIN=sepolia
# ------------------------------------------------------------------------------------------------

REGISTRY_ADDR=${1:-$REGISTRY_ADDR}
if [ -z "$REGISTRY_ADDR" ]; then
  echo "usage: $0 <registry-address>   (or set REGISTRY_ADDR)" >&2
  exit 1
fi
if [ "$ETHERSCAN_API_KEY" = "YOUR_ETHERSCAN_API_KEY" ]; then
  echo "ERROR: substitute ETHERSCAN_API_KEY in this script first." >&2
  exit 1
fi

# Build with the project's committed settings so the verification payload matches the
# deployed bytecode, then submit and poll until Etherscan reports a verdict.
( cd two_tx && forge build >/dev/null )
cd two_tx
exec forge verify-contract "$REGISTRY_ADDR" src/GkrWhirRegistry.sol:GkrWhirRegistry \
  --etherscan-api-key "$ETHERSCAN_API_KEY" \
  --chain "$CHAIN" \
  --watch
