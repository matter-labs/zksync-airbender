#!/bin/sh
# Regenerate the verifier Solidity, build the two sibling verifier projects, then run the
# two-transaction cross-check. Run from anywhere.
set -e
cd "$(dirname "$0")"

# 1. (re)generate GkrVerifier.sol / WhirVerifier.sol / GkrWhirRegistry.sol from the artifact
( cd .. && cargo test -p verifier_evm --test generate_contracts >/dev/null )

# 2. compile each verifier in its own Foundry project (different optimizer settings)
( cd gkr  && forge build )
( cd whir && forge build )

# 3. run the cross-check (reads the sibling deployedBytecode + calldata from ../../debug_data)
( cd two_tx && forge test --match-contract GkrWhirTwoTxTest -vv )
