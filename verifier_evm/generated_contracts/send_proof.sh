#!/bin/sh
# Send the single verification transaction to an already-deployed GkrWhirVerifier. The proof
# bytes (GKR stream ‖ WHIR proof stream) are the transaction's calldata, read from ../debug_data/<mode>
# (regenerate with `cargo test -p verifier_evm --release --test flatten_calldata -- --ignored` after a new proof). The
# verifier address comes from OUTSIDE the script — argument or environment — since it is a
# property of the deployment (see ./deploy.sh), not of this repository. A successful transaction
# (status 1) means the whole GKR+WHIR verification passed and the verifier reported
# `(publicInput, auxInput)` to its registry (`markVerified`); the same 64-byte tuple is the
# call's return data. The registry must accept only approved verifier addresses (`msg.sender`),
# each pinned to one setup embedded in its runtime code, and check `auxInput` against the expected chain.
#
# Requires Foundry v1.9.0 on PATH and a Glamsterdam-capable chain.
#   ./send_proof.sh <mode> <verifier-address>
#   VERIFIER_ADDR=0x… ./send_proof.sh <mode>
set -e
cd "$(dirname "$0")"

case "${1:-}" in
  pessimistic_conjecture|ethproofs_soundcalc) MODE=$1; shift ;;
  *) echo "usage: $0 <pessimistic_conjecture|ethproofs_soundcalc> <verifier-address> (or set VERIFIER_ADDR)" >&2; exit 1 ;;
esac

# Defaults target a local development node; override for the deployment's RPC and signer.
RPC=${RPC:-http://127.0.0.1:8545}
KEY=${KEY:-0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80}

VERIFIER_ADDR=${1:-${VERIFIER_ADDR:-}}
if [ -z "$VERIFIER_ADDR" ]; then
  echo "usage: $0 <mode> <verifier-address> (or set VERIFIER_ADDR)" >&2
  exit 1
fi

# The proof's hex exceeds Linux's per-argument limit. Forge reads it from disk and
# signs/broadcasts the call without passing the proof through argv or the environment.
export VERIFIER_ADDR
cd "$MODE/merged"
forge script script/SendProof.s.sol:SendProof --broadcast --private-key "$KEY" --rpc-url "$RPC"
