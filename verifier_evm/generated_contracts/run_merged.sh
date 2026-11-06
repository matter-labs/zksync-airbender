#!/bin/sh
# End-to-end for the merged single-transaction verifier: (re)generate GkrWhirVerifier.sol from
# the circuit artifact, regenerate the single tx's calldata from the proof, compile, run the
# Foundry test (pure execution gas, then tx-level gas incl. intrinsic + EIP-7623), and report the
# compiler options, deployed bytecode size and the REAL tx gas (raw anvil tx, no harness
# over-count).
#
#   ./run_merged.sh          # full run
#   ./run_merged.sh --no-gas # skip the anvil raw-tx gas step
#
# The verifier binds the statement to the terminal PC of the checked-in L1 feeder binary and to
# the pinned inits/teardowns top bits; the proof must have been produced against that same binary
# (otherwise the GKR half reverts on the final-PC / top-bits checks). The Foundry test deploys a
# TestRegistry and checks the (publicInput, auxInput, setupCommitment) mark it records.
set -e
cd "$(dirname "$0")"

# 1. generate the verifier source + the calldata (production Rust functions; no fixtures).
#    debuginfo=0: rustc (macOS/aarch64 nightly) may SIGBUS emitting DWARF for keccak_special5.
echo "== generating the verifier + calldata from the circuit artifact + proof =="
( cd .. && RUSTFLAGS="-C debuginfo=0" cargo test -q -p verifier_evm --test generate_contracts >/dev/null )
( cd .. && RUSTFLAGS="-C debuginfo=0" cargo test -q -p verifier_evm --test flatten_calldata   >/dev/null )

# 2. compile
echo "== compiling GkrWhirVerifier (via_ir, runs=1) =="
( cd merged && forge build >/dev/null )

# 3. single-transaction verification
echo "== single-transaction verification: pure execution gas (no isolation) =="
( cd merged && forge test --no-isolate -vv | grep -E "calldata_bytes|verifier_call_gas|public_input|aux_input|setup_commitment|PASS|FAIL" )
echo "== single-transaction verification: tx-level gas (isolation: intrinsic + EIP-7623) =="
( cd merged && forge test --isolate -vv --match-test test_merged_single_tx | grep -E "verifier_call_gas|PASS|FAIL" )

# 4. compiler options actually used
echo "== compiler options =="
art=$(find merged/out -name 'GkrWhirVerifier.json' | head -1)
ver=$(jq -r '.metadata.compiler.version' "$art")
ir=$(jq -r '.metadata.settings.viaIR // false' "$art")
opt=$(jq -r '.metadata.settings.optimizer | "optimizer=\(.enabled) runs=\(.runs)"' "$art")
evm=$(jq -r '.metadata.settings.evmVersion // "?"' "$art")
printf "  solc %s  viaIR=%s  %s  evm=%s\n" "$ver" "$ir" "$opt" "$evm"

# 5. bytecode size + real tx gas (raw anvil transaction)
[ "$1" = "--no-gas" ] && exit 0
echo "== deployed bytecode size + real tx gas (Prague / EIP-7623) =="
./raw_tx_gas.sh | grep -E "verifier|gasUsed|registry"
