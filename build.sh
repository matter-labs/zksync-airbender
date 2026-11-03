#!/bin/bash
set -e
./recreate_verifiers.sh

wait

./tools/reproduce/reproduce.sh

wait

RUST_MIN_STACK=100000000 cargo test -p verifier_evm regenerate_evm_verifier_stubs

