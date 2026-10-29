#!/bin/bash
set -e
./recreate_verifiers.sh

wait

./tools/reproduce/reproduce.sh --skip-generate-verifiers "$@"

RUST_MIN_STACK=16777216 cargo test -p full_statement_verifier --profile cli \
  --features host_utils,verifiers --test cost_model_trace emit_census_tables -- --exact --ignored

wait

RUST_MIN_STACK=100000000 cargo test -p verifier_evm --test generate_contracts -- --ignored

