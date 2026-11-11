#!/bin/sh
cd "$(dirname "$0")/prover"
cargo flamegraph --root --profile cli --features test --unit-test -- \
    --exact tests::gkr::unified_generated_witness::generated_witness_satisfies_regular_layout
