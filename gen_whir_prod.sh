#!/usr/bin/env bash
#
# Generate PRODUCTION-sized WHIR verifier input data (whir.sol VARIANT 4:
# message 2^26, initial LDE 32 => RS codeword 2^31, 8 witness + 1 setup polys,
# folds [2,4,4,4,4,4], queries [17,12,8,6,5,4], PoW [30,30,27,25,21,24]).
#
# HEAVY: tens of GB of RAM and minutes of PoW/FFT. Uses all cores. The base
# oracles are committed coset-by-coset (each LDE coset computed and hashed
# separately, with in-coset parallelism) so the full 2^31 codeword is never
# materialized in RAM. PoW grinding is parallelized across the worker.
#
# Writes:
#   verifier_evm/whir/testdata/proth120_whir_calldata_prod.hex
#   verifier_evm/whir/testdata/proth120_whir_input_prod.json
#
# Usage: ./gen_whir_prod.sh
set -euo pipefail
cd "$(dirname "$0")"

# -C debuginfo=0 keeps the build lighter. If the build SIGBUSes during codegen
# (seen on some toolchains for the prover crate), also add: -C codegen-units=256
export RUSTFLAGS="${RUSTFLAGS:-} -C debuginfo=0"

exec cargo test --release -p prover --features prover --lib \
    generate_whir_input_for_evm_production -- --ignored --nocapture
