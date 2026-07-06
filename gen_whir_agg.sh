#!/usr/bin/env bash
#
# Generate AGGRESSIVE-folding WHIR verifier input data (same 8 witness + 1 setup
# polys of 2^26 as VARIANT 4, but first LDE 64 => base RS codeword 2^32, first fold
# by 8, then fold by 32 while possible down to 16 final coefficients, every RS
# codeword pinned at 2^32). 100-bit security under the pessimistic conjecture, PoW
# capped at 30 bits. Computed schedule:
#   folds   = [3, 5, 5, 5, 4]   (fold by 8, 32, 32, 32, 16)
#   cb      = [6, 9, 14, 19, 24]
#   queries = [14, 10, 6, 5, 4]
#   pow     = [30, 25, 30, 21, 20]
#
# HEAVY: ~2x VARIANT 4 (2^32 codewords). Uses all cores. Base + intermediate oracles
# are committed coset-by-coset so the full codeword is never materialized; PoW
# grinding is parallelized across the worker.
#
# Writes:
#   verifier_evm/whir/testdata/proth120_whir_calldata_agg.hex
#   verifier_evm/whir/testdata/proth120_whir_input_agg.json
#
# Usage: ./gen_whir_agg.sh
set -euo pipefail
cd "$(dirname "$0")"

# -C debuginfo=0 keeps the build lighter. If the build SIGBUSes during codegen
# (seen on some toolchains for the prover crate), also add: -C codegen-units=256
export RUSTFLAGS="${RUSTFLAGS:-} -C debuginfo=0"

exec cargo test --release -p prover --features prover --lib \
    generate_whir_input_for_evm_aggressive -- --ignored --nocapture
