#!/usr/bin/env bash
#
# Generate AGGRESSIVE-v2 WHIR verifier input data (same 8 witness + 1 setup polys of
# 2^26 as the production/aggressive configs, first LDE 64 => base RS codeword 2^32,
# every codeword pinned at 2^32). Folding plan: fold by 2 in the FIRST round only
# (keeps the 8-column base leaf small), then by 2^4, then aggressively by 2^5. Total
# 5 rounds, sum of folds 20 => 2^6 = 64 final coefficients (a larger final poly than
# v1's 16 — trades a bigger final-aggregate for a smaller proof). 100-bit security
# under the pessimistic conjecture, PoW capped at 30 bits. Computed schedule:
#   folds   = [1, 4, 5, 5, 5]   (fold by 2, 16, 32, 32, 32)
#   cb      = [6, 7, 11, 16, 21]
#   queries = [14, 12, 8, 6, 4]
#   pow     = [30, 30, 27, 20, 30]
#   final   = 64 monomials (rfin 6)
# EVM verifier: verifier_evm/whir/whir_agg2.sol (WhirVerifierAgg2).
#
# HEAVY (2^32 codewords). Uses all cores. Base + intermediate oracles are committed
# coset-by-coset so the full codeword is never materialized; PoW grinding is
# parallelized across the worker.
#
# Writes:
#   verifier_evm/whir/testdata/proth120_whir_calldata_agg2.hex
#   verifier_evm/whir/testdata/proth120_whir_input_agg2.json
#
# Usage: ./gen_whir_agg2.sh
set -euo pipefail
cd "$(dirname "$0")"

# -C debuginfo=0 keeps the build lighter. If the build SIGBUSes during codegen
# (seen on some toolchains for the prover crate), also add: -C codegen-units=256
export RUSTFLAGS="${RUSTFLAGS:-} -C debuginfo=0"

exec cargo test --release -p prover --features prover --lib \
    generate_whir_input_for_evm_aggressive_v2 -- --ignored --nocapture
