#!/usr/bin/env bash
set -euo pipefail

# echo "==> Step 0: Compile GKR circuits"
# (cd cs && cargo test -p cs --release)

# echo "==> Step 1: Generate proof"
# (cd prover && RUST_MIN_STACK=100000000 cargo test -p prover --release --features gkr_self_checks \
#   -- --nocapture gkr_run_basic_unrolled_test)

echo "==> Step 2: Regenerate inlined GKR verifier"
cargo test -p verifier_generator --test generate_verifiers

echo "==> Step 3: Build RISC-V binary"
(cd tools/gkr_verifier && ./dump_bin.sh)

echo "==> Step 4: Verifier tests"
cargo test -p verifier --features gkr_verify \
  -- --include-ignored

echo "==> All tests passed!"
