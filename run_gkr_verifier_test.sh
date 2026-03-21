#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "==> Step 0: Compile GKR circuits"
(cd cs && cargo test -p cs --release compile_add_sub_lui_auipc_mop_into_gkr -- --nocapture)
(cd cs && cargo test -p cs --release compile_jump_branch_slt_into_gkr -- --nocapture)
(cd cs && cargo test -p cs --release compile_shift_binop_into_gkr -- --nocapture)

echo "==> Step 1: Generate proof"
(cd prover && RUST_MIN_STACK=100000000 cargo test -p prover --release --features gkr_self_checks \
  -- --nocapture gkr_run_basic_unrolled_test)

echo "==> Step 2: Regenerate inlined GKR verifier"
(cd verifier_generator && cargo test -p verifier_generator generate_gkr_inlined)

echo "==> Step 3: Build RISC-V binary"
(cd tools/gkr_verifier && ./dump_bin.sh)

echo "==> Step 4: Native verifier test"
(cd verifier && cargo test -p verifier --features gkr_verify test_gkr_sumcheck_verify_inlined)

echo "==> Step 5: Transpiler verifier test"
(cd verifier && cargo test -p verifier --release --features gkr_verify -- --nocapture --include-ignored test_gkr_verifier_in_transpiler)

echo "==> All tests passed!"
