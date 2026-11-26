#!/bin/bash

set -e

cd "$(dirname "$0")"

usage() {
    cat <<'EOF'
Usage: ./recreate_verifiers.sh [--help]

Regenerate circuit layouts, witness evaluators and Rust verifiers.
For L1 proof references, setup-frontier export and EVM checks, follow
fixtures/README.md.
EOF
}

for option in "$@"; do
    case "$option" in
        --help|-h) usage; exit 0 ;;
        *) echo "unknown option: $option" >&2; usage >&2; exit 1 ;;
    esac
done

# Generate crate layouts/SSAs and the compiler's no-cache layouts before their consumers.
RUST_MIN_STACK=100000000 bash gkr_test.sh unified circuits
RUST_MIN_STACK=100000000 cargo test -p witness_eval_generator --lib -- gen_for_gkr

(RUST_MIN_STACK=100000000 cargo test -p unified_reduced_machine_2_22 --profile cli --lib \
    test::witness_eval_fn_matches_sibling -- --exact)

(RUST_MIN_STACK=100000000 cargo test -p unified_reduced_machine_proth120_2_22 --profile cli --lib \
    test::witness_eval_fn_matches_sibling -- --exact)

(cd circuit_defs/setups && RUST_MIN_STACK=100000000 cargo test --release generate_delegation_circuits_artifacts)

cargo run -p gpu_witness_eval_generator --bin regenerate_committed

for SCHEDULE in cs/compiled_circuits/*_schedule_b4_gkr.json; do
    STEM=$(basename "$SCHEDULE" _schedule_b4_gkr.json)
    case "$STEM" in
        bigint_with_extended_control) PACKAGE=bigint_with_control ;;
        blake2_with_extended_control) PACKAGE=blake2_with_compression ;;
        mem_subword_only) PACKAGE=load_store_subword_only ;;
        mem_word_only) PACKAGE=load_store_word_only ;;
        shift_binop) PACKAGE=shift_binary ;;
        unsigned_mul_div) PACKAGE=mul_div_unsigned ;;
        *) PACKAGE=$STEM ;;
    esac
    CIRCUIT_DIR="circuit_defs/$PACKAGE"
    if [[ ! -d "$CIRCUIT_DIR" ]]; then
        CIRCUIT_DIR="circuit_defs/unrolled_circuits/$PACKAGE"
    fi
    cargo run --release -p gpu_gkr_compiler --features search --bin gkr-forward-artifact -- \
        --if-stale --circuit "$STEM" --layout "$CIRCUIT_DIR/generated/layout.json" \
        --output "$SCHEDULE" --seed 42 --cache-buckets 4 --population 64 --evaluations 1024
done

cargo run --release -p gpu_gkr_compiler --features search --bin gkr-forward-artifact -- \
    --if-stale --field proth120 --circuit unified_reduced_machine \
    --layout circuit_defs/unrolled_circuits/unified_reduced_machine_proth120_2_21/generated/layout.json \
    --output cs/compiled_circuits/unified_reduced_machine_schedule_b4_gkr_proth120.json \
    --seed 42 --cache-buckets 4 --population 64 --evaluations 1024

(cargo test -p verifier_generator --no-default-features --test generate_verifiers)
