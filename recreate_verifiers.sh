#!/bin/bash

set -e

cd "$(dirname "$0")"

usage() {
    cat <<'EOF'
Usage: ./recreate_verifiers.sh [--help]

Regenerate circuit layouts, witness evaluators and Rust verifiers.
For L1 proof references, follow REGENERATE in prover_pipeline/src/l1_reference.rs:
seed, then fresh-process feeder/wrap.
Next run that module's ignored l1_reference::export_l1_wrap_setup_frontier test.
Then run the ignored verifier_evm producers: generate_contracts (also build.sh),
flatten_calldata write_calldata_into_debug_data.
EOF
}

for option in "$@"; do
    case "$option" in
        --help|-h) usage; exit 0 ;;
        *) echo "unknown option: $option" >&2; usage >&2; exit 1 ;;
    esac
done

# Keep compiler layouts and SSA in sync with the production artifacts.
RUST_MIN_STACK=100000000 cargo test -p cs --lib -- \
    _into_gkr _into_no_caches_gkr _witness_graph
RUST_MIN_STACK=100000000 cargo test -p witness_eval_generator --lib -- \
    gen_for_gkr gen_for_large_field

circuit_names=(
    "bigint_with_control"
    "blake2_g_function"
    "blake2_with_compression"
    "keccak_chi5"
    "keccak_column_parity"
    "keccak_special5"
    "keccak_theta_rho"
)

unrolled_circuit_names=(
    "add_sub_lui_auipc_mop"
    "inits_and_teardowns"
    "jump_branch_slt"
    "load_store_subword_only"
    "load_store_word_only"
    "mul_div_unsigned"
    "shift_binary"
    "unified_reduced_machine"
    "unified_reduced_machine_2_22"
)

for CIRCUIT_NAME in "${circuit_names[@]}"; do
    echo $CIRCUIT_NAME

    (cd circuit_defs/${CIRCUIT_NAME} && RUST_MIN_STACK=100000000 cargo test generate)
done

for CIRCUIT_NAME in "${unrolled_circuit_names[@]}"; do
    echo $CIRCUIT_NAME

    (cd circuit_defs/unrolled_circuits/${CIRCUIT_NAME} && RUST_MIN_STACK=100000000 cargo test generate)
done

(cd circuit_defs/setups && RUST_MIN_STACK=100000000 cargo test --release generate_delegation_circuits_artifacts)

cargo run -p gpu_witness_eval_generator --bin regenerate_committed

for SCHEDULE in cs/compiled_circuits/*_schedule_b4_gkr.json; do
    STEM=$(basename "$SCHEDULE" _schedule_b4_gkr.json)
    cargo run --release -p gpu_gkr_compiler --features search --bin gkr-forward-artifact -- \
        --if-stale --circuit "$STEM" --layout "cs/compiled_circuits/${STEM}_layout_gkr.json" \
        --output "$SCHEDULE" --seed 42 --cache-buckets 4 --population 64 --evaluations 1024
done

cargo run --release -p gpu_gkr_compiler --features search --bin gkr-forward-artifact -- \
    --if-stale --field proth120 --circuit unified_reduced_machine \
    --layout cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120_2p21.json \
    --output cs/compiled_circuits/unified_reduced_machine_schedule_b4_gkr_proth120.json \
    --seed 42 --cache-buckets 4 --population 64 --evaluations 1024

(cargo test -p verifier_generator --no-default-features --test generate_verifiers)
