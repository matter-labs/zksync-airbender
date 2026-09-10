#!/bin/bash

set -e

cd "$(dirname "$0")"

# Keep compiler layouts and SSA in sync with the production artifacts.
RUST_MIN_STACK=100000000 cargo test -p cs --lib compile_bigint_with_extended_control
RUST_MIN_STACK=100000000 cargo test -p cs --lib compile_unsigned_mul_div
RUST_MIN_STACK=100000000 cargo test -p cs --lib compile_inits_and_teardowns
RUST_MIN_STACK=100000000 cargo run -p gpu_gkr_compiler --profile cli --features search \
    --bin gkr-forward-artifact -- --circuit inits_and_teardowns \
    --layout cs/compiled_circuits/inits_and_teardowns_layout_gkr.json \
    --output cs/compiled_circuits/inits_and_teardowns_schedule_b4_gkr.json \
    --seed 0 --cache-buckets 4 --population 64 --evaluations 20000 --replace
RUST_MIN_STACK=100000000 cargo test -p witness_eval_generator --lib gen_for_gkr

circuit_names=(
    "blake2_with_compression"
    "blake2_g_function"
    "bigint_with_control"
    "keccak_special5"
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

(cargo test -p verifier_generator --no-default-features --test generate_verifiers)
