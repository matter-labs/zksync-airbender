#!/bin/bash

set -e

cd "$(dirname "$0")"

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
