#!/bin/sh

# Potentially different circuit sizes for tests

cd cs

# RISC-V machines
cargo test compile_minimal_machine_with_delegation
cargo test reduced_machine_with_delegation_get_witness_graph
cargo test compile_full_machine_with_delegation
cargo test full_machine_with_delegation_get_witness_graph
# Delegations
cargo test compile_blake2_with_extended_control
cargo test blake_delegation_get_witness_graph
cargo test compile_u256_ops_extended_control
cargo test bigint_delegation_get_witness_graph

cd ../witness_eval_generator
cargo test gen_for_prover_tests

wait

# Now actual production functions

cd ../
./recreate_verifiers.sh

wait

cd tools/verifier/
./build.sh

