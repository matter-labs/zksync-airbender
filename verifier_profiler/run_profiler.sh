#!/bin/bash

# Write machines you want to profile to profiling_configs.json before running this script

cargo test generate_circuit_files_test --release -- --nocapture

cargo test include_witness_generator_function_test --release -- --nocapture

cargo test generate_testing_proofs --release -- --nocapture

cargo test generate_script_for_creating_verifiers --release -- --nocapture

./create_testing_verifiers.sh

cargo test generate_script_for_compiling_verifiers --release -- --nocapture

./compile_testing_verifiers.sh

cargo test profile_verifiers --release -- --nocapture
