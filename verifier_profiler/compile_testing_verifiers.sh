#!/bin/bash

circuit_names=(
    "full_machine_2^20_4_2nd_word_bits"
    "full_machine_2^21_4_2nd_word_bits"
)

for CIRCUIT_NAME in "${circuit_names[@]}"; do
    echo $CIRCUIT_NAME

    VER_DIR="verifiers/$CIRCUIT_NAME/verifier_for_compilation"

    cd $VER_DIR
    ./build_for_testing.sh
    cd -

    cp $VER_DIR/tester.bin binaries/${CIRCUIT_NAME}_compiled_verifier.bin
    cp $VER_DIR/tester.elf binaries/${CIRCUIT_NAME}_compiled_verifier.elf
    cp $VER_DIR/tester.text binaries/${CIRCUIT_NAME}_compiled_verifier.text

done