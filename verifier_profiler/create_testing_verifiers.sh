#!/bin/bash

circuit_names=(
    "full_machine_2^20_4_2nd_word_bits"
    "full_machine_2^21_4_2nd_word_bits"
    "reduced_machine_2^22_4_2nd_word_bits"
    "reduced_machine_2^23_4_2nd_word_bits"
)

for CIRCUIT_NAME in "${circuit_names[@]}"; do
    echo $CIRCUIT_NAME

    CIRCUIT_DIR="verifiers/$CIRCUIT_NAME"
    DST_DIR="$CIRCUIT_DIR/verifier"

    rm -r $CIRCUIT_DIR

    mkdir $CIRCUIT_DIR

    cp -r ../verifier $DST_DIR

    rm $DST_DIR/src/generated/*

    cp circuit_files/${CIRCUIT_NAME}_layout.json $DST_DIR/src/generated/layout
    cp circuit_files/${CIRCUIT_NAME}_circuit_layout.rs $DST_DIR/src/generated/circuit_layout.rs
    cp circuit_files/${CIRCUIT_NAME}_quotient.rs $DST_DIR/src/generated/quotient.rs

    rm $DST_DIR/README.md
    rm $DST_DIR/expand.sh
    rm $DST_DIR/flamegraph.svg

    DST_DIR="$CIRCUIT_DIR/verifier_for_compilation"
    cp -r verifier_for_compilation $DST_DIR

done