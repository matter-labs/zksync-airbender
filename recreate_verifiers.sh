#!/bin/bash

# Copies over the verifier template from 'verifier' dir to different circuits directories.
circuit_names=(
    "risc_v_cycles"
    "reduced_risc_v_machine"
    "final_reduced_risc_v_machine"
    "machine_without_signed_mul_div"
    "blake2_with_compression"
    "bigint_with_control"
)

# update the generated files
(cd tools/generator && cargo run )

# copy delegation circuit params
cp tools/generator/output/all_delegation_circuits_params.rs circuit_defs/setups/generated/all_delegation_circuits_params.rs

for CIRCUIT_NAME in "${circuit_names[@]}"; do
    echo $CIRCUIT_NAME

    cp tools/generator/output/${CIRCUIT_NAME}_layout.json circuit_defs/$CIRCUIT_NAME/generated/layout
    cp tools/generator/output/${CIRCUIT_NAME}_circuit_layout.rs circuit_defs/$CIRCUIT_NAME/generated/circuit_layout.rs
    cp tools/generator/output/${CIRCUIT_NAME}_quotient.rs circuit_defs/$CIRCUIT_NAME/generated/quotient.rs
    cp tools/generator/output/${CIRCUIT_NAME}_witness_generation_fn.rs circuit_defs/$CIRCUIT_NAME/generated/witness_generation_fn.rs
    cp tools/generator/output/${CIRCUIT_NAME}_witness_generation_fn.cuh circuit_defs/$CIRCUIT_NAME/generated/witness_generation_fn.cuh

    CIRCUIT_DIR="circuit_defs/$CIRCUIT_NAME"
    DST_DIR="$CIRCUIT_DIR/verifier"

    rm -r $CIRCUIT_DIR/verifier
    cp -r verifier $DST_DIR
    rm $DST_DIR/src/generated/*
    cp $CIRCUIT_DIR/generated/* $DST_DIR/src/generated/
    rm $DST_DIR/README.md
    rm $DST_DIR/expand.sh
    rm $DST_DIR/flamegraph.svg

    sed 's/^name = "verifier"$/name = "'"${CIRCUIT_NAME}_verifier"'"/' verifier/Cargo.toml > $DST_DIR/Cargo.toml
    echo "WARNING: this directory was created by the recreate_verifier.sh script. DO NOT MODIFY BY HAND" >> $DST_DIR/README.md

done