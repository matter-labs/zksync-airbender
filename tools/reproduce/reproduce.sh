#!/bin/bash

# Make sure to run from the main zksync-airbender directory.

set -euo pipefail  # Exit on any error

export DOCKER_DEFAULT_PLATFORM=linux/amd64

SOURCE_DATE_EPOCH="1700000000"
export SOURCE_DATE_EPOCH

# create a fresh docker
docker build -t airbender-verifiers \
  --build-arg SOURCE_DATE_EPOCH="$SOURCE_DATE_EPOCH" \
  -f tools/reproduce/Dockerfile .

docker create --name verifiers airbender-verifiers

# Full-statement verifiers and the standalone circuit verifiers used by the
# cost-model drift guard. Keep both sets in sync with the generated Rust code.
STEMS=(
    fsv_unrolled_base_layer_sec_100_blake2_with_compression
    fsv_unrolled_recursion_layer_sec_100_blake2_with_compression
    fsv_unified_recursion_layer_sec_100_blake2_with_compression
    fsv_unified_recursion_layer_sec_100_special_opcodes_extension
    fsv_unified_recursion_layer_sec_100_l1_feeder_special_opcodes_extension
    add_sub_lui_auipc_mop_sec_100
    jump_branch_slt_sec_100
    shift_binop_sec_100
    unsigned_mul_div_sec_100
    mem_word_only_sec_100
    mem_subword_only_sec_100
    inits_and_teardowns_sec_100
    blake2_with_extended_control_sec_100
    bigint_with_extended_control_sec_100
    keccak_special5_sec_100
    blake2_g_function_sec_100
)

FILES=()
for STEM in "${STEMS[@]}"; do
    for EXT in bin elf text; do
        FILES+=("${STEM}.${EXT}")
    done
done

for FILE in "${FILES[@]}"; do
    docker cp verifiers:/zksync-airbender/tools/gkr_verifier/$FILE tools/gkr_verifier/
    md5sum tools/gkr_verifier/$FILE
done


docker rm verifiers
