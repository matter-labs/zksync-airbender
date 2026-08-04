#!/bin/bash

# Make sure to run from the main zksync-airbender directory.

set -e  # Exit on any error

export DOCKER_DEFAULT_PLATFORM=linux/amd64

# create a fresh docker
docker build -t airbender-verifiers  -f tools/reproduce/Dockerfile .

docker create --name verifiers airbender-verifiers

# Full-statement-verifier (fsv_) build artifacts, exactly the set produced by
# tools/gkr_verifier/dump_recursive_verifiers.sh (unrolled base+recursion in the
# blake2_with_compression variant; unified recursion in blake2_with_compression,
# blake2_g_function, and special_opcodes_extension), at both 80- and 100-bit
# security levels.
STEMS=(
    fsv_unrolled_base_layer_sec_80_blake2_with_compression
    fsv_unrolled_base_layer_sec_100_blake2_with_compression
    fsv_unrolled_recursion_layer_sec_80_blake2_with_compression
    fsv_unrolled_recursion_layer_sec_100_blake2_with_compression
    fsv_unified_recursion_layer_sec_80_blake2_with_compression
    fsv_unified_recursion_layer_sec_80_blake2_g_function
    fsv_unified_recursion_layer_sec_80_special_opcodes_extension
    fsv_unified_recursion_layer_sec_100_blake2_with_compression
    fsv_unified_recursion_layer_sec_100_blake2_g_function
    fsv_unified_recursion_layer_sec_100_special_opcodes_extension
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
