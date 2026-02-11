#!/bin/bash

# Make sure to run from the main zksync-airbender directory.

set -e  # Exit on any error

export DOCKER_DEFAULT_PLATFORM=linux/amd64

# create a fresh docker
docker build -t airbender-verifiers  -f tools/reproduce/Dockerfile .

docker create --name verifiers airbender-verifiers

FILES=(
    recursion_in_unified_layer.bin
    recursion_in_unrolled_layer.bin
    recursion_in_unified_layer_security_100_bits.bin
    recursion_in_unrolled_layer_security_100_bits.bin
)

for FILE in "${FILES[@]}"; do
    docker cp verifiers:/zksync-airbender/tools/verifier/$FILE tools/verifier/
    md5sum tools/verifier/$FILE
done


docker rm verifiers
