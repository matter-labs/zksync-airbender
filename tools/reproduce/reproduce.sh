#!/bin/bash

# Make sure to run from the main zksync-airbender directory.

set -e  # Exit on any error

# create a fresh docker
docker build -t airbender-verifiers  -f tools/reproduce/Dockerfile .

docker create --name verifiers airbender-verifiers

FILES=(
    base_layer.bin
    recursion_layer.bin
    final_recursion_layer.bin
    base_layer_with_output.bin
    recursion_layer_with_output.bin
    final_recursion_layer_with_output.bin
    universal.bin
    universal_no_delegation.bin
    universal.reduced.vk.json
    universal_no_delegation.final.vk.json
    recursion_layer.reduced.vk.json
    recursion_layer_no_delegation.final.vk.json
    final_recursion_layer.final.vk.json
)

for FILE in "${FILES[@]}"; do
    docker cp verifiers:/zksync-airbender/tools/verifier/$FILE tools/verifier/
    md5sum tools/verifier/$FILE
done


docker rm verifiers