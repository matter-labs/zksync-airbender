#!/bin/bash

# Make sure to run from the main zksync-airbender directory.

set -e  # Exit on any error

export DOCKER_DEFAULT_PLATFORM=linux/amd64

# create a fresh docker
docker build -t airbender-verifiers  -f tools/reproduce/Dockerfile .

docker create --name verifiers airbender-verifiers

FILES=(
    base_layer.bin
    recursion_layer.bin
    recursion_log_23_layer.bin
    recursion_layer_no_delegation.bin
    final_recursion_layer.bin
    base_layer_with_output.bin
    recursion_layer_with_output.bin
    recursion_log_23_layer_with_output.bin
    recursion_layer_no_delegation_with_output.bin
    final_recursion_layer_with_output.bin
    universal.bin
    universal_no_delegation.bin
    base_layer.reduced.vk.json
    universal.reduced.vk.json
    universal_no_delegation.final.vk.json
    recursion_layer.reduced.vk.json
    recursion_layer_no_delegation.final.vk.json
    final_recursion_layer.final.vk.json
    universal.reduced_log23.vk.json
    recursion_log_23_layer.reduced.vk.json
)

for FILE in "${FILES[@]}"; do
    docker cp verifiers:/zksync-airbender/tools/verifier/$FILE tools/verifier/
    md5sum tools/verifier/$FILE
done


docker rm verifiers