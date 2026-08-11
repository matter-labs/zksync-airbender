#!/bin/bash

# Make sure to run from the main zksync-airbender directory.

set -euo pipefail  # Exit on any error, unset variable, or failure inside a pipeline

export DOCKER_DEFAULT_PLATFORM=linux/amd64

# SOURCE_DATE_EPOCH is a fixed constant in the Dockerfile, deliberately not derived from
# git: anything tied to the commit changes on every commit, so artifacts committed at one
# commit could never reproduce at the next and check_verifiers would fail on unrelated
# changes. A constant is what makes the committed artifacts verifiable over time.

# Set AIRBENDER_BUILD_JOBS=N to cap how many verifier builds run at once; the default of
# 0 launches them all, as CI does. Lower it if the build is being OOM-killed.
# create a fresh docker
docker build -t airbender-verifiers \
  --build-arg AIRBENDER_BUILD_JOBS="${AIRBENDER_BUILD_JOBS:-0}" \
  --build-arg AIRBENDER_VK_JOBS="${AIRBENDER_VK_JOBS:-}" \
  -f tools/reproduce/Dockerfile .

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