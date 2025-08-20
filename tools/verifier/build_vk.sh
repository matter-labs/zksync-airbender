#!/bin/bash

# updates verification keys
(cd ../cli && CARGO_TARGET_DIR=../verifier/target/vk_cli cargo build --release --no-default-features)

target/vk_cli/release/cli generate-vk --bin ../verifier/universal.bin --machine reduced --output ../verifier/universal.reduced.vk.json &
target/vk_cli/release/cli generate-vk --bin ../verifier/universal.bin --machine reduced-log23 --output ../verifier/universal.reduced_log23.vk.json &
target/vk_cli/release/cli generate-vk --bin ../verifier/universal_no_delegation.bin --machine reduced-final --output ../verifier/universal_no_delegation.final.vk.json &

target/vk_cli/release/cli generate-vk --bin ../verifier/base_layer.bin --machine reduced --output ../verifier/base_layer.reduced.vk.json &
target/vk_cli/release/cli generate-vk --bin ../verifier/recursion_layer.bin --machine reduced --output ../verifier/recursion_layer.reduced.vk.json &
target/vk_cli/release/cli generate-vk --bin ../verifier/recursion_layer.bin --machine reduced-log23 --output ../verifier/recursion_log_23_layer.reduced.vk.json &
target/vk_cli/release/cli generate-vk --bin ../verifier/recursion_layer_no_delegation.bin --machine reduced-final --output ../verifier/recursion_layer_no_delegation.final.vk.json &
target/vk_cli/release/cli generate-vk --bin ../verifier/final_recursion_layer.bin --machine reduced-final --output ../verifier/final_recursion_layer.final.vk.json &

wait