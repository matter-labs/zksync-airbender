#!/bin/sh

rm base_layer.bin
rm recursion_layer.bin
rm final_recursion_layer.bin
rm base_layer_with_output.bin
rm recursion_layer_with_output.bin
rm final_recursion_layer_with_output.bin
rm universal.bin
rm universal_no_delegation.bin
rm verifier_test.bin

# Build something simple to check for errors
# cargo build --release  -Z build-std=core,panic_abort,alloc -Z build-std-features=panic_immediate_abort  --features base_layer --no-default-features

#cargo build -Z build-std=core,panic_abort,alloc -Z build-std-features=panic_immediate_abort --release --no-default-features --features=base_layer
CARGO_TARGET_DIR=target/one cargo objcopy --release  -Z build-std=core,panic_abort,alloc -Z build-std-features=panic_immediate_abort  --features base_layer --no-default-features -- -O binary base_layer.bin &

#cargo build -Z build-std=core,panic_abort,alloc -Z build-std-features=panic_immediate_abort --release --no-default-features --features=recursion_step
CARGO_TARGET_DIR=target/two cargo objcopy --release  -Z build-std=core,panic_abort,alloc -Z build-std-features=panic_immediate_abort  --features recursion_step --no-default-features -- -O binary recursion_layer.bin &

#cargo build -Z build-std=core,panic_abort,alloc -Z build-std-features=panic_immediate_abort --release --no-default-features --features=recursion_step
CARGO_TARGET_DIR=target/three cargo objcopy --release  -Z build-std=core,panic_abort,alloc -Z build-std-features=panic_immediate_abort  --features recursion_step_no_delegation --no-default-features -- -O binary recursion_layer_no_delegation.bin &

#cargo build -Z build-std=core,panic_abort,alloc -Z build-std-features=panic_immediate_abort --release --no-default-features --features=recursion_step
CARGO_TARGET_DIR=target/four cargo objcopy --release  -Z build-std=core,panic_abort,alloc -Z build-std-features=panic_immediate_abort  --features final_recursion_step --no-default-features -- -O binary final_recursion_layer.bin &

#cargo build --release --no-default-features --features=base_layer,panic_output
CARGO_TARGET_DIR=target/five cargo objcopy --release --features base_layer,panic_output --no-default-features -- -O binary base_layer_with_output.bin &

#cargo build --release --no-default-features --features=recursion_step,panic_output
CARGO_TARGET_DIR=target/six cargo objcopy --release --features recursion_step,panic_output --no-default-features -- -O binary recursion_layer_with_output.bin &

#cargo build --release --no-default-features --features=recursion_step,panic_output
CARGO_TARGET_DIR=target/seven cargo objcopy --release --features recursion_step_no_delegation,panic_output --no-default-features -- -O binary recursion_layer_no_delegation_with_output.bin &

#cargo build --release --no-default-features --features=final_recursion_step,panic_output
CARGO_TARGET_DIR=target/eight cargo objcopy --release --features final_recursion_step,panic_output --no-default-features -- -O binary final_recursion_layer_with_output.bin &

# cargo biild --release -Z build-std=core,panic_abort,alloc --features universal_circuit,panic_output --no-default-features
CARGO_TARGET_DIR=target/nine cargo objcopy --release -Z build-std=core,panic_abort,alloc --features universal_circuit,panic_output --no-default-features -- -O binary universal.bin &

# cargo build --release -Z build-std=core,panic_abort,alloc --features universal_circuit_no_delegation,panic_output --no-default-features
CARGO_TARGET_DIR=target/ten cargo objcopy --release -Z build-std=core,panic_abort,alloc --features universal_circuit_no_delegation,panic_output --no-default-features -- -O binary universal_no_delegation.bin &

wait

# now update verification keys.
./build_vk.sh