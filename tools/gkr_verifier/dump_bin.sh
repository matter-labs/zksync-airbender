#!/bin/sh
set -euo pipefail

CIRCUITS="add_sub_lui_auipc_mop jump_branch_slt shift_binop mem_word_only mem_subword_only bigint_with_extended_control blake2_with_extended_control keccak_special5"
COMMON_FLAGS="--release -Z panic-immediate-abort -Z build-std=core,alloc"

echo "==> Building all RISC-V binaries"
cargo build $COMMON_FLAGS --bins

# Extract .bin / .elf / .text in parallel
echo "==> Extracting binaries"
for circuit in $CIRCUITS; do
    (
        rm -f ${circuit}.bin ${circuit}.elf ${circuit}.text
        cargo objcopy $COMMON_FLAGS --bin "$circuit" -- -O binary ${circuit}.bin
        cargo objcopy $COMMON_FLAGS --bin "$circuit" -- -R .text ${circuit}.elf
        cargo objcopy $COMMON_FLAGS --bin "$circuit" -- -O binary --only-section=.text ${circuit}.text
    ) &
done
wait

echo "==> All binaries built"
