#!/bin/sh
set -euo pipefail

CIRCUITS=$(ls src/bin/*.rs | sed 's|.*/||;s|\.rs||')
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
