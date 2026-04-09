#!/bin/sh
set -euo pipefail

# BLAKE_MODE: blake2_with_compression (default), blake2_g_function, mop_extension
BLAKE_MODE="${BLAKE_MODE:-blake2_with_compression}"

# GKR_VARIANT: "no_caches" (default) or "" (cached)
GKR_VARIANT="${GKR_VARIANT:-no_caches}"

FEATURES="${BLAKE_MODE}"
if [ -n "$GKR_VARIANT" ]; then
    FEATURES="${FEATURES},${GKR_VARIANT}"
fi

CIRCUITS=$(ls src/bin/*.rs | sed 's|.*/||;s|\.rs||')
COMMON_FLAGS="--release -Z panic-immediate-abort -Z build-std=core,alloc --no-default-features --features ${FEATURES}"

echo "==> Building all RISC-V binaries (blake: ${BLAKE_MODE}, variant: ${GKR_VARIANT:-cached})"
cargo build $COMMON_FLAGS --bins

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

echo "==> All binaries built (blake: ${BLAKE_MODE}, variant: ${GKR_VARIANT:-cached})"
