#!/bin/sh
set -euo pipefail

usage() {
    echo "Usage: $0 [options] [circuits...]"
    echo ""
    echo "Options:"
    echo "  --blake MODE    blake2_with_compression (default), blake2_g_function, mop_extension"
    echo "  --variant VAR   no_caches (default) or caches"
    echo "  --warnings      show compiler warnings (suppressed by default)"
    echo "  -h, --help      show this message"
    echo ""
    echo "Circuits:"
    ls src/bin/*.rs 2>/dev/null | sed 's|.*/||;s|\.rs||;s|^|  |'
    echo ""
    echo "Examples:"
    echo "  $0                                                # all circuits, defaults"
    echo "  $0 --blake mop_extension                          # all circuits, mop_extension"
    echo "  $0 --blake mop_extension blake2_with_extended_control  # single circuit"
    echo "  $0 --variant caches                               # all circuits, cached variant"
    exit 1
}

BLAKE_MODE="blake2_with_compression"
VARIANT="no_caches"
SHOW_WARNINGS=false

while [ $# -gt 0 ]; do
    case "$1" in
        -h|--help) usage ;;
        --blake) BLAKE_MODE="$2"; shift 2 ;;
        --variant) VARIANT="$2"; shift 2 ;;
        --warnings) SHOW_WARNINGS=true; shift ;;
        *) break ;;
    esac
done

# Remaining args are circuits, or default to all
if [ $# -gt 0 ]; then
    CIRCUITS="$@"
else
    CIRCUITS=$(ls src/bin/*.rs | sed 's|.*/||;s|\.rs||')
fi

FEATURES="${BLAKE_MODE}"
if [ "$VARIANT" = "no_caches" ]; then
    FEATURES="${FEATURES},no_caches"
fi

COMMON_FLAGS="--release -Z panic-immediate-abort -Z build-std=core,alloc --no-default-features --features ${FEATURES}"

# Suppress warnings by appending -Awarnings to .cargo/config.toml rustflags.
# Can't use RUSTFLAGS env var because it replaces (not merges) config.toml rustflags.
if ! $SHOW_WARNINGS; then
    sed -i.bak '/"-C", "force-frame-pointers",/a\
  "-A", "warnings",' .cargo/config.toml
    trap 'mv .cargo/config.toml.bak .cargo/config.toml' EXIT
fi

echo "==> Building RISC-V binaries (blake: ${BLAKE_MODE}, variant: ${VARIANT})"
BIN_FLAGS=""
for circuit in $CIRCUITS; do
    BIN_FLAGS="${BIN_FLAGS} --bin ${circuit}"
done
cargo build $COMMON_FLAGS $BIN_FLAGS

# Extract .bin / .elf / .text in parallel
echo "==> Extracting binaries"
for circuit in $CIRCUITS; do
    (
        rm -f ${circuit}.bin ${circuit}.elf ${circuit}.text
        cargo objcopy $COMMON_FLAGS --bin "$circuit" -- -O binary ${circuit}.bin
        cargo objcopy $COMMON_FLAGS --bin "$circuit" -- -R .text ${circuit}.elf
        cargo objcopy $COMMON_FLAGS --bin "$circuit" -- -O binary --only-section=.text ${circuit}.text
    ) > /dev/null 2>&1 &
done
wait

echo "==> Done: $CIRCUITS"
