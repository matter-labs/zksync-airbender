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

case "${1:-}" in -h|--help) usage ;; esac

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

# Wrapper: suppress warnings unless --warnings
cargo_run() {
    if $SHOW_WARNINGS; then
        cargo "$@"
    else
        cargo "$@" 2>&1 | grep -v "^warning" | grep -v "^\s*-->" | grep -v "^\s*|" | grep -v "^\s*=" | grep -v "generated .* warning" || true
    fi
}

echo "==> Building RISC-V binaries (blake: ${BLAKE_MODE}, variant: ${VARIANT})"
for circuit in $CIRCUITS; do
    cargo_run build $COMMON_FLAGS --bin "$circuit"
done

# Extract .bin / .elf / .text in parallel
echo "==> Extracting binaries"
for circuit in $CIRCUITS; do
    (
        rm -f ${circuit}.bin ${circuit}.elf ${circuit}.text
        cargo_run objcopy $COMMON_FLAGS --bin "$circuit" -- -O binary ${circuit}.bin
        cargo_run objcopy $COMMON_FLAGS --bin "$circuit" -- -R .text ${circuit}.elf
        cargo_run objcopy $COMMON_FLAGS --bin "$circuit" -- -O binary --only-section=.text ${circuit}.text
    ) &
done
wait

echo "==> Done: $CIRCUITS"
