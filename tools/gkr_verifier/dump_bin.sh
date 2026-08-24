#!/bin/sh
set -euo pipefail

# These verifier binaries build on STABLE Rust (pinned to 1.97.1 by the local
# rust-toolchain.toml), but still need a few unstable build options:
#   -Z build-std=core,alloc, -Z panic-immediate-abort (cargo flags below), and
#   the [unstable] section in .cargo/config.toml.
# RUSTC_BOOTSTRAP=1 makes both cargo and rustc treat the stable toolchain as
# nightly for the purpose of gating these options (cargo's release channel
# reads as "nightly" when this is set), so no nightly toolchain is required.
export RUSTC_BOOTSTRAP=1

usage() {
    echo "Usage: $0 [options] [circuits...]"
    echo ""
    echo "Options:"
    echo "  --blake MODE    blake2_with_compression (default), blake2_g_function, mop_extension"
    echo "  --variant VAR   no_caches (default) or caches"
    echo "  --sec LEVEL     only 100 bits is accepted"
    echo "  --warnings      show compiler warnings (suppressed by default)"
    echo "  -h, --help      show this message"
    echo ""
    echo "Circuits:"
    ls src/bin/*.rs 2>/dev/null | sed 's|.*/||;s|\.rs||;s|^|  |'
    echo ""
    echo "Examples:"
    echo "  $0                                                # all circuits, defaults"
    echo "  $0 --sec 100                                       # only the 100-bit security leve individual verifiers"
    echo "  $0 --blake mop_extension                          # all circuits, mop_extension"
    echo "  $0 --blake mop_extension blake2_with_extended_control  # single circuit"
    echo "  $0 --variant caches                               # all circuits, cached variant"
    exit 1
}

BLAKE_MODE="blake2_with_compression"
VARIANT="no_caches"
SEC="100"
SHOW_WARNINGS=false

while [ $# -gt 0 ]; do
    case "$1" in
        -h|--help) usage ;;
        --blake) BLAKE_MODE="$2"; shift 2 ;;
        --variant) VARIANT="$2"; shift 2 ;;
        --sec) SEC="$2"; shift 2 ;;
        --warnings) SHOW_WARNINGS=true; shift ;;
        *) break ;;
    esac
done

case "$SEC" in
    100) ;;
    *) echo "ERROR: --sec must be 100 (the 80-bit mode was removed; got '$SEC')" >&2; exit 1 ;;
esac

# Remaining args are circuits, or default to all (filtered by --sec).
if [ $# -gt 0 ]; then
    CIRCUITS="$@"
else
    ALL=$(ls src/bin/*.rs | sed 's|.*/||;s|\.rs||')
    case "$SEC" in
        100)  CIRCUITS=$(echo "$ALL" | grep '_sec_100$') ;;
    esac
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
    trap 'if [ -f .cargo/config.toml.bak ]; then mv .cargo/config.toml.bak .cargo/config.toml; fi' EXIT
fi

echo "==> Building RISC-V binaries (blake: ${BLAKE_MODE}, variant: ${VARIANT})"
BIN_FLAGS=""
for circuit in $CIRCUITS; do
    BIN_FLAGS="${BIN_FLAGS} --bin ${circuit}"
done
cargo build $COMMON_FLAGS $BIN_FLAGS

# Extract .bin / .elf / .text in parallel
echo "==> Extracting binaries"
log_dir=$(mktemp -d)
pids=""
for circuit in $CIRCUITS; do
    (
        rm -f ${circuit}.bin ${circuit}.elf ${circuit}.text
        cargo objcopy $COMMON_FLAGS --bin "$circuit" -- -O binary ${circuit}.bin
        cargo objcopy $COMMON_FLAGS --bin "$circuit" -- -R .text ${circuit}.elf
        cargo objcopy $COMMON_FLAGS --bin "$circuit" -- -O binary --only-section=.text ${circuit}.text
    ) > "${log_dir}/${circuit}.log" 2>&1 &
    pids="${pids} $!"
done

rc=0
for pid in $pids; do
    wait "$pid" || rc=1
done

if [ "$rc" -ne 0 ]; then
    echo "ERROR: binary extraction failed." >&2
    for circuit in $CIRCUITS; do
        if [ ! -s "${circuit}.bin" ] || [ ! -s "${circuit}.elf" ] || [ ! -s "${circuit}.text" ]; then
            echo "  --- ${circuit} ---" >&2
            tail -n 10 "${log_dir}/${circuit}.log" >&2
        fi
    done
    echo "Hint: \"Could not find tool: objcopy\" means the llvm-tools component is missing — run: rustup component add llvm-tools" >&2
    rm -rf "$log_dir"
    exit 1
fi
rm -rf "$log_dir"

echo "==> Done: $CIRCUITS"
