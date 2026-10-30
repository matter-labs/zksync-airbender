#!/usr/bin/env bash
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
    echo "  --mode MODE     per-circuit verifiers of one soundness mode only"
    echo "                  (pessimistic_conjecture | ethproofs_soundcalc); default: both."
    echo "                  pessimistic_conjecture also drops the ethproofs_soundcalc full"
    echo "                  statement verifiers"
    echo "  --warnings      show compiler warnings (suppressed by default)"
    echo "  -h, --help      show this message"
    echo ""
    echo "Binaries (cargo bin names):"
    echo "  full statement verifiers -> full_statement_verifiers/<name>.elf:"
    ls src/bin/full_statement_verifiers/*.rs 2>/dev/null | sed 's|.*/||;s|\.rs||;s|^|    |'
    echo "  ethproofs_soundcalc full statement verifiers <name>_ethproofs_soundcalc"
    echo "    -> full_statement_verifiers/ethproofs_soundcalc/<name>.elf:"
    ls src/bin/full_statement_verifiers/ethproofs_soundcalc/*.rs 2>/dev/null | sed 's|.*/||;s|\.rs||;s|^|    |;s|$|_ethproofs_soundcalc|'
    echo "  per-circuit verifiers <circuit>_<mode> -> circuit_verifiers/<mode>/<circuit>.elf:"
    for m in src/bin/circuit_verifiers/*/; do
        m=$(basename "$m")
        ls "src/bin/circuit_verifiers/$m"/*.rs 2>/dev/null | sed "s|.*/||;s|\.rs||;s|^|    |;s|\$|_$m|"
    done
    echo ""
    echo "Examples:"
    echo "  $0                                                # all circuits, defaults"
    echo "  $0 --sec 100                                       # only the 100-bit security level individual verifiers"
    echo "  $0 --blake mop_extension                          # all circuits, mop_extension"
    echo "  $0 --mode pessimistic_conjecture                   # only the production-mode circuit verifiers"
    echo "  $0 --blake mop_extension blake2_with_extended_control_pessimistic_conjecture  # single binary"
    echo "  $0 --variant caches                               # all circuits, cached variant"
    exit 1
}

BLAKE_MODE="blake2_with_compression"
VARIANT="no_caches"
SEC="100"
MODE_FILTER=""
SHOW_WARNINGS=false

while [ $# -gt 0 ]; do
    case "$1" in
        -h|--help) usage ;;
        --blake) BLAKE_MODE="$2"; shift 2 ;;
        --variant) VARIANT="$2"; shift 2 ;;
        --sec) SEC="$2"; shift 2 ;;
        --mode) MODE_FILTER="$2"; shift 2 ;;
        --warnings) SHOW_WARNINGS=true; shift ;;
        *) break ;;
    esac
done

case "$SEC" in
    100) ;;
    *) echo "ERROR: --sec currently supports only 100 (got '$SEC')" >&2; exit 1 ;;
esac

# Binary name -> output path. Per-circuit verifiers are named `<circuit>_<mode>` and land in
# `circuit_verifiers/<mode>/<circuit>.elf`; pessimistic-conjecture full statement verifiers keep
# their name in `full_statement_verifiers/`, ethproofs-soundcalc ones (`fsv_<name>_ethproofs_soundcalc`)
# land in `full_statement_verifiers/ethproofs_soundcalc/fsv_<name>.elf`.
out_path() {
    case "$1" in
        fsv_*_ethproofs_soundcalc) echo "full_statement_verifiers/ethproofs_soundcalc/${1%_ethproofs_soundcalc}.elf" ;;
        fsv_*) echo "full_statement_verifiers/$1.elf" ;;
        *_pessimistic_conjecture) echo "circuit_verifiers/pessimistic_conjecture/${1%_pessimistic_conjecture}.elf" ;;
        *_ethproofs_soundcalc) echo "circuit_verifiers/ethproofs_soundcalc/${1%_ethproofs_soundcalc}.elf" ;;
        *) echo "ERROR: unknown binary naming for $1" >&2; exit 1 ;;
    esac
}

# Remaining args are binaries (cargo bin names), or default to every binary of the level
# (every full statement verifier and the per-circuit verifiers of every soundness mode, or of
# `--mode` only).
if [ $# -gt 0 ]; then
    CIRCUITS="$@"
else
    FSV=$(ls src/bin/full_statement_verifiers/*.rs | sed 's|.*/||;s|\.rs||' | grep "_sec_${SEC}")
    if [ "$MODE_FILTER" != "pessimistic_conjecture" ]; then
        FSV="$FSV $(ls src/bin/full_statement_verifiers/ethproofs_soundcalc/*.rs | sed 's|.*/||;s|\.rs||;s|$|_ethproofs_soundcalc|' | grep "_sec_${SEC}_")"
    fi
    PER_CIRCUIT=""
    for m in src/bin/circuit_verifiers/*/; do
        m=$(basename "$m")
        if [ -n "$MODE_FILTER" ] && [ "$m" != "$MODE_FILTER" ]; then continue; fi
        PER_CIRCUIT="$PER_CIRCUIT $(ls "src/bin/circuit_verifiers/$m"/*.rs | sed "s|.*/||;s|\.rs||;s|\$|_$m|")"
    done
    CIRCUITS="$FSV $PER_CIRCUIT"
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

# Reproducibility across machines: the checkout root, the toolchain sysroot (build-std
# compiles core/alloc from its rust-src) and the cargo registry would otherwise leak into
# DWARF and `source_filename` as absolute host paths. Remap them to fixed names. These
# prefixes are only known at build time, so they are passed here via `--config`, whose
# arrays are appended after config.toml's rustflags. Symbol names are pinned separately by
# rustc_wrapper.sh (see .cargo/config.toml).
REPO_ROOT=$(cd ../.. && pwd -P)
SYSROOT=$(rustc --print sysroot)
CARGO_REGISTRY="${CARGO_HOME:-$HOME/.cargo}/registry/src"
for p in "$REPO_ROOT" "$SYSROOT" "$CARGO_REGISTRY"; do
    case "$p" in
        *[[:space:]\"]*) echo "ERROR: path with whitespace or quotes is not supported: $p" >&2; exit 1 ;;
    esac
done
REMAP_ARGS="\"--remap-path-prefix=${REPO_ROOT}=/src\",\"--remap-path-prefix=${SYSROOT}=/rustc-sysroot\""
# Every registry index dir (sparse and git protocol use different names) maps to one prefix.
for d in "$CARGO_REGISTRY"/*; do
    [ -d "$d" ] || continue
    REMAP_ARGS="${REMAP_ARGS},\"--remap-path-prefix=${d}=/cargo-registry\""
done

# The canonical fsv_* binaries keep config.toml's `-C debuginfo=0` (the reproducible set,
# #417). Every other binary is a per-circuit verifier that the transpiler tests profile, and
# the flamegraph symbolizer reads only DWARF, so those re-enable debug info: `--config` arrays
# are appended after config.toml's rustflags, so this `-C debuginfo=2` wins. They build in their
# own target dir (CARGO_TARGET_DIR: `cargo objcopy` rejects --target-dir) so the two flag sets
# don't evict each other's artifacts.
FSV_FLAGS="--config build.rustflags=[${REMAP_ARGS}]"
PROFILED_FLAGS="--config build.rustflags=[${REMAP_ARGS},\"-C\",\"debuginfo=2\"]"
PROFILED_TARGET_DIR="target/profiled"
is_fsv() {
    case "$1" in
        fsv_*) return 0 ;;
        *) return 1 ;;
    esac
}

echo "==> Building RISC-V binaries (blake: ${BLAKE_MODE}, variant: ${VARIANT})"
FSV_BIN_FLAGS=""
PROFILED_BIN_FLAGS=""
for circuit in $CIRCUITS; do
    if is_fsv "$circuit"; then
        FSV_BIN_FLAGS="${FSV_BIN_FLAGS} --bin ${circuit}"
    else
        PROFILED_BIN_FLAGS="${PROFILED_BIN_FLAGS} --bin ${circuit}"
    fi
done
if [ -n "$FSV_BIN_FLAGS" ]; then
    cargo build $COMMON_FLAGS $FSV_FLAGS $FSV_BIN_FLAGS
fi
if [ -n "$PROFILED_BIN_FLAGS" ]; then
    CARGO_TARGET_DIR="$PROFILED_TARGET_DIR" cargo build $COMMON_FLAGS $PROFILED_FLAGS $PROFILED_BIN_FLAGS
fi

# Extract the ELFs in parallel (the host reads .text and the flat ROM image from them)
echo "==> Extracting binaries"
log_dir=$(mktemp -d)
pids=""
for circuit in $CIRCUITS; do
    (
        if is_fsv "$circuit"; then
            EXTRA_FLAGS="$FSV_FLAGS"
        else
            EXTRA_FLAGS="$PROFILED_FLAGS"
            export CARGO_TARGET_DIR="$PROFILED_TARGET_DIR"
        fi
        out=$(out_path "$circuit")
        mkdir -p "$(dirname "$out")"
        rm -f "$out"
        # .comment holds the rustc/LLD build strings, which differ between the dist
        # toolchains of different hosts; drop it so the .elf is reproducible too.
        cargo objcopy $COMMON_FLAGS $EXTRA_FLAGS --bin "$circuit" -- -R .comment "$out"
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
        if [ ! -s "$(out_path "$circuit")" ]; then
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
