#!/bin/bash
set -euo pipefail

cd "$(dirname "$0")"
export RUSTC_BOOTSTRAP=1

# This package deliberately builds separately from gkr_verifier: Cargo feature
# unification must never enable the wrap layout on the regular verifier guests.
while [ "$#" -gt 0 ]; do
    case "$1" in
        --blake)
            [ "${2:-}" = special_opcodes_extension ] || { echo 'wrap requires special_opcodes_extension' >&2; exit 1; }
            shift 2 ;;
        --variant)
            [ "${2:-}" = caches ] || { echo 'wrap requires caches' >&2; exit 1; }
            shift 2 ;;
        *) echo "Usage: $0 [--blake special_opcodes_extension] [--variant caches]" >&2; exit 1 ;;
    esac
done

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

bin=fsv_unified_recursion_layer_sec_100_l1_feeder_wrap
stem=${bin}_special_opcodes_extension
flags=(--locked --release -Z panic-immediate-abort -Z build-std=core,alloc
       --no-default-features --features special_opcodes_extension
       --config "build.rustflags=[${REMAP_ARGS},\"-A\",\"warnings\",\"-C\",\"link-arg=-Map=wrap-link.map\"]"
       -p gkr_verifier_l1_wrap --bin "$bin")
cargo build "${flags[@]}"

# Publish only a complete extraction. The loader consumes unpadded images from
# the same canonical directory as all other FSVs.
out_dir=../gkr_verifier
tmp_dir=$(mktemp -d)
trap 'rm -rf "$tmp_dir"' EXIT
cargo objcopy "${flags[@]}" -- -O binary "$tmp_dir/$stem.bin"
cargo objcopy "${flags[@]}" -- -R .text -R .comment "$tmp_dir/$stem.elf"
cargo objcopy "${flags[@]}" -- -O binary --only-section=.text "$tmp_dir/$stem.text"
for ext in bin elf text; do
    cp "$tmp_dir/$stem.$ext" "$out_dir/$stem.$ext"
done
