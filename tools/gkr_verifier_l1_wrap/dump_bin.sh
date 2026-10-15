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

bin=fsv_unified_recursion_layer_sec_100_l1_feeder_wrap
stem=${bin}_special_opcodes_extension
flags=(--locked --release -Z panic-immediate-abort -Z build-std=core,alloc
       --no-default-features --features special_opcodes_extension
       --config 'build.rustflags=["-A","warnings","-C","link-arg=-Map=wrap-link.map"]'
       -p gkr_verifier_l1_wrap --bin "$bin")
cargo build "${flags[@]}"

# Publish only a complete extraction. The loader consumes unpadded images from
# the same canonical directory as all other FSVs.
out_dir=../gkr_verifier
tmp_dir=$(mktemp -d)
trap 'rm -rf "$tmp_dir"' EXIT
cargo objcopy "${flags[@]}" -- -O binary "$tmp_dir/$stem.bin"
cargo objcopy "${flags[@]}" -- -R .text "$tmp_dir/$stem.elf"
cargo objcopy "${flags[@]}" -- -O binary --only-section=.text "$tmp_dir/$stem.text"
for ext in bin elf text; do
    cp "$tmp_dir/$stem.$ext" "$out_dir/$stem.$ext"
done
