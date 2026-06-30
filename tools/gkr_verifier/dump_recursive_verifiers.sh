#!/bin/sh
# Build the recursive full-statement-verifier RISC-V binaries in every blake
# variant the recursion pipeline (circuit_defs/prover_examples/src/recursion.rs)
# can select at runtime, writing each to a blake-suffixed filename so the
# variants don't overwrite one another:
#
#   fsv_unrolled_base_layer_sec_80      : blake2_with_compression, blake2_g_function
#   fsv_unrolled_recursion_layer_sec_80 : blake2_with_compression, blake2_g_function
#   fsv_unified_recursion_layer_sec_80  : blake2_with_compression, blake2_g_function, mop_extension
#
# We do NOT build the unified base-layer verifier — the recursion pipeline never
# uses it (it only verifies a unified proof at the recursion layer).
#
# Output files are e.g. `fsv_unrolled_recursion_layer_sec_80_blake2_g_function.{bin,elf,text}`,
# which is what `recursion.rs::fsv_program_blake` loads based on the
# RECURSION_UNROLLED_BLAKE / RECURSION_UNIFIED_BLAKE environment variables.
#
# Variant defaults to `caches` to match the prover, which runs with
# `use_caches = true`. Override with: ./dump_recursive_verifiers.sh --variant no_caches
set -eu
cd "$(dirname "$0")"

VARIANT="caches"
while [ $# -gt 0 ]; do
    case "$1" in
        --variant) VARIANT="$2"; shift 2 ;;
        -h|--help) echo "Usage: $0 [--variant caches|no_caches]"; exit 0 ;;
        *) echo "unknown argument: $1" >&2; exit 1 ;;
    esac
done

build_variant() {
    circuit="$1"
    mode="$2"
    echo "==> building ${circuit} (blake: ${mode}, variant: ${VARIANT})"
    ./dump_bin.sh --blake "${mode}" --variant "${VARIANT}" "${circuit}"
    for ext in bin elf text; do
        mv -f "${circuit}.${ext}" "${circuit}_${mode}.${ext}"
    done
    echo "    wrote ${circuit}_${mode}.{bin,elf,text}"
}

# Unrolled-machine recursive verifiers: blake round function or blake g function.
for mode in blake2_with_compression blake2_g_function; do
    build_variant fsv_unrolled_base_layer_sec_80 "${mode}"
    build_variant fsv_unrolled_recursion_layer_sec_80 "${mode}"
done

# Unified-machine recursion verifier: round, g function, or mop extension.
for mode in blake2_with_compression blake2_g_function mop_extension; do
    build_variant fsv_unified_recursion_layer_sec_80 "${mode}"
done

echo "==> all recursive verifier variants built"
