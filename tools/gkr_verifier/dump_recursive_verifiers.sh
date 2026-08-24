#!/bin/sh
# Build the recursive full-statement-verifier RISC-V binaries in every blake
# variant the recursion pipeline (circuit_defs/prover_examples/src/recursion.rs)
# can select at runtime, writing each to a blake-suffixed filename so the
# variants don't overwrite one another:
#
#   fsv_unrolled_base_layer_sec_100      : blake2_with_compression, blake2_g_function
#   fsv_unrolled_recursion_layer_sec_100 : blake2_with_compression, blake2_g_function
#   fsv_unified_recursion_layer_sec_100  : blake2_with_compression, blake2_g_function, special_opcodes_extension
#
# `--sec 100` is the only (and default) security level — the 80-bit mode was removed.
#
# `special_opcodes_extension` does blake inline with the reduced machine's
# tri-add / xor-rotate opcodes — the correct mop-style path for the reduced ISA
# (the `mop_extension` rotate opcode is for SPECIAL_ROTATION machines only and
# would be miscompiled here).
#
# We do NOT build the unified base-layer verifier — the recursion pipeline never
# uses it (it only verifies a unified proof at the recursion layer).
#
# Output files are e.g. `fsv_unrolled_recursion_layer_sec_100_blake2_g_function.{bin,elf,text}`.
# The naming contract lives in `verifier_common::fsv_binaries` (FsvProgram::file_stem);
# drivers load the files via `full_statement_verifier::host_utils::load_fsv_program`,
# selecting variants with the RECURSION_UNROLLED_BLAKE / RECURSION_BRIDGE_BLAKE /
# RECURSION_FINAL_BLAKE environment variables.
#
# Variant defaults to `caches` to match the prover, which runs with
# `use_caches = true`. Override with: ./dump_recursive_verifiers.sh --variant no_caches
set -eu
cd "$(dirname "$0")"

VARIANT="caches"
SEC="100"
while [ $# -gt 0 ]; do
    case "$1" in
        --variant) VARIANT="$2"; shift 2 ;;
        --sec) SEC="$2"; shift 2 ;;
        -h|--help) echo "Usage: $0 [--variant caches|no_caches] [--sec 100]"; exit 0 ;;
        *) echo "unknown argument: $1" >&2; exit 1 ;;
    esac
done

case "$SEC" in
    100)  SEC_LEVELS="100" ;;
    *) echo "ERROR: --sec must be 100 (the 80-bit mode was removed; got '$SEC')" >&2; exit 1 ;;
esac

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
for sec in $SEC_LEVELS; do
    # for mode in blake2_with_compression blake2_g_function; do
    for mode in blake2_with_compression; do
        build_variant "fsv_unrolled_base_layer_sec_${sec}" "${mode}"
        build_variant "fsv_unrolled_recursion_layer_sec_${sec}" "${mode}"
    done
done

# Unified-machine recursion verifier: round, g function, or inline special opcodes.
for sec in $SEC_LEVELS; do
    for mode in blake2_with_compression blake2_g_function special_opcodes_extension; do
        build_variant "fsv_unified_recursion_layer_sec_${sec}" "${mode}"
    done
done

echo "==> all recursive verifier variants built (sec: ${SEC})"
