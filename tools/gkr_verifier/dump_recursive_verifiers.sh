#!/bin/sh
# Build the recursive full-statement verifier guests in both soundness modes.
set -eu
cd "$(dirname "$0")"

VARIANT="caches"
SEC="100"
MODES="pessimistic_conjecture ethproofs_soundcalc"
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
    *) echo "ERROR: --sec currently supports only 100 (got '$SEC')" >&2; exit 1 ;;
esac

# build_variant <fsv name> <soundness mode> <blake mode>
build_variant() {
    circuit="$1"
    soundness="$2"
    mode="$3"
    case "$soundness" in
        pessimistic_conjecture) bin="${circuit}"; dir="full_statement_verifiers" ;;
        ethproofs_soundcalc) bin="${circuit}_ethproofs_soundcalc"; dir="full_statement_verifiers/ethproofs_soundcalc" ;;
    esac
    echo "==> building ${circuit} (soundness: ${soundness}, blake: ${mode}, variant: ${VARIANT})"
    ./dump_bin.sh --blake "${mode}" --variant "${VARIANT}" "${bin}"
    mv -f "${dir}/${circuit}.elf" "${dir}/${circuit}_${mode}.elf"
    echo "    wrote ${dir}/${circuit}_${mode}.elf"
}

for soundness in $MODES; do
    for sec in $SEC_LEVELS; do
        # Unrolled-machine recursive verifiers: blake round function.
        for mode in blake2_with_compression; do
            build_variant "fsv_unrolled_base_layer_sec_${sec}" "${soundness}" "${mode}"
            build_variant "fsv_unrolled_recursion_layer_sec_${sec}" "${soundness}" "${mode}"
        done
        # Unified-machine recursion verifier: round or inline special opcodes.
        for mode in blake2_with_compression special_opcodes_extension; do
            build_variant "fsv_unified_recursion_layer_sec_${sec}" "${soundness}" "${mode}"
        done
    done
    if [ "$soundness" = "pessimistic_conjecture" ]; then
        build_variant "fsv_unified_recursion_layer_sec_100_compression" "${soundness}" "special_opcodes_extension"
    fi
done

echo "==> all recursive verifier variants built (sec: ${SEC})"
