#!/bin/sh
# Build the recursive full-statement-verifier RISC-V binaries in every soundness mode and blake
# variant the recursion pipeline (prover_pipeline, circuit_defs/prover_examples/src/recursion.rs)
# can select at runtime, each to its own filename so the variants don't overwrite one another,
# then regenerate the manifest that pins their identity:
#
#   pessimistic_conjecture (full_statement_verifiers/):
#     fsv_unrolled_base_layer_sec_100      : blake2_with_compression
#     fsv_unrolled_recursion_layer_sec_100 : blake2_with_compression
#     fsv_unified_recursion_layer_sec_100  : blake2_with_compression, special_opcodes_extension
#     fsv_unified_recursion_layer_sec_100_l1_feeder : special_opcodes_extension
#   ethproofs_soundcalc (full_statement_verifiers/ethproofs_soundcalc/):
#     fsv_unrolled_base_layer_sec_100      : blake2_with_compression
#     fsv_unrolled_recursion_layer_sec_100 : blake2_with_compression
#     fsv_unified_recursion_layer_sec_100  : blake2_with_compression, special_opcodes_extension
#
# `--soundness-mode` selects pessimistic-conjecture, ethproofs-soundcalc or all (default).
# `--sec` defaults to 100, the currently supported security level.
#
# `special_opcodes_extension` does blake inline with the reduced machine's
# tri-add / xor-rotate opcodes — the correct mop-style path for the reduced ISA
# (the `mop_extension` rotate opcode is for SPECIAL_ROTATION machines only and
# would be miscompiled here).
#
# We do NOT build the unified base-layer verifier — the recursion pipeline never
# uses it (it only verifies a unified proof at the recursion layer). The committed
# pessimistic_conjecture one is built by dump_bin.sh; ethproofs_soundcalc has none. There is
# no ethproofs_soundcalc L1 feeder: its schedule exists only in pessimistic_conjecture.
#
# Output files are e.g. `full_statement_verifiers/fsv_unrolled_recursion_layer_sec_100_blake2_with_compression.elf`
# and `full_statement_verifiers/ethproofs_soundcalc/fsv_unrolled_recursion_layer_sec_100_blake2_with_compression.elf`.
# The exact set of guests and their paths is `verifier_common::fsv_binaries::FSV_REGISTRY`;
# drivers load them with `full_statement_verifier::host_utils::load_fsv_exact`, which accepts a
# file only if it matches its row of `full_statement_verifiers/fsv_manifest.txt`. Blake variants
# are selected with the RECURSION_UNROLLED_BLAKE / RECURSION_BRIDGE_BLAKE / RECURSION_FINAL_BLAKE
# environment variables.
#
# Variant defaults to `caches` to match the prover, which runs with
# `use_caches = true`. Override with: ./dump_recursive_verifiers.sh --variant no_caches
# Only the `caches` build is pinned: other variants skip the manifest, so the loader rejects
# them until the canonical binaries are rebuilt.
set -eu
cd "$(dirname "$0")"

VARIANT="caches"
SEC="100"
SOUNDNESS_MODE="all"
while [ $# -gt 0 ]; do
    case "$1" in
        --variant) VARIANT="$2"; shift 2 ;;
        --sec) SEC="$2"; shift 2 ;;
        --soundness-mode) SOUNDNESS_MODE="$2"; shift 2 ;;
        -h|--help) echo "Usage: $0 [--variant caches|no_caches] [--sec 100] [--soundness-mode pessimistic-conjecture|ethproofs-soundcalc|all]"; exit 0 ;;
        *) echo "unknown argument: $1" >&2; exit 1 ;;
    esac
done

case "$SEC" in
    100)  SEC_LEVELS="100" ;;
    *) echo "ERROR: --sec currently supports only 100 (got '$SEC')" >&2; exit 1 ;;
esac

case "$SOUNDNESS_MODE" in
    pessimistic-conjecture) MODES="pessimistic_conjecture" ;;
    ethproofs-soundcalc) MODES="ethproofs_soundcalc" ;;
    all) MODES="pessimistic_conjecture ethproofs_soundcalc" ;;
    *) echo "ERROR: --soundness-mode must be pessimistic-conjecture, ethproofs-soundcalc or all (got '$SOUNDNESS_MODE')" >&2; exit 1 ;;
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
        build_variant "fsv_unified_recursion_layer_sec_100_l1_feeder" "${soundness}" "special_opcodes_extension"
    fi
done

echo "==> all recursive verifier variants built (sec: ${SEC}, soundness: ${SOUNDNESS_MODE})"

if [ "$VARIANT" != "caches" ]; then
    echo "==> NOT regenerating full_statement_verifiers/fsv_manifest.txt: only the caches variant is pinned"
    exit 0
fi

# Regenerate the manifest from every registered guest on disk, with the workspace toolchain
# (the host loader is part of the workspace, not of this guest crate).
echo "==> regenerating full_statement_verifiers/fsv_manifest.txt"
cd ../..
cargo test -p full_statement_verifier --profile cli --features host_utils,verifiers --lib \
    -- --ignored --exact host_utils::fsv::tests::regenerate_fsv_manifest
