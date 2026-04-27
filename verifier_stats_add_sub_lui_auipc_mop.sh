#!/usr/bin/env bash
set -euo pipefail

REFRESH=false
NOCACHES=false
for arg in "$@"; do
    case "$arg" in
        --refresh) REFRESH=true ;;
        # Use the no-caches circuit/verifier variant. Currently broken upstream
        # (regenerated no-caches code disagrees with the committed proof.json),
        # so leave it off until upstream regenerates a matching proof.
        --nocaches) NOCACHES=true ;;
        *) echo "unknown arg: $arg" >&2; exit 1 ;;
    esac
done

REGEN_FEATURES=()
TEST_FEATURES="verifier_stats,blake2_with_compression"
DUMP_VARIANT="caches"
if $NOCACHES; then
    REGEN_FEATURES=(--features no_caches)
    TEST_FEATURES="${TEST_FEATURES},no_caches"
    DUMP_VARIANT="no_caches"
fi

if $REFRESH; then
    env RUSTFLAGS=-Awarnings cargo test -p verifier_generator ${REGEN_FEATURES[@]+"${REGEN_FEATURES[@]}"} --test generate_verifiers add_sub_lui_auipc_mop
fi

env RUSTFLAGS=-Awarnings cargo test -p verifier --features "${TEST_FEATURES}" --test native -- add_sub_lui_auipc_mop --nocapture

if $REFRESH; then
    (cd tools/gkr_verifier && ./dump_bin.sh --stats --variant "${DUMP_VARIANT}" add_sub_lui_auipc_mop)
fi

env RUSTFLAGS=-Awarnings cargo test --profile test-release -p verifier --features "${TEST_FEATURES}" --test transpiler -- --ignored add_sub_lui_auipc_mop --nocapture
