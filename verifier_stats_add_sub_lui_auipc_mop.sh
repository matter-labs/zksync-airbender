#!/usr/bin/env bash
set -euo pipefail

REFRESH=false
NOCACHES=false
for arg in "$@"; do
    case "$arg" in
        --refresh) REFRESH=true ;;
        # Use the no-caches circuit/verifier variant. Requires a proof.json
        # that was generated against the no-caches circuit; regenerate via
        # `cargo test --release -p prover --features no_caches -- gkr_run_basic_unrolled_test`
        # before running with this flag.
        --nocaches) NOCACHES=true ;;
        *) echo "unknown arg: $arg" >&2; exit 1 ;;
    esac
done

REGEN_FEATURES=()
TEST_FEATURES="verifier_stats,blake2_with_compression"
if $NOCACHES; then
    REGEN_FEATURES=(--features no_caches)
    TEST_FEATURES="${TEST_FEATURES},no_caches"
fi

if $REFRESH; then
    env RUSTFLAGS=-Awarnings cargo test -p verifier_generator ${REGEN_FEATURES[@]+"${REGEN_FEATURES[@]}"} --test generate_verifiers add_sub_lui_auipc_mop
fi

OUT="verifier/verifier_stats_add_sub_lui_auipc_mop.txt"
TMP=$(mktemp)
trap 'rm -f "$TMP"' EXIT
env RUSTFLAGS=-Awarnings cargo test -p verifier --features "${TEST_FEATURES}" --test native -- add_sub_lui_auipc_mop --nocapture | tee "$TMP"
mv "$TMP" "$OUT"
chmod 644 "$OUT"
