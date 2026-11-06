#!/usr/bin/env bash
set -euo pipefail

REFRESH=false
for arg in "$@"; do
    case "$arg" in
        --refresh) REFRESH=true ;;
        *) echo "unknown arg: $arg" >&2; exit 1 ;;
    esac
done

TEST_FEATURES="verifier_stats,blake2_with_compression"

if $REFRESH; then
    env RUSTFLAGS=-Awarnings cargo test -p verifier_generator --test generate_verifiers add_sub_lui_auipc_mop
fi

OUT="verifier/verifier_stats_add_sub_lui_auipc_mop.txt"
TMP=$(mktemp)
trap 'rm -f "$TMP"' EXIT
env RUSTFLAGS=-Awarnings cargo test -p verifier --features "${TEST_FEATURES}" --test native -- add_sub_lui_auipc_mop --nocapture | tee "$TMP"
mv "$TMP" "$OUT"
chmod 644 "$OUT"
