#!/usr/bin/env bash
set -euo pipefail

REFRESH=false
for arg in "$@"; do
    case "$arg" in
        --refresh) REFRESH=true ;;
        *) echo "unknown arg: $arg" >&2; exit 1 ;;
    esac
done

if $REFRESH; then
    env RUSTFLAGS=-Awarnings cargo test -p verifier_generator --features no_caches --test generate_verifiers add_sub_lui_auipc_mop
fi

env RUSTFLAGS=-Awarnings cargo test -p verifier --features verifier_stats,blake2_with_compression,no_caches --test native -- add_sub_lui_auipc_mop --nocapture

if $REFRESH; then
    (cd tools/gkr_verifier && ./dump_bin.sh --stats add_sub_lui_auipc_mop)
fi

env RUSTFLAGS=-Awarnings cargo test --profile test-release -p verifier --features verifier_stats,blake2_with_compression,no_caches --test transpiler -- --ignored add_sub_lui_auipc_mop --nocapture
