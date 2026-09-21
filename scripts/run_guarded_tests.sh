#!/usr/bin/env bash
# Fail when a Cargo test selection executes fewer than MIN_TESTS tests.
set -euo pipefail
MIN_TESTS="${MIN_TESTS:-1}"
test "$MIN_TESTS" -gt 0
run_log="$(mktemp)"
trap 'rm -f "$run_log"' EXIT
cargo test "$@" 2>&1 | tee "$run_log"
passed="$(awk '/^test result: ok\./ { total += $4 } END { print total + 0 }' "$run_log")"
if [[ "$passed" -lt "$MIN_TESTS" ]]; then
    echo "Expected at least $MIN_TESTS passing tests, got $passed" >&2
    exit 1
fi
