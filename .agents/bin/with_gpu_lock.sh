#!/usr/bin/env bash
set -euo pipefail

if [[ $# -eq 0 ]]; then
    echo "usage: $0 <command> [args...]" >&2
    exit 2
fi

LOCK_FILE="${GPU_LOCK_FILE:-/tmp/zksync-airbender-gpu.lock}"
LOCK_WAIT_SECONDS="${GPU_LOCK_WAIT_SECONDS:-}"
LOCK_OWNER="${GPU_LOCK_OWNER:-${USER:-unknown}}"

mkdir -p "$(dirname "$LOCK_FILE")"
exec 9>"$LOCK_FILE"

echo "[with_gpu_lock] waiting for GPU lock: $LOCK_FILE (owner=$LOCK_OWNER pid=$$)" >&2

if [[ -n "$LOCK_WAIT_SECONDS" ]]; then
    if ! flock -w "$LOCK_WAIT_SECONDS" 9; then
        echo "[with_gpu_lock] timed out after ${LOCK_WAIT_SECONDS}s waiting for GPU lock: $LOCK_FILE (owner=$LOCK_OWNER pid=$$)" >&2
        exit 1
    fi
else
    flock 9
fi

echo "[with_gpu_lock] acquired GPU lock: $LOCK_FILE (owner=$LOCK_OWNER pid=$$)" >&2

cleanup() {
    local status=$?
    echo "[with_gpu_lock] releasing GPU lock: $LOCK_FILE (owner=$LOCK_OWNER pid=$$ status=$status)" >&2
}

trap cleanup EXIT

set +e
"$@"
status=$?
set -e

exit "$status"
