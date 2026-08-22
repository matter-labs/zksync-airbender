#!/usr/bin/env bash
# Assert the linked gpu_gkr_native archive exports exactly the windowed-R0 entry
# points the committed generated translation units define, and no others.
#
#   gpu/gkr/scripts/check-window-kernel-symbols.sh [cargo build flags...]
#
# Defaults to `--release`. The archive is resolved from THIS build's own output
# (the link search paths gpu_gkr's build script reported), never from a guessed
# target path, so a stale archive elsewhere under target/ cannot answer for it.
# Symbols are counted by DISTINCT name: a device-linked archive lists each kernel
# once per image it appears in, so the raw line count is a multiple of the truth.
set -euo pipefail

readonly SYMBOL_PREFIX=ab_gkr_bwd_r0_window3
readonly ARCHIVE_NAME=libgpu_gkr_native.a

root=$(git -C "$(dirname "${BASH_SOURCE[0]}")" rev-parse --show-toplevel)
cd "$root"

readonly GENERATED_DIR=gpu/gkr/native/gkr/backward/generated

expected=$(mktemp)
observed=$(mktemp)
log=$(mktemp)
trap 'rm -f "$expected" "$observed" "$log"' EXIT

grep -ho "${SYMBOL_PREFIX}[A-Za-z0-9_]*" "$GENERATED_DIR"/*.cu | sort -u >"$expected"
if [[ ! -s "$expected" ]]; then
    echo "FAIL: no $SYMBOL_PREFIX kernels found in $GENERATED_DIR" >&2
    exit 1
fi

flags=("$@")
if [[ ${#flags[@]} -eq 0 ]]; then
    flags=(--release)
fi

RUSTFLAGS=${RUSTFLAGS:--Awarnings} \
    cargo build -p gpu_gkr "${flags[@]}" --message-format=json >"$log"

mapfile -t candidates < <(
    python3 - "$log" "$ARCHIVE_NAME" <<'PY'
import json, os, sys

log_path, archive_name = sys.argv[1], sys.argv[2]
roots = []
with open(log_path) as handle:
    for line in handle:
        line = line.strip()
        if not line.startswith("{"):
            continue
        message = json.loads(line)
        if message.get("reason") != "build-script-executed":
            continue
        package = message.get("package_id", "")
        if "gpu_gkr" not in package or "gpu_gkr_" in package:
            continue
        roots.extend(message.get("linked_paths", []))

# Only the link search paths themselves: that is what the linker resolves, so a
# CMake build-tree copy underneath one of them must not be mistaken for it.
found = set()
for entry in roots:
    directory = entry.split("=", 1)[1] if entry.startswith("native=") else entry
    candidate = os.path.join(directory, archive_name)
    if os.path.isfile(candidate):
        found.add(os.path.realpath(candidate))
for path in sorted(found):
    print(path)
PY
)

if [[ ${#candidates[@]} -eq 0 ]]; then
    echo "FAIL: this build reported no $ARCHIVE_NAME for gpu_gkr" >&2
    exit 1
fi
if [[ ${#candidates[@]} -gt 1 ]]; then
    echo "FAIL: this build reported ${#candidates[@]} candidate archives:" >&2
    printf '  %s\n' "${candidates[@]}" >&2
    exit 1
fi

archive=${candidates[0]}
echo "archive: $archive"

cuobjdump -symbols "$archive" |
    grep -o "${SYMBOL_PREFIX}[A-Za-z0-9_]*" |
    sort -u >"$observed"

if ! diff -u "$expected" "$observed"; then
    echo "FAIL: linked window kernels differ from the committed generated sources" >&2
    exit 1
fi

echo "OK: $(wc -l <"$observed") window kernels in $ARCHIVE_NAME"
