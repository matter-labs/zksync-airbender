#!/usr/bin/env bash
# Validate the exact continuation-window symbol bank and linked resources in the
# gpu_gkr native archive produced by this invocation.
set -euo pipefail

readonly SYMBOL_PREFIX=ab_gkr_bwd_main_cont_window3
readonly ARCHIVE_NAME=libgpu_gkr_native.a
readonly GENERATED_DIR=gpu/gkr/native/gkr/backward/main_continuation_window/generated
readonly EXPECTED_KERNELS=7

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)
cd "$root"

expected=$(mktemp)
observed=$(mktemp)
build_json=$(mktemp)
resources=$(mktemp)
sass=$(mktemp)
trap 'rm -f "$expected" "$observed" "$build_json" "$resources" "$sass"' EXIT

grep -ho "${SYMBOL_PREFIX}[A-Za-z0-9_]*" "$GENERATED_DIR"/*.cu | sort -u >"$expected"
if [[ $(wc -l <"$expected") -ne $EXPECTED_KERNELS ]]; then
    echo "FAIL: expected $EXPECTED_KERNELS distinct generated continuation symbols" >&2
    exit 1
fi

flags=("$@")
if [[ ${#flags[@]} -eq 0 ]]; then
    flags=(--release)
fi

RUSTFLAGS=${RUSTFLAGS:--Awarnings} \
    cargo build -p gpu_gkr "${flags[@]}" --message-format=json >"$build_json"

mapfile -t candidates < <(
    python3 - "$build_json" "$ARCHIVE_NAME" <<'PY'
import json
import os
import sys

log_path, archive_name = sys.argv[1:]
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

if [[ ${#candidates[@]} -ne 1 ]]; then
    echo "FAIL: expected exactly one $ARCHIVE_NAME from this build, found ${#candidates[@]}" >&2
    printf '  %s\n' "${candidates[@]}" >&2
    exit 1
fi

archive=${candidates[0]}
echo "archive: $archive"

cuobjdump -symbols "$archive" |
    grep -o "${SYMBOL_PREFIX}[A-Za-z0-9_]*" |
    sort -u >"$observed"
if ! diff -u "$expected" "$observed"; then
    echo "FAIL: linked continuation symbols differ from generated sources" >&2
    exit 1
fi

cuobjdump --dump-resource-usage "$archive" >"$resources"
cuobjdump --dump-sass "$archive" >"$sass"

python3 - "$expected" "$resources" "$sass" "$SYMBOL_PREFIX" <<'PY'
import re
import sys

expected_path, resources_path, sass_path, prefix = sys.argv[1:]
expected = {line.strip() for line in open(expected_path) if line.strip()}

function_re = re.compile(r"^\s*Function (?P<symbol>[^:]+):$")
resource_re = re.compile(
    r"^\s*REG:(?P<registers>\d+) STACK:(?P<stack>\d+) "
    r"SHARED:(?P<shared>\d+) LOCAL:(?P<local>\d+)"
)
constant_re = re.compile(r"\bCONSTANT\[3\]:(?P<constant3>\d+)\b")

records = {symbol: [] for symbol in expected}
current = None
constant3 = []
with open(resources_path) as handle:
    for line in handle:
        if match := constant_re.search(line):
            constant3.append(int(match.group("constant3")))
        if match := function_re.match(line.rstrip("\n")):
            current = match.group("symbol")
            continue
        if current is not None and (match := resource_re.match(line.rstrip("\n"))):
            if current in expected:
                records[current].append(
                    {name: int(value) for name, value in match.groupdict().items()}
                )
            current = None

missing = sorted(symbol for symbol, rows in records.items() if not rows)
if missing:
    raise SystemExit(f"FAIL: missing resource records for {missing}")
if not constant3:
    raise SystemExit("FAIL: linked image reports no CONSTANT[3] record")
if max(constant3) > 65_536:
    raise SystemExit(f"FAIL: CONSTANT[3] exceeds 65536 bytes: {constant3}")

sass_function_re = re.compile(r"^\s*Function : (?P<symbol>\S+)$")
opcode_re = re.compile(
    r"^\s*/\*[0-9a-fA-F]+\*/\s+(?:@!?[A-Za-z0-9_.]+\s+)?(?P<opcode>[A-Z][A-Z0-9_.]*)\b"
)
spills = {symbol: {"loads": 0, "stores": 0} for symbol in expected}
current = None
with open(sass_path) as handle:
    for line in handle:
        if match := sass_function_re.match(line.rstrip("\n")):
            current = match.group("symbol")
            continue
        if current not in expected:
            continue
        if match := opcode_re.match(line):
            opcode = match.group("opcode").split(".", 1)[0]
            if opcode == "LDL":
                spills[current]["loads"] += 1
            elif opcode == "STL":
                spills[current]["stores"] += 1

for symbol in sorted(expected):
    for record in records[symbol]:
        if record["stack"] != 0 or record["local"] != 0:
            raise SystemExit(f"FAIL: {symbol} uses stack/local storage: {record}")
        if record["shared"] > 49_152:
            raise SystemExit(f"FAIL: {symbol} static shared memory exceeds 49152 bytes: {record}")
        if record["registers"] > 255:
            raise SystemExit(f"FAIL: {symbol} register count is invalid: {record}")
    if spills[symbol] != {"loads": 0, "stores": 0}:
        raise SystemExit(f"FAIL: {symbol} has local spill instructions: {spills[symbol]}")
    rendered = "; ".join(
        f"REG:{row['registers']} STACK:{row['stack']} SHARED:{row['shared']} LOCAL:{row['local']}"
        for row in records[symbol]
    )
    print(
        f"resource: {symbol} {rendered} "
        f"spill_loads:{spills[symbol]['loads']} spill_stores:{spills[symbol]['stores']}"
    )

print(f"CONSTANT[3]: {max(constant3)}")
PY

echo "OK: $EXPECTED_KERNELS continuation kernels; exact symbols and legal linked resources"
