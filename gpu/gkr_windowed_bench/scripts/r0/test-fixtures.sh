#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
RUN_TIMING="$SCRIPT_DIR/run-timing.py"
AUDIT_RESULTS="$SCRIPT_DIR/audit-results.py"
DERIVE_ENVELOPE="$SCRIPT_DIR/derive-envelope.py"
BUILD_POINT="$SCRIPT_DIR/build-point.sh"
FIXTURE_ROOT="$(mktemp -d)"
trap 'rm -rf "$FIXTURE_ROOT"' EXIT

TASK11_ROOT="$FIXTURE_ROOT/task11"
TASK11_DEVICE="$TASK11_ROOT/device.json"
TASK11_NATURAL="$TASK11_ROOT/natural.json"
TASK11_RESULTS_SAME="$TASK11_ROOT/results-same.json"
TASK11_RESULTS_DIFFERENT="$TASK11_ROOT/results-different.json"
TASK11_POINTS="$TASK11_ROOT/points.json"
TASK11_BUILD_ROOT="$TASK11_ROOT/builds"
TASK11_FAKE_BIN="$TASK11_ROOT/fake-bin"

mkdir -p "$TASK11_ROOT" "$TASK11_FAKE_BIN"

python3 - \
    "$TASK11_DEVICE" "$TASK11_NATURAL" \
    "$TASK11_RESULTS_SAME" "$TASK11_RESULTS_DIFFERENT" <<'PY'
import json
import pathlib
import sys

device_path, natural_path, same_path, different_path = map(pathlib.Path, sys.argv[1:])
device = {
    "device_id": "fixture-sm",
    "registers_per_sm": 65_536,
    "max_threads_per_sm": 1_536,
    "max_blocks_per_sm": 24,
    "warp_size": 32,
    "register_allocation_granularity": 8,
}
natural = [
    {
        "geometry": "cta288_pair",
        "threads": 288,
        "registers": 70,
        "shared_bytes": 0,
        "active_blocks": 3,
    }
]
same = [
    {
        "point_id": "cta288_pair--launch-b4-r0",
        "geometry": "cta288_pair",
        "kind": "launch",
        "target_active_blocks": 4,
        "min_blocks": 4,
        "maxreg": 0,
        "outcome": "success",
        "resources": {
            "registers": 56,
            "stack_bytes": 0,
            "local_bytes": 0,
            "shared_bytes": 0,
            "binary_sha256": "a" * 64,
        },
    },
    {
        "point_id": "cta288_pair--maxreg-b0-r56",
        "geometry": "cta288_pair",
        "kind": "maxreg",
        "target_active_blocks": 4,
        "min_blocks": 0,
        "maxreg": 56,
        "outcome": "success",
        "resources": {
            "registers": 56,
            "stack_bytes": 0,
            "local_bytes": 0,
            "shared_bytes": 0,
            "binary_sha256": "a" * 64,
        },
    },
]
different = json.loads(json.dumps(same))
different[1]["resources"]["stack_bytes"] = 16
different[1]["resources"]["binary_sha256"] = "b" * 64
for path, value in (
    (device_path, device),
    (natural_path, natural),
    (same_path, same),
    (different_path, different),
):
    path.write_text(json.dumps(value, sort_keys=True) + "\n")
PY

python3 "$DERIVE_ENVELOPE" derive \
    --device "$TASK11_DEVICE" \
    --natural "$TASK11_NATURAL" \
    --output "$TASK11_POINTS"

python3 - "$TASK11_POINTS" <<'PY'
import json
import pathlib
import sys

points = json.loads(pathlib.Path(sys.argv[1]).read_text())["points"]
assert points == [
    {
        "constraints": [
            {"geometry": "cta288_pair", "maxreg": 0, "min_blocks": 0}
        ],
        "geometry": "cta288_pair",
        "kind": "natural",
        "maxreg": 0,
        "min_blocks": 0,
        "parents": [],
        "point_id": "cta288_pair--natural-b0-r0",
        "target_active_blocks": 3,
    },
    {
        "constraints": [
            {"geometry": "cta288_pair", "maxreg": 0, "min_blocks": 4}
        ],
        "geometry": "cta288_pair",
        "kind": "launch",
        "maxreg": 0,
        "min_blocks": 4,
        "parents": ["cta288_pair--natural-b0-r0"],
        "point_id": "cta288_pair--launch-b4-r0",
        "target_active_blocks": 4,
    },
    {
        "constraints": [
            {"geometry": "cta288_pair", "maxreg": 56, "min_blocks": 0}
        ],
        "geometry": "cta288_pair",
        "kind": "maxreg",
        "maxreg": 56,
        "min_blocks": 0,
        "parents": ["cta288_pair--natural-b0-r0"],
        "point_id": "cta288_pair--maxreg-b0-r56",
        "target_active_blocks": 4,
    },
]
PY

python3 "$DERIVE_ENVELOPE" derive \
    --device "$TASK11_DEVICE" --natural "$TASK11_NATURAL" \
    --results "$TASK11_RESULTS_SAME" --output "$TASK11_POINTS"
test "$(python3 -c 'import json,sys; print(len(json.load(open(sys.argv[1]))["points"]))' "$TASK11_POINTS")" -eq 3

python3 "$DERIVE_ENVELOPE" derive \
    --device "$TASK11_DEVICE" --natural "$TASK11_NATURAL" \
    --results "$TASK11_RESULTS_DIFFERENT" --output "$TASK11_POINTS"
python3 - "$TASK11_POINTS" <<'PY'
import json
import pathlib
import sys

points = json.loads(pathlib.Path(sys.argv[1]).read_text())["points"]
combined = [point for point in points if point["kind"] == "combined"]
assert combined == [
    {
        "constraints": [
            {"geometry": "cta288_pair", "maxreg": 56, "min_blocks": 4}
        ],
        "geometry": "cta288_pair",
        "kind": "combined",
        "maxreg": 56,
        "min_blocks": 4,
        "parents": [
            "cta288_pair--launch-b4-r0",
            "cta288_pair--maxreg-b0-r56",
        ],
        "point_id": "cta288_pair--combined-b4-r56",
        "target_active_blocks": 4,
    }
]
PY

for mutation in \
    zero negative impossible duplicate multi-geometry \
    device-mismatch target-mismatch threshold-mismatch dangling-parent; do
    python3 - "$TASK11_POINTS" "$TASK11_ROOT/invalid-$mutation.json" "$mutation" <<'PY'
import json
import pathlib
import sys

source, output, mutation = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2]), sys.argv[3]
value = json.loads(source.read_text())
if mutation == "zero":
    next(point for point in value["points"] if point["kind"] == "launch")["min_blocks"] = 0
elif mutation == "negative":
    next(point for point in value["points"] if point["kind"] == "maxreg")["maxreg"] = -8
elif mutation == "impossible":
    next(point for point in value["points"] if point["kind"] == "launch")["min_blocks"] = 6
elif mutation == "duplicate":
    value["points"].append(json.loads(json.dumps(value["points"][0])))
elif mutation == "multi-geometry":
    value["points"][1]["constraints"].append(
        {"geometry": "cta96_x0_major", "min_blocks": 0, "maxreg": 64}
    )
elif mutation == "device-mismatch":
    value["device"]["registers_per_sm"] += 1
elif mutation == "target-mismatch":
    next(point for point in value["points"] if point["kind"] == "launch")[
        "target_active_blocks"
    ] = 5
elif mutation == "threshold-mismatch":
    point = next(point for point in value["points"] if point["kind"] == "maxreg")
    point["maxreg"] = 64
    point["point_id"] = "cta288_pair--maxreg-b0-r64"
    point["constraints"] = [
        {"geometry": "cta288_pair", "min_blocks": 0, "maxreg": 64}
    ]
elif mutation == "dangling-parent":
    next(point for point in value["points"] if point["kind"] == "natural")[
        "parents"
    ] = ["missing-point"]
else:
    raise AssertionError(mutation)
output.write_text(json.dumps(value, sort_keys=True) + "\n")
PY
    if python3 "$DERIVE_ENVELOPE" validate \
        --device "$TASK11_DEVICE" \
        --points "$TASK11_ROOT/invalid-$mutation.json" \
        > "$TASK11_ROOT/invalid-$mutation.stdout" \
        2> "$TASK11_ROOT/invalid-$mutation.stderr"; then
        echo "invalid Task 11 point mutation unexpectedly succeeded: $mutation" >&2
        exit 1
    fi
done

cat > "$TASK11_FAKE_BIN/cargo" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
if [[ "${1:-}" == "--version" ]]; then
    echo "cargo fixture 1.0"
    exit 0
fi
if [[ -v GPU_GKR_WINDOWED_BENCH_ENABLE_BUILD_DIAG ]]; then
    echo "build-point must not enable collision-prone nvcc --keep diagnostics" >&2
    exit 88
fi
if [[ "${TASK11_FAKE_CARGO_FAIL:-0}" == 1 ]]; then
    echo "intentional compiler failure" >&2
    exit 41
fi
target_dir="${CARGO_TARGET_DIR:?}"
cmake_dir="$target_dir/release/build/gpu_gkr_windowed_bench-fixture/out/build"
mkdir -p "$target_dir/release" "$cmake_dir/CMakeFiles/gpu_gkr_windowed_bench_native.dir"

python3 - "$cmake_dir/compile_commands.json" <<'PY'
import json
import os
import pathlib
import sys

geometries = (
    "CTA288_PAIR",
    "CTA96_PARTITIONED",
    "CTA96_X0_MAJOR",
    "CTA96_X1_MAJOR",
    "CTA96_X2_MAJOR",
)
commands = []
for upper in geometries:
    lower = upper.lower()
    options = []
    prefix = f"GPU_GKR_WINDOWED_R0_{upper}"
    min_blocks = os.environ.get(f"{prefix}_MIN_BLOCKS")
    maxreg = os.environ.get(f"{prefix}_MAXREG")
    if min_blocks and min_blocks != "0":
        options.append(
            f"-D{prefix}_MIN_BLOCKS={min_blocks}"
            f"{os.environ.get('TASK11_FAKE_MIN_SUFFIX', '')}"
        )
    if maxreg and maxreg != "0":
        options.append(
            f"--maxrregcount={maxreg}"
            f"{os.environ.get('TASK11_FAKE_MAX_SUFFIX', '')}"
        )
    if os.environ.get("GPU_GKR_WINDOWED_BENCH_ENABLE_LINEINFO"):
        options.append("-lineinfo")
    commands.append(
        {
            "directory": "/fixture/build",
            "file": f"/fixture/native/windowed_r0_{lower}.cu",
            "command": "nvcc --device-c " + " ".join(options) + f" windowed_r0_{lower}.cu",
        }
    )
pathlib.Path(sys.argv[1]).write_text(json.dumps(commands) + "\n")
PY

printf 'nvcc --device-link fixture-objects -o fixture-device-link.o\n' \
    > "$cmake_dir/CMakeFiles/gpu_gkr_windowed_bench_native.dir/dlink.txt"
printf 'GPU_GKR_WINDOWED_BENCH_ENABLE_LINEINFO:BOOL=%s\n' \
    "$([[ -n "${GPU_GKR_WINDOWED_BENCH_ENABLE_LINEINFO:-}" ]] && echo ON || echo OFF)" \
    > "$cmake_dir/CMakeCache.txt"
printf 'fixture binary lineinfo=%s\n' "${GPU_GKR_WINDOWED_BENCH_ENABLE_LINEINFO:-off}" \
    > "$target_dir/release/run_windowed_r0_corpus"
chmod +x "$target_dir/release/run_windowed_r0_corpus"
SH
chmod +x "$TASK11_FAKE_BIN/cargo"

cat > "$TASK11_FAKE_BIN/cuobjdump" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
case "${1:-}" in
    --version)
        echo "cuobjdump fixture 1.0"
        ;;
    --extract-elf|-xelf)
        printf 'fixture cubin\n' > fixture.1.sm_120.cubin
        ;;
    --dump-elf-symbols|-symbols)
        for geometry in cta288_pair cta96_partitioned cta96_x0_major cta96_x1_major cta96_x2_major; do
            echo "STT_FUNC ab_gkr_windowed_r0_${geometry}_kernel"
        done
        ;;
    --dump-resource-usage|-res-usage)
        for geometry in cta288_pair cta96_partitioned cta96_x0_major cta96_x1_major cta96_x2_major; do
            echo " Function ab_gkr_windowed_r0_${geometry}_kernel:"
            echo "  REG:56 STACK:0 SHARED:0 LOCAL:0 CONSTANT[0]:18432"
        done
        ;;
    --dump-sass|-sass)
        for geometry in cta288_pair cta96_partitioned cta96_x0_major cta96_x1_major cta96_x2_major; do
            echo "Function : ab_gkr_windowed_r0_${geometry}_kernel"
            echo ' /*0000*/ LDC R0, c[0x0][0x0];'
            echo ' /*0010*/ EXIT;'
        done
        ;;
    --dump-elf|-elf)
        echo 'arch = sm_120'
        ;;
    *)
        echo "unsupported fake cuobjdump invocation: $*" >&2
        exit 2
        ;;
esac
SH
chmod +x "$TASK11_FAKE_BIN/cuobjdump"

for tool in nvcc rustc cmake clang; do
    cat > "$TASK11_FAKE_BIN/$tool" <<SH
#!/usr/bin/env bash
echo "$tool fixture 1.0"
SH
    chmod +x "$TASK11_FAKE_BIN/$tool"
done

CLAIM_ROOT="$TASK11_ROOT/claim-builds"
CLAIM_POINT=cta96_partitioned--natural-b0-r0
mkdir -p "$CLAIM_ROOT/.claims/$CLAIM_POINT"
if PATH="$TASK11_FAKE_BIN:$PATH" CARGO="$TASK11_FAKE_BIN/cargo" \
    R0_BUILD_POINT_ROOT="$CLAIM_ROOT" \
    R0_BUILD_POINT_DEVICE_JSON="$TASK11_DEVICE" \
    "$BUILD_POINT" cta96_partitioned natural 0 0 \
    > "$TASK11_ROOT/live-claim.stdout" \
    2> "$TASK11_ROOT/live-claim.stderr"; then
    echo "same-point live claim unexpectedly succeeded" >&2
    exit 1
fi
[[ ! -e "$CLAIM_ROOT/$CLAIM_POINT" ]]
rmdir "$CLAIM_ROOT/.claims/$CLAIM_POINT"
PATH="$TASK11_FAKE_BIN:$PATH" \
CARGO="$TASK11_FAKE_BIN/cargo" \
R0_BUILD_POINT_ROOT="$CLAIM_ROOT" \
R0_BUILD_POINT_DEVICE_JSON="$TASK11_DEVICE" \
    "$BUILD_POINT" cta96_partitioned natural 0 0
[[ ! -e "$CLAIM_ROOT/.claims/$CLAIM_POINT" ]]

PATH="$TASK11_FAKE_BIN:$PATH" \
CARGO="$TASK11_FAKE_BIN/cargo" \
R0_BUILD_POINT_ROOT="$TASK11_BUILD_ROOT" \
R0_BUILD_POINT_DEVICE_JSON="$TASK11_DEVICE" \
    "$BUILD_POINT" cta288_pair natural 0 0
PATH="$TASK11_FAKE_BIN:$PATH" \
CARGO="$TASK11_FAKE_BIN/cargo" \
R0_BUILD_POINT_ROOT="$TASK11_BUILD_ROOT" \
R0_BUILD_POINT_DEVICE_JSON="$TASK11_DEVICE" \
    "$BUILD_POINT" cta288_pair launch 4 0
PATH="$TASK11_FAKE_BIN:$PATH" \
CARGO="$TASK11_FAKE_BIN/cargo" \
R0_BUILD_POINT_ROOT="$TASK11_BUILD_ROOT" \
R0_BUILD_POINT_DEVICE_JSON="$TASK11_DEVICE" \
    "$BUILD_POINT" cta96_x0_major maxreg 0 56

for built_point in \
    cta288_pair--natural-b0-r0 \
    cta288_pair--launch-b4-r0 \
    cta96_x0_major--maxreg-b0-r56; do
    (
        cd "$TASK11_BUILD_ROOT/$built_point"
        sha256sum --quiet -c files.sha256
    )
done

grep -q -- '-DGPU_GKR_WINDOWED_R0_CTA288_PAIR_MIN_BLOCKS=4' \
    "$TASK11_BUILD_ROOT/cta288_pair--launch-b4-r0/timing/target-compile-command.txt"
if grep -q -- 'MIN_BLOCKS=4' \
    "$TASK11_BUILD_ROOT/cta288_pair--launch-b4-r0/timing/sibling-compile-commands.txt"; then
    echo "launch bound leaked into a sibling translation unit" >&2
    exit 1
fi
grep -q -- '--maxrregcount=56' \
    "$TASK11_BUILD_ROOT/cta96_x0_major--maxreg-b0-r56/timing/target-compile-command.txt"
if grep -q -- '--maxrregcount' \
    "$TASK11_BUILD_ROOT/cta96_x0_major--maxreg-b0-r56/timing/sibling-compile-commands.txt"; then
    echo "max-register cap leaked into a sibling translation unit" >&2
    exit 1
fi
if grep -q -- '--maxrregcount' \
    "$TASK11_BUILD_ROOT/cta96_x0_major--maxreg-b0-r56/timing/device-link-command.txt"; then
    echo "max-register cap leaked into device link" >&2
    exit 1
fi

COMPILER_FAILURE_ROOT="$TASK11_ROOT/compiler-failure-builds"
if TASK11_FAKE_CARGO_FAIL=1 \
    PATH="$TASK11_FAKE_BIN:$PATH" CARGO="$TASK11_FAKE_BIN/cargo" \
    R0_BUILD_POINT_ROOT="$COMPILER_FAILURE_ROOT" \
    R0_BUILD_POINT_DEVICE_JSON="$TASK11_DEVICE" \
    "$BUILD_POINT" cta288_pair natural 0 0 \
    > "$TASK11_ROOT/compiler-failure.stdout" \
    2> "$TASK11_ROOT/compiler-failure.stderr"; then
    echo "intentional compiler failure unexpectedly succeeded" >&2
    exit 1
fi
python3 - "$COMPILER_FAILURE_ROOT/cta288_pair--natural-b0-r0/outcome.json" <<'PY'
import json
import pathlib
import sys

outcome = json.loads(pathlib.Path(sys.argv[1]).read_text())
assert outcome["outcome"] == "compiler_failure", outcome
assert outcome["phase"] == "timing_compile", outcome
assert outcome["exit_code"] == 41, outcome
PY
[[ ! -e "$COMPILER_FAILURE_ROOT/.claims/cta288_pair--natural-b0-r0" ]]

for mismatch in min max; do
    MISMATCH_ROOT="$TASK11_ROOT/$mismatch-mismatch-builds"
    if [[ "$mismatch" == min ]]; then
        mismatch_geometry=cta96_x1_major
        mismatch_kind=launch
        mismatch_min=5
        mismatch_maxreg=0
        mismatch_env=(TASK11_FAKE_MIN_SUFFIX=0)
    else
        mismatch_geometry=cta96_x2_major
        mismatch_kind=maxreg
        mismatch_min=0
        mismatch_maxreg=96
        mismatch_env=(TASK11_FAKE_MAX_SUFFIX=0)
    fi
    if env "${mismatch_env[@]}" \
        PATH="$TASK11_FAKE_BIN:$PATH" CARGO="$TASK11_FAKE_BIN/cargo" \
        R0_BUILD_POINT_ROOT="$MISMATCH_ROOT" \
        R0_BUILD_POINT_DEVICE_JSON="$TASK11_DEVICE" \
        "$BUILD_POINT" "$mismatch_geometry" "$mismatch_kind" \
        "$mismatch_min" "$mismatch_maxreg" \
        > "$TASK11_ROOT/$mismatch-mismatch.stdout" \
        2> "$TASK11_ROOT/$mismatch-mismatch.stderr"; then
        echo "near-match $mismatch compile flag unexpectedly succeeded" >&2
        exit 1
    fi
    mismatch_point="$MISMATCH_ROOT/${mismatch_geometry}--${mismatch_kind}-b${mismatch_min}-r${mismatch_maxreg}"
    python3 - "$mismatch_point/outcome.json" <<'PY'
import json
import pathlib
import sys

outcome = json.loads(pathlib.Path(sys.argv[1]).read_text())
assert outcome["outcome"] == "recording_failure", outcome
assert outcome["phase"] == "timing_recording", outcome
PY
done

if PATH="$TASK11_FAKE_BIN:$PATH" CARGO="$TASK11_FAKE_BIN/cargo" \
    R0_BUILD_POINT_ROOT="$TASK11_BUILD_ROOT" \
    R0_BUILD_POINT_DEVICE_JSON="$TASK11_DEVICE" \
    "$BUILD_POINT" cta288_pair natural 0 0 \
    > "$TASK11_ROOT/overwrite.stdout" 2> "$TASK11_ROOT/overwrite.stderr"; then
    echo "complete point overwrite unexpectedly succeeded" >&2
    exit 1
fi

for invalid in 'launch 0 0' 'maxreg 0 -8' 'combined 6 56'; do
    read -r kind min_blocks maxreg <<< "$invalid"
    if PATH="$TASK11_FAKE_BIN:$PATH" CARGO="$TASK11_FAKE_BIN/cargo" \
        R0_BUILD_POINT_ROOT="$TASK11_BUILD_ROOT" \
        R0_BUILD_POINT_DEVICE_JSON="$TASK11_DEVICE" \
        "$BUILD_POINT" cta288_pair "$kind" "$min_blocks" "$maxreg" \
        > "$TASK11_ROOT/build-invalid.stdout" 2> "$TASK11_ROOT/build-invalid.stderr"; then
        echo "invalid build point unexpectedly succeeded: $invalid" >&2
        exit 1
    fi
done

if GPU_GKR_WINDOWED_R0_CTA96_X0_MAJOR_MAXREG=56 \
    PATH="$TASK11_FAKE_BIN:$PATH" CARGO="$TASK11_FAKE_BIN/cargo" \
    R0_BUILD_POINT_ROOT="$TASK11_BUILD_ROOT" \
    R0_BUILD_POINT_DEVICE_JSON="$TASK11_DEVICE" \
    "$BUILD_POINT" cta288_pair launch 4 0 \
    > "$TASK11_ROOT/foreign-control.stdout" \
    2> "$TASK11_ROOT/foreign-control.stderr"; then
    echo "foreign geometry control unexpectedly succeeded" >&2
    exit 1
fi

echo "TASK11_FIXTURES_OK"
if [[ "${TASK11_ONLY:-0}" == 1 ]]; then
    exit 0
fi

TASK12_ROOT="$FIXTURE_ROOT/task12"
TASK12_POINTS="$TASK12_ROOT/points.json"
TASK12_EVIDENCE="$TASK12_ROOT/evidence.json"
TASK12_DEDUP="$TASK12_ROOT/dedup.json"
mkdir -p "$TASK12_ROOT"

python3 - "$TASK12_POINTS" "$TASK12_EVIDENCE" <<'PY'
import json
import pathlib
import sys

points_path, evidence_path = map(pathlib.Path, sys.argv[1:])
common = {
    "geometry": "cta96_x0_major",
    "symbol": "ab_gkr_windowed_r0_cta96_x0_major_kernel",
    "bundle_sha256": "c" * 64,
    "correctness_input_bindings_sha256": "d" * 64,
    "sanitizer_input_bindings_sha256": "e" * 64,
    "registers": 96,
}
points = [
    {**common, "point_id": "point-a", "executable_sha256": "a" * 64},
    {**common, "point_id": "point-a-alias", "executable_sha256": "a" * 64},
    {**common, "point_id": "point-b", "executable_sha256": "b" * 64},
    {
        **common,
        "point_id": "point-symbol",
        "executable_sha256": "a" * 64,
        "symbol": "ab_gkr_windowed_r0_cta96_x0_major_kernel_variant",
    },
]
evidence = {
    "version": 1,
    "points": {
        "point-a": {
            "correctness": "complete",
            "sanitizer": "complete",
            "fully_timed": True,
        },
        "point-a-alias": {"reused_from": "point-a"},
        "point-b": {
            "correctness": "complete",
            "sanitizer": "complete",
            "fully_timed": True,
        },
        "point-symbol": {
            "correctness": "complete",
            "sanitizer": "complete",
            "fully_timed": True,
        },
    },
}
points_path.write_text(json.dumps({"version": 1, "points": points}) + "\n")
evidence_path.write_text(json.dumps(evidence) + "\n")
PY

python3 "$AUDIT_RESULTS" envelope-dedup \
    --points "$TASK12_POINTS" \
    --evidence "$TASK12_EVIDENCE" \
    --output "$TASK12_DEDUP"
python3 - "$TASK12_DEDUP" <<'PY'
import json
import pathlib
import sys

dedup = json.loads(pathlib.Path(sys.argv[1]).read_text())
assert dedup["unique_evidence_groups"] == 3, dedup
assert dedup["representatives"] == ["point-a", "point-b", "point-symbol"], dedup
assert dedup["reuse"] == {"point-a-alias": "point-a"}, dedup
PY

for mutation in missing-b-sanitizer resource-only-reuse symbol-reuse; do
    python3 - "$TASK12_EVIDENCE" "$TASK12_ROOT/$mutation.json" "$mutation" <<'PY'
import json
import pathlib
import sys

source, output, mutation = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2]), sys.argv[3]
value = json.loads(source.read_text())
if mutation == "missing-b-sanitizer":
    del value["points"]["point-b"]["sanitizer"]
elif mutation == "resource-only-reuse":
    value["points"]["point-b"] = {"reused_from": "point-a"}
elif mutation == "symbol-reuse":
    value["points"]["point-symbol"] = {"reused_from": "point-a"}
else:
    raise AssertionError(mutation)
output.write_text(json.dumps(value) + "\n")
PY
    if python3 "$AUDIT_RESULTS" envelope-dedup \
        --points "$TASK12_POINTS" \
        --evidence "$TASK12_ROOT/$mutation.json" \
        --output "$TASK12_ROOT/$mutation-output.json" \
        > "$TASK12_ROOT/$mutation.stdout" \
        2> "$TASK12_ROOT/$mutation.stderr"; then
        echo "invalid Task 12 dedup mutation unexpectedly succeeded: $mutation" >&2
        exit 1
    fi
    grep -Eq 'sanitizer evidence|deduplication binding mismatch' \
        "$TASK12_ROOT/$mutation.stderr"
done

python3 - "$RUN_TIMING" "$AUDIT_RESULTS" <<'PY'
import importlib.util
import pathlib
import sys


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, pathlib.Path(path))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


timing = load("task12_run_timing", sys.argv[1])
audit = load("task12_audit_results", sys.argv[2])
points = ["point-a", "point-b", "point-c"]
assert timing.rotated_points(points, 0, "forward") == points
assert timing.rotated_points(points, 1, "forward") == ["point-b", "point-c", "point-a"]
assert timing.rotated_points(points, 0, "reverse") == ["point-c", "point-a", "point-b"]
assert timing.envelope_pair_session_count(15, 57) == 1710
assert timing.envelope_pair_session_count(1, 1) == 2
budget = timing.projected_envelope_budget(
    pilot_wall_seconds=481.197406,
    pilot_sessions=6,
    distinct_point_binaries=20,
    total_pair_sessions=1710,
    completed_pair_sessions=0,
)
assert budget == {
    "version": 1,
    "pilot_wall_seconds": 481.197406,
    "pilot_sessions": 6,
    "observed_wall_seconds_per_all_geometry_runner": 80.19956766666667,
    "distinct_point_binaries": 20,
    "runner_invocations_per_pair_session": 2,
    "total_pair_sessions": 1710,
    "completed_pair_sessions": 0,
    "remaining_pair_sessions": 1710,
    "projected_remaining_lock_hours": 76.18958928333334,
    "hard_gate": False,
}
comparison = audit.envelope_resource_comparison(
    {
        "registers": 96,
        "stack_bytes": 64,
        "local_bytes": 0,
        "shared_bytes": 0,
        "ldl": 62,
        "stl": 31,
        "inferred_active_blocks": 7,
        "inferred_occupancy": 0.4375,
        "opcodes": {"LDC": 12, "LDG": 44, "STL": 31},
    },
    {
        "registers": 130,
        "stack_bytes": 0,
        "local_bytes": 0,
        "shared_bytes": 0,
        "ldl": 0,
        "stl": 0,
        "inferred_active_blocks": 5,
        "inferred_occupancy": 0.3125,
        "opcodes": {"LDC": 13, "LDG": 56, "STL": 0},
    },
    candidate_median_ms=9.0,
    natural_median_ms=10.0,
)
assert comparison["speedup"] == 10.0 / 9.0
assert comparison["wording"] == "11.111% faster"
assert comparison["spill_loads"] == 62
assert comparison["spill_stores"] == 31
assert comparison["actual_active_blocks"] == 7
assert comparison["occupancy"] == 0.4375
assert comparison["opcode_changes"] == {"LDC": -1, "LDG": -12, "STL": 31}
assert audit.envelope_disposition("compiler_failure", None, None, None) == "compile-failed"
assert audit.envelope_disposition("success", "launch_failed", "complete", None) == "launch-failed"
assert audit.envelope_disposition("success", "correctness_failed", "complete", None) == "correctness-failed"
assert audit.envelope_disposition("success", "complete", "sanitizer_failed", None) == "sanitizer-failed"
assert audit.envelope_disposition("success", "complete", "complete", "complete") == "fully-timed"
PY

echo "TASK12_FIXTURES_OK"
if [[ "${TASK12_ONLY:-0}" == 1 ]]; then
    exit 0
fi

MANIFEST="$FIXTURE_ROOT/manifest.json"
WEIGHTS="$FIXTURE_ROOT/weights.json"
BUNDLE="$FIXTURE_ROOT/bundle.bin"
BUILD_FLAGS="$FIXTURE_ROOT/build-flags.txt"
SOURCE_ROOT="$FIXTURE_ROOT/source"
PRODUCTION_ROOT="$FIXTURE_ROOT/production"
TIMING_ROOT="$FIXTURE_ROOT/timing"
NSYS_ROOT="$FIXTURE_ROOT/nsys"
FAKE_RUNNER="$FIXTURE_ROOT/fake-runner"
FAKE_LOCK="$FIXTURE_ROOT/fake-lock"
CALLS="$FIXTURE_ROOT/calls.jsonl"

mkdir -p "$SOURCE_ROOT" "$PRODUCTION_ROOT"
printf 'fixture bundle\n' > "$BUNDLE"
printf 'profile=release;artifact-gen=true;cudaarchs=native\n' > "$BUILD_FLAGS"
printf 'fixture source\n' > "$SOURCE_ROOT/kernel.cu"

python3 - "$MANIFEST" "$WEIGHTS" "$PRODUCTION_ROOT" <<'PY'
import hashlib
import json
import pathlib
import sys

manifest_path = pathlib.Path(sys.argv[1])
weights_path = pathlib.Path(sys.argv[2])
production_root = pathlib.Path(sys.argv[3])
geometries = [
    "cta288_pair",
    "cta96_partitioned",
    "cta96_x0_major",
    "cta96_x1_major",
    "cta96_x2_major",
]

coordinates = []
for index in range(57):
    circuit = f"fixture_circuit_{index // 8:02d}"
    layer = index % 8
    payload = hashlib.sha256(f"coordinate:{circuit}:{layer}".encode()).hexdigest()
    coordinates.append(
        {
            "circuit": circuit,
            "layer": layer,
            "trace_len": 1 << (20 + (index % 3)),
            "shape": {
                "records": index + 1,
                "projections": index + 2,
                "bf_atoms": index + 3,
                "e4_atoms": index + 4,
                "source_uses": index + 5,
                "unique_sources": index + 6,
                "windows": 1,
                "max_relative_column": 7,
                "coefficient_recipes": index + 7,
                "immediates": 0,
            },
            "payload_sha256": payload,
        }
    )

manifest = {
    "bundle_sha256": hashlib.sha256(b"fixture bundle\n").hexdigest(),
    "coordinates": coordinates,
}
manifest_path.write_text(json.dumps(manifest) + "\n")
weights_path.write_text(
    json.dumps(
        {
            "schema_version": 1,
            "profiles": {
                "current_base": {
                    f"fixture_circuit_{index:02d}": 57 for index in range(8)
                },
                "development_recursion_proxy": {
                    "status": "available",
                    "layers": [],
                },
                "future_current_recursion": None,
            },
        }
    )
    + "\n"
)

for coordinate in coordinates:
    stem = f"{coordinate['circuit']}-l{coordinate['layer']}"
    input_hash = hashlib.sha256(f"input:{stem}".encode()).hexdigest()
    cell_bytes = b"".join(
        limb.to_bytes(4, "little")
        for index in range(27)
        for limb in (index, 0, 0, 0)
    )
    checksum = hashlib.sha256(cell_bytes).hexdigest()
    bindings = {
        "bundle_sha256": manifest["bundle_sha256"],
        "coordinate_sha256": coordinate["payload_sha256"],
        "input_sha256": input_hash,
        "source_data_sha256": hashlib.sha256(f"source:{stem}".encode()).hexdigest(),
        "independent_source_sha256": hashlib.sha256(
            f"source:{stem}".encode()
        ).hexdigest(),
        "derived_source_sha256": None,
        "challenge_sha256": hashlib.sha256(f"challenge:{stem}".encode()).hexdigest(),
        "equality_point_sha256": hashlib.sha256(f"eq-point:{stem}".encode()).hexdigest(),
        "direct_eq_sha256": hashlib.sha256(f"direct-eq:{stem}".encode()).hexdigest(),
        "factored_eq_sha256": hashlib.sha256(f"factored-eq:{stem}".encode()).hexdigest(),
        "coefficient_sha256": hashlib.sha256(f"coefficient:{stem}".encode()).hexdigest(),
    }
    directory = production_root / stem
    directory.mkdir(parents=True)
    (directory / "input-bindings.json").write_text(
        json.dumps(
            {
                "version": 1,
                "coordinate": f"{coordinate['circuit']}:{coordinate['layer']}",
                "bindings": bindings,
                "checksum": checksum,
                "geometries": geometries,
                "production_rows": coordinate["trace_len"] // 8,
                "shape": coordinate["shape"],
                "launches": [
                    {
                        "geometry": geometry,
                        "symbol": f"ab_gkr_windowed_r0_{geometry}_kernel",
                        "grid": [
                            (coordinate["trace_len"] // 8 // 32)
                            * (3 if geometry == "cta96_partitioned" else 1),
                            1,
                            1,
                        ],
                        "block": [288 if geometry == "cta288_pair" else 96, 1, 1],
                    }
                    for geometry in geometries
                ],
            }
        )
        + "\n"
    )
PY

python3 - "$AUDIT_RESULTS" <<'PY'
import importlib.util
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
spec = importlib.util.spec_from_file_location("task10_audit_results", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
weights = {
    "profiles": {
        "current_base": {
            "add_sub": 15,
            "jump": 8,
            "mem_word": 9,
            "mem_subword": 3,
            "shift": 4,
            "mul_div": 1,
            "initial": 1,
            "keccak": 15,
            "bigint": 3,
        },
        "development_recursion_proxy": {
            "status": "available",
            "layers": [
                {"circuit": "add_sub_lui_auipc_mop", "invocations": 4},
            ],
        },
        "future_current_recursion": [
            {"circuit": "add_sub_lui_auipc_mop", "invocations": 2},
        ],
    }
}
assert module.weights_for_circuit(weights, "add_sub_lui_auipc_mop") == (15, 4, 2)
assert module.weights_for_circuit(weights, "bigint_with_extended_control") == (3, 0, 0)
assert module.weights_for_circuit(weights, "blake2_g_function") == (None, 0, 0)
weights["profiles"]["future_current_recursion"] = None
assert module.weights_for_circuit(weights, "add_sub_lui_auipc_mop") == (15, 4, None)
for invalid in (True, -1, 1.5):
    weights["profiles"]["current_base"]["add_sub"] = invalid
    try:
        module.weights_for_circuit(weights, "add_sub_lui_auipc_mop")
    except SystemExit:
        pass
    else:
        raise AssertionError(f"invalid current_base weight accepted: {invalid!r}")
PY

cat > "$FAKE_LOCK" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
exec "$@"
SH
chmod +x "$FAKE_LOCK"

cat > "$FAKE_RUNNER" <<'PY'
#!/usr/bin/env python3
import argparse
import hashlib
import json
import os
import pathlib

parser = argparse.ArgumentParser()
parser.add_argument("command")
parser.add_argument("--point", required=True)
parser.add_argument("--coordinate", required=True)
parser.add_argument("--geometries", required=True)
parser.add_argument("--traversal", required=True)
parser.add_argument("--warmups", type=int, required=True)
parser.add_argument("--samples", type=int, required=True)
parser.add_argument("--expected-checksum", required=True)
parser.add_argument("--session-bindings", required=True)
parser.add_argument("--output-dir", required=True)
parser.add_argument("--resume", action="store_true")
args = parser.parse_args()
assert args.command == "timing"
assert args.warmups == 5
assert args.samples == 50

bindings_path = pathlib.Path(args.session_bindings)
assert bindings_path.is_file(), "bindings must exist before the fake GPU marker"
bindings = json.loads(bindings_path.read_text())
for name in (
    "executable_sha256",
    "bundle_sha256",
    "input_sha256",
    "source_tree_sha256",
    "build_flags_sha256",
):
    value = bindings[name]
    assert len(value) == 64 and value == value.lower()
runner_hash = hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
assert bindings["executable_sha256"] == runner_hash
assert bindings["input_sha256"] == bindings["production_bindings"]["input_sha256"]

calls = pathlib.Path(os.environ["TASK10_FIXTURE_CALLS"])
with calls.open("a") as stream:
    stream.write(
        json.dumps(
            {
                "coordinate": args.coordinate,
                "traversal": args.traversal,
                "geometries": args.geometries.split(","),
                "binding_before_marker": True,
            }
        )
        + "\n"
    )

output_dir = pathlib.Path(args.output_dir)
output_dir.mkdir(parents=True, exist_ok=True)
for geometry_index, geometry in enumerate(args.geometries.split(",")):
    circuit, layer_text = args.coordinate.rsplit(":", 1)
    layer = int(layer_text)
    circuit_index = int(circuit.rsplit("_", 1)[1])
    log_trace = 20 + ((circuit_index * 8 + layer) % 3)
    rows = []
    for sample_index in range(args.warmups + args.samples):
        rows.append(
            {
                "version": 1,
                "point": args.point,
                "coordinate": args.coordinate,
                "circuit": circuit,
                "layer": layer,
                "log_trace": log_trace,
                "seed": 0xDEADBEEFCAFEBABE,
                "geometry": geometry,
                "traversal": args.traversal,
                "sample_index": sample_index,
                "warmup": sample_index < args.warmups,
                "milliseconds": float(geometry_index + 1) + sample_index / 1000.0,
                "checksum": args.expected_checksum,
            }
        )
    path = output_dir / f"{geometry}.samples.jsonl"
    path.write_text("".join(json.dumps(row) + "\n" for row in rows))
    task_bindings = dict(bindings["production_bindings"])
    for field in (
        "executable_sha256",
        "bundle_sha256",
        "source_tree_sha256",
        "build_flags_sha256",
    ):
        task_bindings[field] = bindings[field]
    (output_dir / f"{geometry}.checkpoint.json").write_text(
        json.dumps(
            {
                "version": 1,
                "key": {
                    "point": args.point,
                    "circuit": circuit,
                    "layer": layer,
                    "log_trace": log_trace,
                    "seed": 0xDEADBEEFCAFEBABE,
                    "geometry": geometry,
                    "traversal": args.traversal,
                },
                "bindings": task_bindings,
                "state": "complete",
                "rows_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            }
        )
        + "\n"
    )
    production_rows = (1 << log_trace) // 8
    base_grid = production_rows // 32
    launch = {
        "geometry": geometry,
        "symbol": f"ab_gkr_windowed_r0_{geometry}_kernel",
        "grid": [base_grid * (3 if geometry == "cta96_partitioned" else 1), 1, 1],
        "block": [288 if geometry == "cta288_pair" else 96, 1, 1],
    }
    print(
        json.dumps(
            {
                "key": {
                    "point": args.point,
                    "circuit": circuit,
                    "layer": layer,
                    "log_trace": log_trace,
                    "seed": 0xDEADBEEFCAFEBABE,
                    "geometry": geometry,
                    "traversal": args.traversal,
                },
                "reused": False,
                "launch": launch,
                "correctness_checksum": args.expected_checksum,
                "post_session_checksum": args.expected_checksum,
                "warmups": 5,
                "samples": 50,
            },
            separators=(",", ":"),
        )
    )
PY
chmod +x "$FAKE_RUNNER"

export TASK10_FIXTURE_CALLS="$CALLS"

python3 "$RUN_TIMING" run \
    --manifest "$MANIFEST" \
    --runner "$FAKE_RUNNER" \
    --lock-wrapper "$FAKE_LOCK" \
    --bundle "$BUNDLE" \
    --source-root "$SOURCE_ROOT" \
    --build-flags "$BUILD_FLAGS" \
    --production-root "$PRODUCTION_ROOT" \
    --output-root "$TIMING_ROOT"

python3 - "$MANIFEST" "$CALLS" "$TIMING_ROOT" <<'PY'
import json
import pathlib
import sys

manifest = json.loads(pathlib.Path(sys.argv[1]).read_text())
calls = [json.loads(line) for line in pathlib.Path(sys.argv[2]).read_text().splitlines()]
timing_root = pathlib.Path(sys.argv[3])
geometries = [
    "cta288_pair",
    "cta96_partitioned",
    "cta96_x0_major",
    "cta96_x1_major",
    "cta96_x2_major",
]
coordinates = [f"{row['circuit']}:{row['layer']}" for row in manifest["coordinates"]]
assert len(calls) == 114
assert [row["coordinate"] for row in calls[:57]] == coordinates
assert [row["coordinate"] for row in calls[57:]] == list(reversed(coordinates))
for traversal_calls in (calls[:57], calls[57:]):
    for index, call in enumerate(traversal_calls):
        if call["traversal"] == "forward":
            rotation = index % len(geometries)
        else:
            rotation = (-index - 1) % len(geometries)
        assert call["geometries"] == geometries[rotation:] + geometries[:rotation]
        assert call["binding_before_marker"] is True

counts = {}
for path in timing_root.glob("*/*/*.samples.jsonl"):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    assert len(rows) == 55
    assert sum(row["warmup"] for row in rows) == 5
    assert sum(not row["warmup"] for row in rows) == 50
    key = (rows[0]["coordinate"], rows[0]["geometry"])
    warmups, samples = counts.get(key, (0, 0))
    counts[key] = (
        warmups + sum(row["warmup"] for row in rows),
        samples + sum(not row["warmup"] for row in rows),
    )
assert len(counts) == 57 * 5
assert set(counts.values()) == {(10, 100)}
PY

before_reuse="$(wc -l < "$CALLS")"
python3 "$RUN_TIMING" run \
    --manifest "$MANIFEST" \
    --runner "$FAKE_RUNNER" \
    --lock-wrapper "$FAKE_LOCK" \
    --bundle "$BUNDLE" \
    --source-root "$SOURCE_ROOT" \
    --build-flags "$BUILD_FLAGS" \
    --production-root "$PRODUCTION_ROOT" \
    --output-root "$TIMING_ROOT" \
    --resume
test "$(wc -l < "$CALLS")" -eq "$before_reuse"

STARTED_CHECKPOINT="$(find "$TIMING_ROOT" -name session.checkpoint.json | sort | head -1)"
python3 - "$STARTED_CHECKPOINT" <<'PY'
import json
import pathlib
import sys
path = pathlib.Path(sys.argv[1])
value = json.loads(path.read_text())
value["state"] = "started"
value["rows_sha256"] = ""
path.write_text(json.dumps(value) + "\n")
PY
python3 "$RUN_TIMING" run \
    --manifest "$MANIFEST" \
    --runner "$FAKE_RUNNER" \
    --lock-wrapper "$FAKE_LOCK" \
    --bundle "$BUNDLE" \
    --source-root "$SOURCE_ROOT" \
    --build-flags "$BUILD_FLAGS" \
    --production-root "$PRODUCTION_ROOT" \
    --output-root "$TIMING_ROOT" \
    --resume
test "$(wc -l < "$CALLS")" -eq "$((before_reuse + 1))"

MISMATCH_BINDINGS="${STARTED_CHECKPOINT%session.checkpoint.json}session-bindings.json"
cp "$MISMATCH_BINDINGS" "$FIXTURE_ROOT/original-session-bindings.json"
python3 - "$MISMATCH_BINDINGS" <<'PY'
import json
import pathlib
import sys
path = pathlib.Path(sys.argv[1])
value = json.loads(path.read_text())
value["input_sha256"] = "f" * 64
path.write_text(json.dumps(value) + "\n")
PY
if python3 "$RUN_TIMING" run \
    --manifest "$MANIFEST" \
    --runner "$FAKE_RUNNER" \
    --lock-wrapper "$FAKE_LOCK" \
    --bundle "$BUNDLE" \
    --source-root "$SOURCE_ROOT" \
    --build-flags "$BUILD_FLAGS" \
    --production-root "$PRODUCTION_ROOT" \
    --output-root "$TIMING_ROOT" \
    --resume > "$FIXTURE_ROOT/mismatch.stdout" 2> "$FIXTURE_ROOT/mismatch.stderr"; then
    echo "binding mismatch unexpectedly succeeded" >&2
    exit 1
fi
grep -q 'binding mismatch' "$FIXTURE_ROOT/mismatch.stderr"
test "$(wc -l < "$CALLS")" -eq "$((before_reuse + 1))"
mv "$FIXTURE_ROOT/original-session-bindings.json" "$MISMATCH_BINDINGS"

python3 - "$MANIFEST" "$PRODUCTION_ROOT" "$NSYS_ROOT" "$FAKE_RUNNER" "$BUNDLE" <<'PY'
import hashlib
import json
import pathlib
import sqlite3
import sys

manifest = json.loads(pathlib.Path(sys.argv[1]).read_text())
production_root = pathlib.Path(sys.argv[2])
nsys_root = pathlib.Path(sys.argv[3])
runner = pathlib.Path(sys.argv[4])
bundle = pathlib.Path(sys.argv[5])
coordinate_row = sorted(
    manifest["coordinates"],
    key=lambda row: (row["shape"]["records"], f"{row['circuit']}:{row['layer']}"),
)[len(manifest["coordinates"]) // 2]
coordinate = f"{coordinate_row['circuit']}:{coordinate_row['layer']}"
stem = f"{coordinate_row['circuit']}-l{coordinate_row['layer']}"
production = json.loads((production_root / stem / "input-bindings.json").read_text())

def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

for launch in production["launches"]:
    directory = nsys_root / launch["geometry"]
    directory.mkdir(parents=True)
    report = directory / "profile.nsys-rep"
    database = directory / "profile.sqlite"
    report.write_bytes(f"fixture nsys report {launch['geometry']}\n".encode())
    connection = sqlite3.connect(database)
    connection.executescript(
        """
        CREATE TABLE StringIds (id INTEGER PRIMARY KEY, value TEXT NOT NULL);
        CREATE TABLE CUPTI_ACTIVITY_KIND_KERNEL (
            shortName INTEGER NOT NULL,
            gridX INTEGER NOT NULL, gridY INTEGER NOT NULL, gridZ INTEGER NOT NULL,
            blockX INTEGER NOT NULL, blockY INTEGER NOT NULL, blockZ INTEGER NOT NULL
        );
        """
    )
    connection.execute("INSERT INTO StringIds VALUES (1, ?)", (launch["symbol"],))
    connection.execute(
        "INSERT INTO CUPTI_ACTIVITY_KIND_KERNEL VALUES (1, ?, ?, ?, ?, ?, ?)",
        (*launch["grid"], *launch["block"]),
    )
    connection.commit()
    connection.close()
    (directory / "launch-metadata.json").write_text(
        json.dumps(
            {
                "version": 1,
                "coordinate": coordinate,
                "geometry": launch["geometry"],
                "kernel_symbol": launch["symbol"],
                "grid": launch["grid"],
                "block": launch["block"],
                "observed_launch_count": 1,
                "checksum": production["checksum"],
                "report_sha256": sha256(report),
                "sqlite_sha256": sha256(database),
                "executable_sha256": sha256(runner),
                "bundle_sha256": sha256(bundle),
                "input_sha256": production["bindings"]["input_sha256"],
            }
        )
        + "\n"
    )

for coordinate_row in manifest["coordinates"]:
    coordinate = f"{coordinate_row['circuit']}:{coordinate_row['layer']}"
    stem = f"{coordinate_row['circuit']}-l{coordinate_row['layer']}"
    summary_path = production_root / stem / "input-bindings.json"
    summary = json.loads(summary_path.read_text())
    cells = [{"limbs": [index, 0, 0, 0]} for index in range(27)]
    preflight = {
        "requested_bytes": coordinate_row["trace_len"],
        "device_free_bytes": coordinate_row["trace_len"] * 2,
    }
    for launch in summary["launches"]:
        key = {
            "point": "natural",
            "circuit": coordinate_row["circuit"],
            "layer": coordinate_row["layer"],
            "log_trace": coordinate_row["trace_len"].bit_length() - 1,
            "seed": 0xDEADBEEFCAFEBABE,
            "geometry": launch["geometry"],
            "traversal": None,
        }
        row = {
            "version": 1,
            "key": key,
            "bindings": summary["bindings"],
            "production_rows": coordinate_row["trace_len"] // 8,
            "shape": coordinate_row["shape"],
            "preflight": preflight,
            "launch": launch,
            "cells": cells,
            "checksum": summary["checksum"],
            "failure": None,
        }
        prefix = f"natural--{stem}--{launch['geometry']}"
        rows_path = summary_path.parent / f"{prefix}.observations.jsonl"
        checkpoint_path = summary_path.parent / f"{prefix}.checkpoint.json"
        rows_path.write_text(json.dumps(row, separators=(",", ":")) + "\n")
        checkpoint_path.write_text(
            json.dumps(
                {
                    "version": 1,
                    "key": key,
                    "bindings": summary["bindings"],
                    "state": "complete",
                    "rows_sha256": sha256(rows_path),
                }
            )
            + "\n"
        )
PY

python3 "$AUDIT_RESULTS" natural \
    --manifest "$MANIFEST" \
    --weights "$WEIGHTS" \
    --timing-root "$TIMING_ROOT" \
    --nsys-root "$NSYS_ROOT" \
    --production-root "$PRODUCTION_ROOT" \
    --output-dir "$FIXTURE_ROOT/reports" \
    > "$FIXTURE_ROOT/audit.stdout"
grep -q 'WINDOWED_R0_NSYS_AUDIT_OK' "$FIXTURE_ROOT/audit.stdout"
grep -Eq '[0-9]+([.][0-9]+)?% (faster|slower)' "$FIXTURE_ROOT/audit.stdout"
if grep -Eq -- '-[0-9]+([.][0-9]+)?%' "$FIXTURE_ROOT/audit.stdout"; then
    echo "ambiguous signed timing percentage found" >&2
    exit 1
fi

NSYS_METADATA="$NSYS_ROOT/cta288_pair/launch-metadata.json"
cp "$NSYS_METADATA" "$FIXTURE_ROOT/original-nsys-count-metadata.json"
python3 - "$NSYS_METADATA" <<'PY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
value = json.loads(path.read_text())
value["observed_launch_count"] = True
path.write_text(json.dumps(value) + "\n")
PY
if python3 "$AUDIT_RESULTS" natural \
    --manifest "$MANIFEST" \
    --weights "$WEIGHTS" \
    --timing-root "$TIMING_ROOT" \
    --nsys-root "$NSYS_ROOT" \
    --production-root "$PRODUCTION_ROOT" \
    --output-dir "$FIXTURE_ROOT/tampered-nsys-count-reports" \
    > "$FIXTURE_ROOT/tampered-nsys-count.stdout" \
    2> "$FIXTURE_ROOT/tampered-nsys-count.stderr"; then
    echo "boolean nsys launch count unexpectedly succeeded" >&2
    exit 1
fi
grep -q 'nsys target launch cardinality type mismatch' "$FIXTURE_ROOT/tampered-nsys-count.stderr"
mv "$FIXTURE_ROOT/original-nsys-count-metadata.json" "$NSYS_METADATA"

cp "$NSYS_METADATA" "$FIXTURE_ROOT/original-nsys-metadata.json"
python3 - "$NSYS_METADATA" <<'PY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
value = json.loads(path.read_text())
value["grid"][0] += 1
path.write_text(json.dumps(value) + "\n")
PY
if python3 "$AUDIT_RESULTS" natural \
    --manifest "$MANIFEST" \
    --weights "$WEIGHTS" \
    --timing-root "$TIMING_ROOT" \
    --nsys-root "$NSYS_ROOT" \
    --production-root "$PRODUCTION_ROOT" \
    --output-dir "$FIXTURE_ROOT/tampered-reports" \
    > "$FIXTURE_ROOT/tampered-nsys.stdout" \
    2> "$FIXTURE_ROOT/tampered-nsys.stderr"; then
    echo "tampered nsys metadata unexpectedly succeeded" >&2
    exit 1
fi
grep -q 'nsys grid mismatch' "$FIXTURE_ROOT/tampered-nsys.stderr"
mv "$FIXTURE_ROOT/original-nsys-metadata.json" "$NSYS_METADATA"

TIMING_ROWS="$TIMING_ROOT/fixture_circuit_00-l0/forward/cta288_pair.samples.jsonl"
TIMING_SESSION="${TIMING_ROWS%/cta288_pair.samples.jsonl}/session.checkpoint.json"
cp "$TIMING_ROWS" "$FIXTURE_ROOT/original-timing-rows.jsonl"
cp "$TIMING_SESSION" "$FIXTURE_ROOT/original-timing-session.json"
python3 - "$TIMING_ROWS" "$TIMING_SESSION" <<'PY'
import hashlib
import json
import pathlib
import sys

rows_path = pathlib.Path(sys.argv[1])
session_path = pathlib.Path(sys.argv[2])
rows = [json.loads(line) for line in rows_path.read_text().splitlines()]
rows[0]["log_trace"] += 1
rows_path.write_text("".join(json.dumps(row) + "\n" for row in rows))
digest = hashlib.sha256()
directory = rows_path.parent
for geometry in (
    "cta288_pair",
    "cta96_partitioned",
    "cta96_x0_major",
    "cta96_x1_major",
    "cta96_x2_major",
):
    path = directory / f"{geometry}.samples.jsonl"
    relative = path.name.encode()
    contents = path.read_bytes()
    digest.update(len(relative).to_bytes(8, "little"))
    digest.update(relative)
    digest.update(len(contents).to_bytes(8, "little"))
    digest.update(contents)
session = json.loads(session_path.read_text())
session["rows_sha256"] = digest.hexdigest()
session_path.write_text(json.dumps(session) + "\n")
PY
if python3 "$AUDIT_RESULTS" natural \
    --manifest "$MANIFEST" --weights "$WEIGHTS" \
    --timing-root "$TIMING_ROOT" --nsys-root "$NSYS_ROOT" \
    --production-root "$PRODUCTION_ROOT" \
    --output-dir "$FIXTURE_ROOT/tampered-timing-reports" \
    > "$FIXTURE_ROOT/tampered-timing.stdout" \
    2> "$FIXTURE_ROOT/tampered-timing.stderr"; then
    echo "tampered timing key unexpectedly succeeded" >&2
    exit 1
fi
grep -q 'timing key mismatch' "$FIXTURE_ROOT/tampered-timing.stderr"
mv "$FIXTURE_ROOT/original-timing-rows.jsonl" "$TIMING_ROWS"
mv "$FIXTURE_ROOT/original-timing-session.json" "$TIMING_SESSION"

FORWARD_BINDINGS="$TIMING_ROOT/fixture_circuit_00-l0/forward/session-bindings.json"
REVERSE_BINDINGS="$TIMING_ROOT/fixture_circuit_00-l0/reverse/session-bindings.json"
FORWARD_SESSION="$TIMING_ROOT/fixture_circuit_00-l0/forward/session.checkpoint.json"
REVERSE_SESSION="$TIMING_ROOT/fixture_circuit_00-l0/reverse/session.checkpoint.json"
FORWARD_GEOMETRY="$TIMING_ROOT/fixture_circuit_00-l0/forward/cta288_pair.checkpoint.json"
for path in \
    "$FORWARD_BINDINGS" "$REVERSE_BINDINGS" \
    "$FORWARD_SESSION" "$REVERSE_SESSION"; do
    cp "$path" "$FIXTURE_ROOT/original-$(basename "${path%/*}")-$(basename "$path")"
done
python3 - \
    "$FORWARD_BINDINGS" "$REVERSE_BINDINGS" \
    "$FORWARD_SESSION" "$REVERSE_SESSION" <<'PY'
import hashlib
import json
import pathlib
import sys

forward_bindings, reverse_bindings, forward_session, reverse_session = map(
    pathlib.Path, sys.argv[1:]
)
for bindings_path, session_path in (
    (forward_bindings, forward_session),
    (reverse_bindings, reverse_session),
):
    bindings = json.loads(bindings_path.read_text())
    bindings["version"] = 2
    bindings["point"] = "not-natural"
    bindings_path.write_text(json.dumps(bindings) + "\n")
    session = json.loads(session_path.read_text())
    session["version"] = 2
    session["bindings_sha256"] = hashlib.sha256(bindings_path.read_bytes()).hexdigest()
    session_path.write_text(json.dumps(session) + "\n")
PY
if python3 "$AUDIT_RESULTS" natural \
    --manifest "$MANIFEST" --weights "$WEIGHTS" \
    --timing-root "$TIMING_ROOT" --nsys-root "$NSYS_ROOT" \
    --production-root "$PRODUCTION_ROOT" \
    --output-dir "$FIXTURE_ROOT/tampered-session-identity-reports" \
    > "$FIXTURE_ROOT/tampered-session-identity.stdout" \
    2> "$FIXTURE_ROOT/tampered-session-identity.stderr"; then
    echo "tampered session identity unexpectedly succeeded" >&2
    exit 1
fi
grep -q 'session binding identity mismatch' "$FIXTURE_ROOT/tampered-session-identity.stderr"
for path in \
    "$FORWARD_BINDINGS" "$REVERSE_BINDINGS" \
    "$FORWARD_SESSION" "$REVERSE_SESSION"; do
    mv "$FIXTURE_ROOT/original-$(basename "${path%/*}")-$(basename "$path")" "$path"
done

for path in "$FORWARD_BINDINGS" "$REVERSE_BINDINGS"; do
    cp "$path" "$FIXTURE_ROOT/original-bool-$(basename "${path%/*}")-bindings.json"
done
for path in "$FORWARD_SESSION" "$REVERSE_SESSION"; do
    cp "$path" "$FIXTURE_ROOT/original-bool-$(basename "${path%/*}")-session.json"
done
python3 - \
    "$FORWARD_BINDINGS" "$REVERSE_BINDINGS" \
    "$FORWARD_SESSION" "$REVERSE_SESSION" <<'PY'
import hashlib
import json
import pathlib
import sys

forward_bindings, reverse_bindings, forward_session, reverse_session = map(
    pathlib.Path, sys.argv[1:]
)
for bindings_path, session_path in (
    (forward_bindings, forward_session),
    (reverse_bindings, reverse_session),
):
    bindings = json.loads(bindings_path.read_text())
    bindings["version"] = True
    bindings_path.write_text(json.dumps(bindings) + "\n")
    session = json.loads(session_path.read_text())
    session["bindings_sha256"] = hashlib.sha256(bindings_path.read_bytes()).hexdigest()
    session_path.write_text(json.dumps(session) + "\n")
PY
if python3 "$AUDIT_RESULTS" natural \
    --manifest "$MANIFEST" --weights "$WEIGHTS" \
    --timing-root "$TIMING_ROOT" --nsys-root "$NSYS_ROOT" \
    --production-root "$PRODUCTION_ROOT" \
    --output-dir "$FIXTURE_ROOT/tampered-binding-version-type-reports" \
    > "$FIXTURE_ROOT/tampered-binding-version-type.stdout" \
    2> "$FIXTURE_ROOT/tampered-binding-version-type.stderr"; then
    echo "boolean session binding version unexpectedly succeeded" >&2
    exit 1
fi
grep -q 'session binding identity mismatch' "$FIXTURE_ROOT/tampered-binding-version-type.stderr"
for path in "$FORWARD_BINDINGS" "$REVERSE_BINDINGS"; do
    mv "$FIXTURE_ROOT/original-bool-$(basename "${path%/*}")-bindings.json" "$path"
done
for path in "$FORWARD_SESSION" "$REVERSE_SESSION"; do
    mv "$FIXTURE_ROOT/original-bool-$(basename "${path%/*}")-session.json" "$path"
done

cp "$FORWARD_SESSION" "$FIXTURE_ROOT/original-session-version.json"
python3 - "$FORWARD_SESSION" <<'PY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
checkpoint = json.loads(path.read_text())
checkpoint["version"] = True
path.write_text(json.dumps(checkpoint) + "\n")
PY
if python3 "$AUDIT_RESULTS" natural \
    --manifest "$MANIFEST" --weights "$WEIGHTS" \
    --timing-root "$TIMING_ROOT" --nsys-root "$NSYS_ROOT" \
    --production-root "$PRODUCTION_ROOT" \
    --output-dir "$FIXTURE_ROOT/tampered-session-version-reports" \
    > "$FIXTURE_ROOT/tampered-session-version.stdout" \
    2> "$FIXTURE_ROOT/tampered-session-version.stderr"; then
    echo "tampered session checkpoint version unexpectedly succeeded" >&2
    exit 1
fi
grep -q 'session checkpoint version mismatch' "$FIXTURE_ROOT/tampered-session-version.stderr"
mv "$FIXTURE_ROOT/original-session-version.json" "$FORWARD_SESSION"

cp "$FORWARD_GEOMETRY" "$FIXTURE_ROOT/original-geometry-version.json"
python3 - "$FORWARD_GEOMETRY" <<'PY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
checkpoint = json.loads(path.read_text())
checkpoint["version"] = True
path.write_text(json.dumps(checkpoint) + "\n")
PY
if python3 "$AUDIT_RESULTS" natural \
    --manifest "$MANIFEST" --weights "$WEIGHTS" \
    --timing-root "$TIMING_ROOT" --nsys-root "$NSYS_ROOT" \
    --production-root "$PRODUCTION_ROOT" \
    --output-dir "$FIXTURE_ROOT/tampered-geometry-version-reports" \
    --strict --runner "$FAKE_RUNNER" --bundle "$BUNDLE" \
    --source-root "$SOURCE_ROOT" --build-flags "$BUILD_FLAGS" \
    > "$FIXTURE_ROOT/tampered-geometry-version.stdout" \
    2> "$FIXTURE_ROOT/tampered-geometry-version.stderr"; then
    echo "tampered geometry checkpoint version unexpectedly succeeded" >&2
    exit 1
fi
grep -q 'geometry checkpoint version mismatch' "$FIXTURE_ROOT/tampered-geometry-version.stderr"
mv "$FIXTURE_ROOT/original-geometry-version.json" "$FORWARD_GEOMETRY"

cp "$TIMING_ROWS" "$FIXTURE_ROOT/original-warmup-rows.jsonl"
cp "$TIMING_SESSION" "$FIXTURE_ROOT/original-warmup-session.json"
TIMING_GEOMETRY="${TIMING_ROWS%.samples.jsonl}.checkpoint.json"
cp "$TIMING_GEOMETRY" "$FIXTURE_ROOT/original-warmup-geometry.json"
python3 - "$TIMING_ROWS" "$TIMING_GEOMETRY" "$TIMING_SESSION" <<'PY'
import hashlib
import json
import pathlib
import sys

rows_path, geometry_path, session_path = map(pathlib.Path, sys.argv[1:])
rows = [json.loads(line) for line in rows_path.read_text().splitlines()]
rows[0]["warmup"] = False
rows[5]["warmup"] = True
rows_path.write_text("".join(json.dumps(row) + "\n" for row in rows))
geometry = json.loads(geometry_path.read_text())
geometry["rows_sha256"] = hashlib.sha256(rows_path.read_bytes()).hexdigest()
geometry_path.write_text(json.dumps(geometry) + "\n")
digest = hashlib.sha256()
for name in (
    "cta288_pair",
    "cta96_partitioned",
    "cta96_x0_major",
    "cta96_x1_major",
    "cta96_x2_major",
):
    path = rows_path.parent / f"{name}.samples.jsonl"
    relative = path.name.encode()
    contents = path.read_bytes()
    digest.update(len(relative).to_bytes(8, "little"))
    digest.update(relative)
    digest.update(len(contents).to_bytes(8, "little"))
    digest.update(contents)
session = json.loads(session_path.read_text())
session["rows_sha256"] = digest.hexdigest()
session_path.write_text(json.dumps(session) + "\n")
PY
if python3 "$AUDIT_RESULTS" natural \
    --manifest "$MANIFEST" --weights "$WEIGHTS" \
    --timing-root "$TIMING_ROOT" --nsys-root "$NSYS_ROOT" \
    --production-root "$PRODUCTION_ROOT" \
    --output-dir "$FIXTURE_ROOT/tampered-warmup-order-reports" \
    > "$FIXTURE_ROOT/tampered-warmup-order.stdout" \
    2> "$FIXTURE_ROOT/tampered-warmup-order.stderr"; then
    echo "tampered warmup order unexpectedly succeeded" >&2
    exit 1
fi
grep -q 'warmup ordering mismatch' "$FIXTURE_ROOT/tampered-warmup-order.stderr"
mv "$FIXTURE_ROOT/original-warmup-rows.jsonl" "$TIMING_ROWS"
mv "$FIXTURE_ROOT/original-warmup-session.json" "$TIMING_SESSION"
mv "$FIXTURE_ROOT/original-warmup-geometry.json" "$TIMING_GEOMETRY"

cp "$TIMING_ROWS" "$FIXTURE_ROOT/original-warmup-type-rows.jsonl"
cp "$TIMING_SESSION" "$FIXTURE_ROOT/original-warmup-type-session.json"
cp "$TIMING_GEOMETRY" "$FIXTURE_ROOT/original-warmup-type-geometry.json"
python3 - "$TIMING_ROWS" "$TIMING_GEOMETRY" "$TIMING_SESSION" <<'PY'
import hashlib
import json
import pathlib
import sys

rows_path, geometry_path, session_path = map(pathlib.Path, sys.argv[1:])
rows = [json.loads(line) for line in rows_path.read_text().splitlines()]
for row in rows:
    row["warmup"] = int(row["warmup"])
rows_path.write_text("".join(json.dumps(row) + "\n" for row in rows))
geometry = json.loads(geometry_path.read_text())
geometry["rows_sha256"] = hashlib.sha256(rows_path.read_bytes()).hexdigest()
geometry_path.write_text(json.dumps(geometry) + "\n")
digest = hashlib.sha256()
for name in (
    "cta288_pair",
    "cta96_partitioned",
    "cta96_x0_major",
    "cta96_x1_major",
    "cta96_x2_major",
):
    path = rows_path.parent / f"{name}.samples.jsonl"
    relative = path.name.encode()
    contents = path.read_bytes()
    digest.update(len(relative).to_bytes(8, "little"))
    digest.update(relative)
    digest.update(len(contents).to_bytes(8, "little"))
    digest.update(contents)
session = json.loads(session_path.read_text())
session["rows_sha256"] = digest.hexdigest()
session_path.write_text(json.dumps(session) + "\n")
PY
if python3 "$AUDIT_RESULTS" natural \
    --manifest "$MANIFEST" --weights "$WEIGHTS" \
    --timing-root "$TIMING_ROOT" --nsys-root "$NSYS_ROOT" \
    --production-root "$PRODUCTION_ROOT" \
    --output-dir "$FIXTURE_ROOT/tampered-warmup-type-reports" \
    > "$FIXTURE_ROOT/tampered-warmup-type.stdout" \
    2> "$FIXTURE_ROOT/tampered-warmup-type.stderr"; then
    echo "non-boolean warmup flags unexpectedly succeeded" >&2
    exit 1
fi
grep -q 'warmup flag type mismatch' "$FIXTURE_ROOT/tampered-warmup-type.stderr"
mv "$FIXTURE_ROOT/original-warmup-type-rows.jsonl" "$TIMING_ROWS"
mv "$FIXTURE_ROOT/original-warmup-type-session.json" "$TIMING_SESSION"
mv "$FIXTURE_ROOT/original-warmup-type-geometry.json" "$TIMING_GEOMETRY"

tamper_timing_types_and_rehash() {
    python3 - "$1" "$TIMING_ROWS" "$TIMING_GEOMETRY" "$TIMING_SESSION" <<'PY'
import hashlib
import json
import pathlib
import sys

mode = sys.argv[1]
rows_path, geometry_path, session_path = map(pathlib.Path, sys.argv[2:])
rows = [json.loads(line) for line in rows_path.read_text().splitlines()]
if mode == "key":
    rows[0]["layer"] = False
elif mode == "sample-index":
    rows[0]["sample_index"] = False
    rows[1]["sample_index"] = True
elif mode == "milliseconds":
    rows[0]["milliseconds"] = True
else:
    raise AssertionError(mode)
rows_path.write_text("".join(json.dumps(row) + "\n" for row in rows))
geometry = json.loads(geometry_path.read_text())
geometry["rows_sha256"] = hashlib.sha256(rows_path.read_bytes()).hexdigest()
geometry_path.write_text(json.dumps(geometry) + "\n")
digest = hashlib.sha256()
for name in (
    "cta288_pair",
    "cta96_partitioned",
    "cta96_x0_major",
    "cta96_x1_major",
    "cta96_x2_major",
):
    path = rows_path.parent / f"{name}.samples.jsonl"
    relative = path.name.encode()
    contents = path.read_bytes()
    digest.update(len(relative).to_bytes(8, "little"))
    digest.update(relative)
    digest.update(len(contents).to_bytes(8, "little"))
    digest.update(contents)
session = json.loads(session_path.read_text())
session["rows_sha256"] = digest.hexdigest()
session_path.write_text(json.dumps(session) + "\n")
PY
}

cp "$TIMING_ROWS" "$FIXTURE_ROOT/original-key-type-rows.jsonl"
cp "$TIMING_SESSION" "$FIXTURE_ROOT/original-key-type-session.json"
cp "$TIMING_GEOMETRY" "$FIXTURE_ROOT/original-key-type-geometry.json"
tamper_timing_types_and_rehash key
if python3 "$AUDIT_RESULTS" natural \
    --manifest "$MANIFEST" --weights "$WEIGHTS" \
    --timing-root "$TIMING_ROOT" --nsys-root "$NSYS_ROOT" \
    --production-root "$PRODUCTION_ROOT" \
    --output-dir "$FIXTURE_ROOT/tampered-key-type-reports" \
    > "$FIXTURE_ROOT/tampered-key-type.stdout" \
    2> "$FIXTURE_ROOT/tampered-key-type.stderr"; then
    echo "boolean timing key field unexpectedly succeeded" >&2
    exit 1
fi
grep -q 'timing key mismatch' "$FIXTURE_ROOT/tampered-key-type.stderr"
mv "$FIXTURE_ROOT/original-key-type-rows.jsonl" "$TIMING_ROWS"
mv "$FIXTURE_ROOT/original-key-type-session.json" "$TIMING_SESSION"
mv "$FIXTURE_ROOT/original-key-type-geometry.json" "$TIMING_GEOMETRY"

cp "$TIMING_ROWS" "$FIXTURE_ROOT/original-index-type-rows.jsonl"
cp "$TIMING_SESSION" "$FIXTURE_ROOT/original-index-type-session.json"
cp "$TIMING_GEOMETRY" "$FIXTURE_ROOT/original-index-type-geometry.json"
tamper_timing_types_and_rehash sample-index
if python3 "$AUDIT_RESULTS" natural \
    --manifest "$MANIFEST" --weights "$WEIGHTS" \
    --timing-root "$TIMING_ROOT" --nsys-root "$NSYS_ROOT" \
    --production-root "$PRODUCTION_ROOT" \
    --output-dir "$FIXTURE_ROOT/tampered-index-type-reports" \
    > "$FIXTURE_ROOT/tampered-index-type.stdout" \
    2> "$FIXTURE_ROOT/tampered-index-type.stderr"; then
    echo "boolean sample indices unexpectedly succeeded" >&2
    exit 1
fi
grep -q 'sample index type mismatch' "$FIXTURE_ROOT/tampered-index-type.stderr"
mv "$FIXTURE_ROOT/original-index-type-rows.jsonl" "$TIMING_ROWS"
mv "$FIXTURE_ROOT/original-index-type-session.json" "$TIMING_SESSION"
mv "$FIXTURE_ROOT/original-index-type-geometry.json" "$TIMING_GEOMETRY"

cp "$TIMING_ROWS" "$FIXTURE_ROOT/original-duration-type-rows.jsonl"
cp "$TIMING_SESSION" "$FIXTURE_ROOT/original-duration-type-session.json"
cp "$TIMING_GEOMETRY" "$FIXTURE_ROOT/original-duration-type-geometry.json"
tamper_timing_types_and_rehash milliseconds
if python3 "$AUDIT_RESULTS" natural \
    --manifest "$MANIFEST" --weights "$WEIGHTS" \
    --timing-root "$TIMING_ROOT" --nsys-root "$NSYS_ROOT" \
    --production-root "$PRODUCTION_ROOT" \
    --output-dir "$FIXTURE_ROOT/tampered-duration-type-reports" \
    > "$FIXTURE_ROOT/tampered-duration-type.stdout" \
    2> "$FIXTURE_ROOT/tampered-duration-type.stderr"; then
    echo "boolean timing duration unexpectedly succeeded" >&2
    exit 1
fi
grep -q 'timing duration type mismatch' "$FIXTURE_ROOT/tampered-duration-type.stderr"
mv "$FIXTURE_ROOT/original-duration-type-rows.jsonl" "$TIMING_ROWS"
mv "$FIXTURE_ROOT/original-duration-type-session.json" "$TIMING_SESSION"
mv "$FIXTURE_ROOT/original-duration-type-geometry.json" "$TIMING_GEOMETRY"

PRODUCTION_SUMMARY="$PRODUCTION_ROOT/fixture_circuit_00-l0/input-bindings.json"
cp "$PRODUCTION_SUMMARY" "$FIXTURE_ROOT/original-production-summary.json"
python3 - "$PRODUCTION_SUMMARY" <<'PY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
value = json.loads(path.read_text())
value["production_rows"] = value.get("production_rows", 0) + 1
path.write_text(json.dumps(value) + "\n")
PY
if python3 "$AUDIT_RESULTS" natural \
    --manifest "$MANIFEST" --weights "$WEIGHTS" \
    --timing-root "$TIMING_ROOT" --nsys-root "$NSYS_ROOT" \
    --production-root "$PRODUCTION_ROOT" \
    --output-dir "$FIXTURE_ROOT/tampered-production-reports" \
    > "$FIXTURE_ROOT/tampered-production.stdout" \
    2> "$FIXTURE_ROOT/tampered-production.stderr"; then
    echo "tampered production summary unexpectedly succeeded" >&2
    exit 1
fi
grep -q 'production summary mismatch' "$FIXTURE_ROOT/tampered-production.stderr"
mv "$FIXTURE_ROOT/original-production-summary.json" "$PRODUCTION_SUMMARY"

TIMING_STDOUT="$TIMING_ROOT/fixture_circuit_00-l0/forward/stdout.jsonl"
cp "$TIMING_STDOUT" "$FIXTURE_ROOT/original-timing-stdout.jsonl"
python3 - "$TIMING_STDOUT" <<'PY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
rows = [json.loads(line) for line in path.read_text().splitlines()]
rows[0]["post_session_checksum"] = "f" * 64
path.write_text("".join(json.dumps(row) + "\n" for row in rows))
PY
if python3 "$AUDIT_RESULTS" natural \
    --manifest "$MANIFEST" --weights "$WEIGHTS" \
    --timing-root "$TIMING_ROOT" --nsys-root "$NSYS_ROOT" \
    --production-root "$PRODUCTION_ROOT" \
    --output-dir "$FIXTURE_ROOT/tampered-stdout-reports" \
    > "$FIXTURE_ROOT/tampered-stdout.stdout" \
    2> "$FIXTURE_ROOT/tampered-stdout.stderr"; then
    echo "tampered timing stdout unexpectedly succeeded" >&2
    exit 1
fi
grep -q 'timing stdout mismatch' "$FIXTURE_ROOT/tampered-stdout.stderr"
mv "$FIXTURE_ROOT/original-timing-stdout.jsonl" "$TIMING_STDOUT"

echo "TASK10_FIXTURES_OK"
