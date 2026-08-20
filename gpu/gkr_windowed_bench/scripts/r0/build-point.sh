#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
BUILD_ROOT="${R0_BUILD_POINT_ROOT:-$REPO_ROOT/target/windowed-gkr-r0-corpus/builds}"
DEVICE_JSON="${R0_BUILD_POINT_DEVICE_JSON:-$REPO_ROOT/target/windowed-gkr-r0-corpus/task11/device.json}"
CARGO_BIN="${CARGO:-cargo}"

usage() {
    echo "usage: $0 <geometry> <natural|launch|maxreg|combined> <min_blocks> <maxreg>" >&2
    exit 2
}

[[ $# -eq 4 ]] || usage
geometry="$1"
kind="$2"
min_blocks="$3"
maxreg="$4"

case "$geometry" in
    cta288_pair)
        geometry_upper="CTA288_PAIR"
        threads=288
        ;;
    cta96_partitioned)
        geometry_upper="CTA96_PARTITIONED"
        threads=96
        ;;
    cta96_x0_major)
        geometry_upper="CTA96_X0_MAJOR"
        threads=96
        ;;
    cta96_x1_major)
        geometry_upper="CTA96_X1_MAJOR"
        threads=96
        ;;
    cta96_x2_major)
        geometry_upper="CTA96_X2_MAJOR"
        threads=96
        ;;
    *)
        echo "unknown R0 geometry: $geometry" >&2
        exit 2
        ;;
esac
case "$kind" in
    natural|launch|maxreg|combined) ;;
    *)
        echo "unknown R0 point kind: $kind" >&2
        exit 2
        ;;
esac
[[ "$min_blocks" =~ ^[0-9]+$ ]] || {
    echo "min_blocks must be a nonnegative integer" >&2
    exit 2
}
[[ "$maxreg" =~ ^[0-9]+$ ]] || {
    echo "maxreg must be a nonnegative integer" >&2
    exit 2
}

case "$kind" in
    natural)
        [[ "$min_blocks" -eq 0 && "$maxreg" -eq 0 ]] || {
            echo "natural requires min_blocks=0 and maxreg=0" >&2
            exit 2
        }
        ;;
    launch)
        [[ "$min_blocks" -gt 0 && "$maxreg" -eq 0 ]] || {
            echo "launch requires positive min_blocks and maxreg=0" >&2
            exit 2
        }
        ;;
    maxreg)
        [[ "$min_blocks" -eq 0 && "$maxreg" -gt 0 ]] || {
            echo "maxreg requires min_blocks=0 and positive maxreg" >&2
            exit 2
        }
        ;;
    combined)
        [[ "$min_blocks" -gt 0 && "$maxreg" -gt 0 ]] || {
            echo "combined requires positive min_blocks and maxreg" >&2
            exit 2
        }
        ;;
esac

all_geometries=(
    CTA288_PAIR
    CTA96_PARTITIONED
    CTA96_X0_MAJOR
    CTA96_X1_MAJOR
    CTA96_X2_MAJOR
)
for candidate_geometry in "${all_geometries[@]}"; do
    for control in MIN_BLOCKS MAXREG; do
        variable="GPU_GKR_WINDOWED_R0_${candidate_geometry}_${control}"
        if [[ -v "$variable" ]]; then
            echo "refusing inherited R0 build control: $variable" >&2
            exit 2
        fi
    done
done

[[ -f "$DEVICE_JSON" ]] || {
    echo "missing device description: $DEVICE_JSON" >&2
    exit 2
}
read -r max_blocks_per_sm max_threads_per_sm register_granularity max_registers_per_thread < <(
    python3 - "$DEVICE_JSON" <<'PY'
import json
import pathlib
import sys

value = json.loads(pathlib.Path(sys.argv[1]).read_text())
required = (
    "max_blocks_per_sm",
    "max_threads_per_sm",
    "register_allocation_granularity",
)
for key in required:
    item = value.get(key)
    if isinstance(item, bool) or not isinstance(item, int) or item <= 0:
        raise SystemExit(f"invalid device field: {key}")
maximum = value.get("max_registers_per_thread", 255)
if isinstance(maximum, bool) or not isinstance(maximum, int) or maximum <= 0:
    raise SystemExit("invalid device field: max_registers_per_thread")
print(value["max_blocks_per_sm"], value["max_threads_per_sm"],
      value["register_allocation_granularity"], maximum)
PY
)
physical_block_limit=$((max_threads_per_sm / threads))
if ((max_blocks_per_sm < physical_block_limit)); then
    physical_block_limit=$max_blocks_per_sm
fi
if ((min_blocks > physical_block_limit)); then
    echo "min_blocks=$min_blocks is impossible for $geometry (limit $physical_block_limit)" >&2
    exit 2
fi
if ((maxreg > max_registers_per_thread)); then
    echo "maxreg=$maxreg exceeds the device limit $max_registers_per_thread" >&2
    exit 2
fi
if ((maxreg > 0 && maxreg % register_granularity != 0)); then
    echo "maxreg=$maxreg is not rounded to granularity $register_granularity" >&2
    exit 2
fi

point_id="${geometry}--${kind}-b${min_blocks}-r${maxreg}"
point_dir="$BUILD_ROOT/$point_id"
target_root="$BUILD_ROOT/.cargo-targets/$point_id"
claim_root="$BUILD_ROOT/.claims"
claim_dir="$claim_root/$point_id"
mkdir -p "$BUILD_ROOT" "$BUILD_ROOT/.cargo-targets" "$claim_root"
if [[ -e "$point_dir" ]]; then
    if [[ -f "$point_dir/COMPLETE" ]]; then
        echo "refusing to overwrite complete point: $point_id" >&2
    else
        echo "refusing to overwrite existing incomplete point: $point_id" >&2
    fi
    exit 2
fi
if ! mkdir "$claim_dir"; then
    echo "refusing concurrent build of point: $point_id" >&2
    exit 2
fi
if [[ -e "$point_dir" ]]; then
    rmdir "$claim_dir"
    if [[ -f "$point_dir/COMPLETE" ]]; then
        echo "refusing to overwrite complete point: $point_id" >&2
    else
        echo "refusing to overwrite existing incomplete point: $point_id" >&2
    fi
    exit 2
fi

stage=""
cleanup_stage() {
    if [[ -n "$stage" && -d "$stage" ]]; then
        rm -rf -- "$stage"
    fi
    if [[ -d "$claim_dir" ]]; then
        rmdir "$claim_dir"
    fi
}
trap cleanup_stage EXIT
stage="$(mktemp -d "$BUILD_ROOT/.${point_id}.tmp.XXXXXX")"

symbol="ab_gkr_windowed_r0_${geometry}_kernel"
wrapper="windowed_r0_${geometry}.cu"
min_variable="GPU_GKR_WINDOWED_R0_${geometry_upper}_MIN_BLOCKS"
maxreg_variable="GPU_GKR_WINDOWED_R0_${geometry_upper}_MAXREG"

python3 - "$stage/point.json" "$point_id" "$geometry" "$kind" \
    "$min_blocks" "$maxreg" "$threads" "$symbol" "$DEVICE_JSON" <<'PY'
import hashlib
import json
import pathlib
import sys

path, point_id, geometry, kind, min_blocks, maxreg, threads, symbol, device_path = sys.argv[1:]
device_bytes = pathlib.Path(device_path).read_bytes()
value = {
    "version": 1,
    "point_id": point_id,
    "geometry": geometry,
    "kind": kind,
    "min_blocks": int(min_blocks),
    "maxreg": int(maxreg),
    "threads": int(threads),
    "symbol": symbol,
    "device_sha256": hashlib.sha256(device_bytes).hexdigest(),
}
pathlib.Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
PY
cp "$DEVICE_JSON" "$stage/device.json"

(
    cd "$REPO_ROOT"
    find gpu/gkr_windowed_bench \
        \( -path 'gpu/gkr_windowed_bench/target' -o -path 'gpu/gkr_windowed_bench/target/*' \) -prune -o \
        -type f \
        \( -path '*/src/*' -o -path '*/native/*' -o -path '*/artifacts/*' \
           -o -path '*/scripts/r0/*' -o -name Cargo.toml -o -name build.rs \) \
        ! -path '*/__pycache__/*' ! -name '*.pyc' \
        -print0 \
        | sort -z \
        | xargs -0 sha256sum
) > "$stage/source-files.sha256"
sha256sum "$stage/source-files.sha256" | awk '{print $1}' > "$stage/source-tree.sha256.tmp"
mv "$stage/source-tree.sha256.tmp" "$stage/source-tree.sha256"

{
    printf 'CUDAARCHS=native\n'
    printf 'CARGO_TARGET_TIMING=%s\n' "$target_root/timing"
    printf 'CARGO_TARGET_LINEINFO=%s\n' "$target_root/lineinfo"
    printf 'RUSTC_WRAPPER=%s\n' "${RUSTC_WRAPPER:-}"
    printf 'RUSTFLAGS=%s\n' "${RUSTFLAGS:-}"
    printf '%s=%s\n' "$min_variable" "$min_blocks"
    printf '%s=%s\n' "$maxreg_variable" "$maxreg"
} > "$stage/environment.txt"

{
    "$CARGO_BIN" --version
    rustc --version
    nvcc --version
    cuobjdump --version
    cmake --version
    clang --version
} > "$stage/compiler-versions.txt" 2>&1

finalize_publish() {
    local outcome="$1"
    local phase="$2"
    local exit_code="$3"
    if [[ ! -f "$stage/outcome.json" ]]; then
    python3 - "$stage/outcome.json.tmp" "$point_id" "$outcome" "$phase" "$exit_code" <<'PY'
import json
import pathlib
import sys

path, point_id, outcome, phase, exit_code = sys.argv[1:]
pathlib.Path(path).write_text(
    json.dumps(
        {
            "version": 1,
            "point_id": point_id,
            "outcome": outcome,
            "phase": phase,
            "exit_code": int(exit_code),
        },
        indent=2,
        sort_keys=True,
    )
    + "\n"
)
PY
        mv "$stage/outcome.json.tmp" "$stage/outcome.json"
    fi
    (
        cd "$stage"
        find . -type f \
            ! -name COMPLETE \
            ! -name files.sha256 \
            ! -name files.sha256.tmp \
            -print0 \
            | sort -z | xargs -0 sha256sum
    ) > "$stage/files.sha256.tmp"
    mv "$stage/files.sha256.tmp" "$stage/files.sha256"
    sha256sum "$stage/files.sha256" | awk '{print $1}' > "$stage/COMPLETE.tmp"
    mv "$stage/COMPLETE.tmp" "$stage/COMPLETE"
    mv "$stage" "$point_dir"
    rmdir "$claim_dir"
    trap - EXIT
}

verify_and_capture_build() {
    local profile="$1"
    local lineinfo="$2"
    local target_dir="$target_root/$profile"
    local profile_dir="$stage/$profile"
    local failure_state="$stage/failure-state.txt"
    mkdir -p "$profile_dir" "$target_dir"

    local -a build_environment=(
        env
        -u GPU_GKR_WINDOWED_BENCH_ENABLE_LINEINFO
        "CARGO_TARGET_DIR=$target_dir"
        "CUDAARCHS=native"
    )
    if [[ "$lineinfo" -eq 1 ]]; then
        build_environment+=("GPU_GKR_WINDOWED_BENCH_ENABLE_LINEINFO=1")
    fi
    if [[ "$min_blocks" -gt 0 ]]; then
        build_environment+=("$min_variable=$min_blocks")
    fi
    if [[ "$maxreg" -gt 0 ]]; then
        build_environment+=("$maxreg_variable=$maxreg")
    fi

    printf 'compiler_failure %s_compile\n' "$profile" > "$failure_state.tmp"
    mv "$failure_state.tmp" "$failure_state"
    set +e
    (
        cd "$REPO_ROOT"
        "${build_environment[@]}" "$CARGO_BIN" build \
            -p gpu_gkr_windowed_bench \
            --release --locked --features artifact-gen \
            --bin run_windowed_r0_corpus
    ) > "$profile_dir/build.log" 2>&1
    local build_status=$?
    set -e
    if [[ "$build_status" -ne 0 ]]; then
        return "$build_status"
    fi
    printf 'recording_failure %s_recording\n' "$profile" > "$failure_state.tmp"
    mv "$failure_state.tmp" "$failure_state"

    local executable="$target_dir/release/run_windowed_r0_corpus"
    [[ -f "$executable" ]] || {
        echo "missing built executable: $executable" >&2
        return 2
    }
    cp "$executable" "$profile_dir/run_windowed_r0_corpus"
    sha256sum "$profile_dir/run_windowed_r0_corpus" \
        | awk '{print $1}' > "$profile_dir/binary.sha256.tmp"
    mv "$profile_dir/binary.sha256.tmp" "$profile_dir/binary.sha256"

    local compile_commands
    compile_commands="$(find "$target_dir" -path '*/out/build/compile_commands.json' -type f \
        | sort | tail -1)"
    [[ -n "$compile_commands" ]] || {
        echo "missing compile_commands.json for $point_id/$profile" >&2
        return 2
    }
    local cmake_dir
    cmake_dir="$(dirname "$compile_commands")"
    cp "$compile_commands" "$profile_dir/compile-commands.json"
    [[ -f "$cmake_dir/CMakeCache.txt" ]] || {
        echo "missing CMakeCache.txt for $point_id/$profile" >&2
        return 2
    }
    cp "$cmake_dir/CMakeCache.txt" "$profile_dir/CMakeCache.txt"
    local device_link
    device_link="$(find "$cmake_dir" -type f \
        \( -name device_link.txt -o -name dlink.txt \) | sort | tail -1)"
    [[ -n "$device_link" ]] || {
        echo "missing literal device-link command for $point_id/$profile" >&2
        return 2
    }
    cp "$device_link" "$profile_dir/device-link-command.txt"

    python3 - \
        "$profile_dir/compile-commands.json" \
        "$profile_dir/target-compile-command.txt" \
        "$profile_dir/sibling-compile-commands.txt" \
        "$wrapper" "$min_variable" "$min_blocks" \
        "$maxreg_variable" "$maxreg" "$lineinfo" \
        "$profile_dir/device-link-command.txt" <<'PY'
import json
import pathlib
import shlex
import sys

(
    commands_path,
    target_path,
    sibling_path,
    wrapper,
    min_variable,
    min_blocks,
    maxreg_variable,
    maxreg,
    lineinfo,
    device_link_path,
) = sys.argv[1:]
commands = json.loads(pathlib.Path(commands_path).read_text())
wrappers = [row for row in commands if pathlib.Path(row["file"]).name.startswith("windowed_r0_cta")]
target = [row for row in wrappers if pathlib.Path(row["file"]).name == wrapper]
siblings = [row for row in wrappers if pathlib.Path(row["file"]).name != wrapper]
if len(target) != 1 or len(siblings) != 4:
    raise SystemExit("compile command geometry coverage mismatch")

def literal(row):
    command = row.get("command")
    if not isinstance(command, str) or not command:
        raise SystemExit("compile command is not literal text")
    return command

target_command = literal(target[0])
sibling_commands = [literal(row) for row in siblings]
target_tokens = shlex.split(target_command)
minimum_flag = f"-D{min_variable}={min_blocks}"
maxreg_flag = f"--maxrregcount={maxreg}"
expected_controls = []
if int(min_blocks) > 0:
    expected_controls.append(minimum_flag)
if int(maxreg) > 0:
    expected_controls.append(maxreg_flag)

def controls(command):
    return [
        token
        for token in shlex.split(command)
        if token.startswith("-DGPU_GKR_WINDOWED_R0_")
        or token.startswith("--maxrregcount")
    ]

if controls(target_command) != expected_controls:
    raise SystemExit(
        "target compile controls do not exactly match arguments: "
        f"expected {expected_controls!r}, found {controls(target_command)!r}"
    )
for command in sibling_commands:
    if controls(command):
        raise SystemExit("a sibling geometry is constrained")
if int(lineinfo) == 1 and "-lineinfo" not in target_tokens:
    raise SystemExit("lineinfo absent from profiling compile")
if int(lineinfo) == 0 and "-lineinfo" in target_tokens:
    raise SystemExit("lineinfo present in timing compile")
device_link = pathlib.Path(device_link_path).read_text()
if controls(device_link):
    raise SystemExit("per-TU control leaked into device link")
pathlib.Path(target_path).write_text(target_command + "\n")
pathlib.Path(sibling_path).write_text("\n".join(sibling_commands) + "\n")
PY

    local extraction_dir
    extraction_dir="$(mktemp -d "$profile_dir/.extract.XXXXXX")"
    (
        cd "$extraction_dir"
        cuobjdump --extract-elf all "$profile_dir/run_windowed_r0_corpus"
    ) > "$profile_dir/cubin-extraction.log" 2>&1
    local selected_cubin=""
    local candidate_cubin
    while IFS= read -r candidate_cubin; do
        if cuobjdump --dump-elf-symbols "$candidate_cubin" 2>/dev/null \
            | grep -Fq "$symbol"; then
            if [[ -n "$selected_cubin" ]]; then
                echo "target symbol occurs in multiple final linked cubins" >&2
                return 2
            fi
            selected_cubin="$candidate_cubin"
        fi
    done < <(find "$extraction_dir" -type f -name '*.cubin' | sort)
    [[ -n "$selected_cubin" ]] || {
        echo "target symbol absent from final linked cubin" >&2
        return 2
    }
    cp "$selected_cubin" "$profile_dir/final-linked.cubin"
    sha256sum "$profile_dir/final-linked.cubin" \
        | awk '{print $1}' > "$profile_dir/cubin.sha256.tmp"
    mv "$profile_dir/cubin.sha256.tmp" "$profile_dir/cubin.sha256"

    cuobjdump --dump-resource-usage "$profile_dir/final-linked.cubin" \
        > "$profile_dir/all-resources.txt"
    cuobjdump --dump-sass "$profile_dir/final-linked.cubin" \
        > "$profile_dir/all.sass"
    cuobjdump --dump-elf "$profile_dir/final-linked.cubin" \
        > "$profile_dir/elf.txt"
    cuobjdump --dump-elf-symbols "$profile_dir/final-linked.cubin" \
        > "$profile_dir/elf-symbols.txt"

    python3 - \
        "$profile_dir/all-resources.txt" "$profile_dir/resources.txt" \
        "$profile_dir/all.sass" "$profile_dir/kernel.sass" "$symbol" <<'PY'
import pathlib
import sys

resources_path, target_resources_path, sass_path, target_sass_path, symbol = sys.argv[1:]

def section(lines, marker, next_marker):
    matches = [index for index, line in enumerate(lines) if line.strip() == marker]
    if len(matches) != 1:
        raise SystemExit(f"expected one {marker!r} section, found {len(matches)}")
    start = matches[0]
    end = len(lines)
    for index in range(start + 1, len(lines)):
        if lines[index].strip().startswith(next_marker):
            end = index
            break
    return lines[start:end]

resource_lines = pathlib.Path(resources_path).read_text().splitlines()
sass_lines = pathlib.Path(sass_path).read_text().splitlines()
target_resources = section(resource_lines, f"Function {symbol}:", "Function ")
target_sass = section(sass_lines, f"Function : {symbol}", "Function : ")
pathlib.Path(target_resources_path).write_text("\n".join(target_resources) + "\n")
pathlib.Path(target_sass_path).write_text("\n".join(target_sass) + "\n")
PY
    sha256sum "$profile_dir/kernel.sass" \
        | awk '{print $1}' > "$profile_dir/sass.sha256.tmp"
    mv "$profile_dir/sass.sha256.tmp" "$profile_dir/sass.sha256"

    python3 - \
        "$profile_dir/resources.txt" "$profile_dir/binary.sha256" \
        "$profile_dir/cubin.sha256" "$profile_dir/sass.sha256" \
        "$profile_dir/resources.json" "$profile_dir/kernel.sass" <<'PY'
import json
import pathlib
import re
import sys

resources_path, binary_path, cubin_path, sass_path, output_path, kernel_sass_path = map(
    pathlib.Path, sys.argv[1:]
)
text = resources_path.read_text()
match = re.search(r"REG:(\d+)\s+STACK:(\d+)\s+SHARED:(\d+)\s+LOCAL:(\d+)", text)
if match is None:
    raise SystemExit("unable to parse target resources")
registers, stack_bytes, shared_bytes, local_bytes = map(int, match.groups())
sass = kernel_sass_path.read_text()
opcodes = {}
for opcode in ("LDC", "LDG", "LDL", "STL", "LDS", "STS", "CALL", "RET"):
    opcodes[opcode] = len(re.findall(rf"\b{opcode}(?:\.|\s)", sass))
value = {
    "registers": registers,
    "stack_bytes": stack_bytes,
    "local_bytes": local_bytes,
    "shared_bytes": shared_bytes,
    "binary_sha256": binary_path.read_text().strip(),
    "cubin_sha256": cubin_path.read_text().strip(),
    "sass_sha256": sass_path.read_text().strip(),
    "opcodes": opcodes,
}
output_path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
PY
    rm -f "$failure_state"
}

set +e
(
    set -e
    verify_and_capture_build timing 0
)
build_status=$?
set -e
if [[ "$build_status" -ne 0 ]]; then
    read -r failure_outcome failure_phase < "$stage/failure-state.txt"
    finalize_publish "$failure_outcome" "$failure_phase" "$build_status"
    echo "$failure_outcome preserved at $point_dir" >&2
    exit 2
fi
set +e
(
    set -e
    verify_and_capture_build lineinfo 1
)
build_status=$?
set -e
if [[ "$build_status" -ne 0 ]]; then
    read -r failure_outcome failure_phase < "$stage/failure-state.txt"
    finalize_publish "$failure_outcome" "$failure_phase" "$build_status"
    echo "$failure_outcome preserved at $point_dir" >&2
    exit 2
fi

python3 - "$stage/outcome.json.tmp" "$stage/timing/resources.json" "$point_id" <<'PY'
import json
import pathlib
import sys

output_path, resources_path, point_id = map(pathlib.Path, sys.argv[1:])
value = {
    "version": 1,
    "point_id": str(point_id),
    "outcome": "success",
    "classification_profile": "timing",
    "profiling_profile": "lineinfo",
    "resources": json.loads(resources_path.read_text()),
}
output_path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
PY
mv "$stage/outcome.json.tmp" "$stage/outcome.json"
finalize_publish success complete 0
echo "$point_dir"
