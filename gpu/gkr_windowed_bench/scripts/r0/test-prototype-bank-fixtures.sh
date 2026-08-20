#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/../../../.." && pwd)
controller="$repo_root/gpu/gkr_windowed_bench/scripts/r0/run-prototype-bank.py"
auditor="$repo_root/gpu/gkr_windowed_bench/scripts/r0/audit-prototype-bank.py"
sanitizer_deriver="$repo_root/gpu/gkr_windowed_bench/scripts/r0/derive-prototype-sanitizer.py"
sanitizer_runner="$repo_root/gpu/gkr_windowed_bench/scripts/r0/run-prototype-sanitizer.py"
screen_deriver="$repo_root/gpu/gkr_windowed_bench/scripts/r0/derive-prototype-screen.py"
report_fixture="$repo_root/gpu/gkr_windowed_bench/scripts/r0/test-prototype-report.py"
sectioned_static="$repo_root/gpu/gkr_windowed_bench/scripts/r0/audit-sectioned-launch-bounds.py"
fixture_root=$(mktemp -d)
trap 'rm -rf "$fixture_root"' EXIT

if rg -F 'env!("CARGO_MANIFEST_DIR")' \
  "$repo_root/gpu/gkr_windowed_bench/src/bin/run_windowed_r0_prototype_bank.rs"; then
  echo "prototype runner contains a compile-time worktree root" >&2
  exit 1
fi

cat >"$fixture_root/corpus.json" <<'JSON'
{"coordinates":[
  {"circuit":"alpha","layer":0},
  {"circuit":"beta","layer":1}
]}
JSON
printf 'fixture corpus bytes' >"$fixture_root/corpus.bin"
cat >"$fixture_root/prototypes.json" <<'JSON'
{"configurations":[
  {"configuration_id":"cfg/a","candidate_id":"candidate/a","tile_capacity":null},
  {"configuration_id":"cfg/b","candidate_id":"candidate/b","tile_capacity":8},
  {"configuration_id":"cfg/c","candidate_id":"candidate/c","tile_capacity":16}
]}
JSON
cat >"$fixture_root/screen-runtime.json" <<'JSON'
{"version":1,"rows":[{"circuit":"alpha","layer":0,"log_trace":24,"requested_bytes":4096,"reasons":["fixture"]}]}
JSON
printf 'fixture-gpu' >"$fixture_root/device-name.txt"
export R0_PROTOTYPE_FIXTURE_DEVICE_NAME="$fixture_root/device-name.txt"

cat >"$fixture_root/fake-runner.py" <<'PY'
#!/usr/bin/env python3
import argparse, hashlib, json, os, pathlib
p=argparse.ArgumentParser()
p.add_argument("--mode")
p.add_argument("--repo-root")
p.add_argument("--corpus")
p.add_argument("--artifact-root")
p.add_argument("--output-root")
p.add_argument("--candidate")
p.add_argument("--coordinate")
p.add_argument("--log", type=int)
p.add_argument("--seed", type=int)
a=p.parse_args()
device_name=pathlib.Path(os.environ["R0_PROTOTYPE_FIXTURE_DEVICE_NAME"]).read_text().strip()
device={"cuda_device_index":0,"uuid":"GPU-fixture","name":device_name,
    "compute_capability_major":10,"compute_capability_minor":0,
    "cuda_driver_version":12090,"cuda_runtime_version":12080,
    "cuda_toolkit_version":"12.8","default_shared_memory_bytes":49152,
    "opt_in_shared_memory_bytes":232448,
    "clock_policy":{"raw_query":"fixture clock row\n","uuid":"GPU-fixture",
        "name":device_name,"compute_capability":"10.0","driver_version":"fixture-driver",
        "performance_state":"P0","persistence_mode":"Enabled",
        "current_graphics_clock":"1 MHz","current_memory_clock":"2 MHz",
        "max_graphics_clock":"3 MHz","max_memory_clock":"4 MHz",
        "application_graphics_clock":"5 MHz","application_memory_clock":"6 MHz",
        "clock_event_reasons_active":"None"}}
if a.mode == "device-info":
    print(json.dumps(device,sort_keys=True))
    raise SystemExit(0)
circuit, layer = a.coordinate.rsplit(":", 1)
configs=a.candidate.split(",")
for position, config in enumerate(configs):
    cells=[{"limbs":[i, i+1, i+2, i+3]} for i in range(27)]
    payload=b"".join(int(limb).to_bytes(4,"little") for cell in cells for limb in cell["limbs"])
    checksum=hashlib.sha256(payload).hexdigest()
    observation={"version":2,"configuration_id":config,
        "candidate_id":"candidate/"+config[-1],"circuit":circuit,
        "layer":int(layer),"log_trace":a.log,"seed":a.seed,
        "input_sha256":"1"*64,"program_sha256":"2"*64,
        "tile_sha256":None,"descriptor_bytes":100,
        "launchability":{"launchable":{"dynamic_shared_bytes":0,"opt_in":False}},
        "launch":{"geometry":"cta288_pair","symbol":"fake","grid":[1,1,1],"block":[288,1,1]},
        "cells":cells,"checksum":checksum,"expected_checksum":checksum,
        "passing":True,"failure":None,"device_identity":device}
    if a.mode == "screen":
        if config.endswith("c"):
            observation.update({"launchability":{"unlaunchable_capacity":{
                "required_bytes":232449,"device_limit_bytes":232448}},
                "launch":None,"cells":None,"checksum":None,"passing":False,
                "failure":"unlaunchable_capacity"})
            print(json.dumps({"observation":observation,"pilot_median_ms":None,
                "retained_samples":0,"pilot_correctness_checksum":None,
                "pilot_post_session_checksum":None,"retained_correctness_checksum":None,
                "retained_post_session_checksum":None,"pilot_samples":[],"samples":[],
                "candidate_wall_seconds":0.0,"coordinate_cpu_setup_seconds":1.0,
                "coordinate_harness_setup_seconds":2.0,"reference_wall_seconds":0.25,
                "coordinate_execution_wall_seconds":5.0},sort_keys=True))
            continue
        pilot=[{"version":2,"configuration_id":config,"circuit":circuit,"layer":int(layer),
            "log_trace":a.log,"seed":a.seed,"phase":"pilot","pass_index":0,
            "pass_position":position,"warmup":index<2,
            "sample_index":index if index<2 else index-2,"milliseconds":1.0+index}
            for index in range(5)]
        retained_position=(position-1)%len(configs)
        retained=[{"version":2,"configuration_id":config,"circuit":circuit,"layer":int(layer),
            "log_trace":a.log,"seed":a.seed,"phase":"retained","pass_index":1,
            "pass_position":retained_position,"warmup":index<2,
            "sample_index":index if index<2 else index-2,"milliseconds":2.0+index}
            for index in range(27)]
        print(json.dumps({"observation":observation,"pilot_median_ms":4.0,
            "retained_samples":25,"pilot_correctness_checksum":checksum,
            "pilot_post_session_checksum":checksum,"retained_correctness_checksum":checksum,
            "retained_post_session_checksum":checksum,"pilot_samples":pilot,"samples":retained,
            "candidate_wall_seconds":0.5,"coordinate_cpu_setup_seconds":1.0,
            "coordinate_harness_setup_seconds":2.0,"reference_wall_seconds":0.25,
            "coordinate_execution_wall_seconds":5.0},sort_keys=True))
    else:
        print(json.dumps(observation,sort_keys=True))
PY
chmod +x "$fixture_root/fake-runner.py"

cat >"$fixture_root/fake-lock.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
echo '[with_gpu_lock] waiting for GPU lock: /tmp/fixture.lock (owner=fixture pid=1)' >&2
echo '[with_gpu_lock] acquired GPU lock: /tmp/fixture.lock (owner=fixture pid=1)' >&2
set +e
"$@"
rc=$?
set -e
echo "[with_gpu_lock] releasing GPU lock: /tmp/fixture.lock (owner=fixture pid=1 status=$rc)" >&2
exit "$rc"
SH
chmod +x "$fixture_root/fake-lock.sh"

python3 "$controller" correctness \
  --runner "$fixture_root/fake-runner.py" \
  --corpus "$fixture_root/corpus.bin" \
  --corpus-manifest "$fixture_root/corpus.json" \
  --prototype-manifest "$fixture_root/prototypes.json" \
  --artifact-root "$fixture_root" --output-root "$fixture_root/out" \
  --gpu-lock "$fixture_root/fake-lock.sh" --logs 3,12 >"$fixture_root/first.txt"

test "$(find "$fixture_root/out" -name rows.jsonl | wc -l)" -eq 4
test "$(find "$fixture_root/out" -name checkpoint.json | wc -l)" -eq 4
test "$(cat "$fixture_root/calls.txt" 2>/dev/null || true)" = ""
python3 - "$fixture_root/out" <<'PY'
import json, pathlib, sys
for bindings in pathlib.Path(sys.argv[1]).glob("**/bindings.json"):
    binding=json.loads(bindings.read_text())
    expected=binding["configuration_ids"]
    assert binding["corpus"].endswith("/corpus.bin")
    assert len(binding["corpus_sha256"]) == 64
    assert binding["device_identity"]["name"] == "fixture-gpu"
    assert binding["execution"]["gpu_lock"]["mode"] == "repository_file_lock"
    assert len(binding["execution"]["gpu_lock"]["sha256"]) == 64
    assert binding["execution"]["command"][0].endswith("fake-lock.sh")
    observed=[json.loads(line)["configuration_id"] for line in (bindings.parent/"rows.jsonl").read_text().splitlines()]
    assert observed == expected, (bindings, observed, expected)
    checkpoint=json.loads((bindings.parent/"checkpoint.json").read_text())
    assert len(checkpoint["driver_sha256"]) == 64
PY

before=$(find "$fixture_root/out" -type f -exec sha256sum {} + | sort | sha256sum)
python3 "$controller" correctness \
  --runner "$fixture_root/fake-runner.py" \
  --corpus "$fixture_root/corpus.bin" \
  --corpus-manifest "$fixture_root/corpus.json" \
  --prototype-manifest "$fixture_root/prototypes.json" \
  --artifact-root "$fixture_root" --output-root "$fixture_root/out" \
  --gpu-lock "$fixture_root/fake-lock.sh" --logs 3,12 >"$fixture_root/reuse.txt"
after=$(find "$fixture_root/out" -type f -exec sha256sum {} + | sort | sha256sum)
test "$before" = "$after"
grep -q 'reused=4' "$fixture_root/reuse.txt"

driver_file=$(find "$fixture_root/out" -name driver.log | sort | head -1)
cp "$driver_file" "$fixture_root/driver.clean"
printf 'tamper\n' >>"$driver_file"
if python3 "$controller" correctness \
  --runner "$fixture_root/fake-runner.py" \
  --corpus "$fixture_root/corpus.bin" \
  --corpus-manifest "$fixture_root/corpus.json" \
  --prototype-manifest "$fixture_root/prototypes.json" \
  --artifact-root "$fixture_root" --output-root "$fixture_root/out" \
  --gpu-lock "$fixture_root/fake-lock.sh" --logs 3,12 >/dev/null 2>&1; then
  echo "tampered driver log unexpectedly reused complete evidence" >&2
  exit 1
fi
cp "$fixture_root/driver.clean" "$driver_file"

printf 'drifted-gpu' >"$fixture_root/device-name.txt"
if python3 "$controller" correctness \
  --runner "$fixture_root/fake-runner.py" \
  --corpus "$fixture_root/corpus.bin" \
  --corpus-manifest "$fixture_root/corpus.json" \
  --prototype-manifest "$fixture_root/prototypes.json" \
  --artifact-root "$fixture_root" --output-root "$fixture_root/out" \
  --gpu-lock "$fixture_root/fake-lock.sh" --logs 3,12 >/dev/null 2>&1; then
  echo "current device drift unexpectedly reused complete evidence" >&2
  exit 1
fi
printf 'fixture-gpu' >"$fixture_root/device-name.txt"

python3 "$auditor" correctness \
  --corpus-manifest "$fixture_root/corpus.json" \
  --prototype-manifest "$fixture_root/prototypes.json" \
  --output-root "$fixture_root/out" --logs 3,12 \
  >"$fixture_root/audit.txt"
grep -q WINDOWED_R0_PROTOTYPE_CORRECTNESS_OK "$fixture_root/audit.txt"

python3 "$controller" screen \
  --runner "$fixture_root/fake-runner.py" --corpus "$fixture_root/corpus.bin" \
  --prototype-manifest "$fixture_root/prototypes.json" --artifact-root "$fixture_root" \
  --screen "$fixture_root/screen-runtime.json" --output-root "$fixture_root/screen-out" \
  --gpu-lock none >"$fixture_root/screen-run.txt"
python3 - "$fixture_root/screen-out/alpha--0" <<'PY'
import json, pathlib, sys
root=pathlib.Path(sys.argv[1])
rows=[json.loads(line) for line in (root/"rows.jsonl").read_text().splitlines()]
assert len(rows)==3
launchable=[row for row in rows if row["pilot_samples"]]
assert sorted(row["pilot_samples"][0]["pass_position"] for row in launchable)==[0,1]
assert sorted(row["samples"][0]["pass_position"] for row in launchable)==[0,2]
assert [row["pilot_samples"][0]["pass_position"] for row in launchable] != [row["samples"][0]["pass_position"] for row in launchable]
checkpoint=json.loads((root/"checkpoint.json").read_text())
assert checkpoint["controller_command_wall_seconds"] > 0
assert checkpoint["runner_coordinate_work_seconds"] == rows[0]["coordinate_execution_wall_seconds"]
assert checkpoint["device_identity"]["uuid"] == "GPU-fixture"
binding=json.loads((root/"bindings.json").read_text())
assert binding["execution"]["gpu_lock"] == {"mode":"none","path":None,"sha256":None}
assert len(checkpoint["driver_sha256"]) == 64
PY

screen_dir="$fixture_root/screen-out/alpha--0"
cp "$screen_dir/rows.jsonl" "$fixture_root/screen-rows.clean"
cp "$screen_dir/checkpoint.json" "$fixture_root/screen-checkpoint.clean"
for mutation in device warmup sample_index pass_position pilot_median same_order wall capacity; do
  cp "$fixture_root/screen-rows.clean" "$screen_dir/rows.jsonl"
  cp "$fixture_root/screen-checkpoint.clean" "$screen_dir/checkpoint.json"
  python3 - "$screen_dir" "$mutation" <<'PY'
import hashlib, json, pathlib, sys
root=pathlib.Path(sys.argv[1]); mutation=sys.argv[2]
rows=[json.loads(line) for line in (root/"rows.jsonl").read_text().splitlines()]
if mutation == "device":
    rows[0]["observation"]["device_identity"]["name"]="drifted-gpu"
    rows[0]["observation"]["device_identity"]["clock_policy"]["name"]="drifted-gpu"
elif mutation == "warmup":
    rows[0]["pilot_samples"][0]["warmup"]=1
elif mutation == "sample_index":
    rows[0]["pilot_samples"][2]["sample_index"]=7
elif mutation == "pass_position":
    for sample in rows[0]["pilot_samples"]: sample["pass_position"]=99
elif mutation == "pilot_median":
    rows[0]["pilot_median_ms"]=999.0
elif mutation == "same_order":
    for row in rows:
        if not row["pilot_samples"]: continue
        position=row["pilot_samples"][0]["pass_position"]
        for sample in row["samples"]: sample["pass_position"]=position
elif mutation == "wall":
    for row in rows: row["coordinate_cpu_setup_seconds"]=0
elif mutation == "capacity":
    rows[0]["observation"]["launchability"]["launchable"]["dynamic_shared_bytes"]=50000
payload="".join(json.dumps(row,sort_keys=True,separators=(",",":"))+"\n" for row in rows)
(root/"rows.jsonl").write_text(payload)
checkpoint=json.loads((root/"checkpoint.json").read_text())
checkpoint["rows_sha256"]=hashlib.sha256(payload.encode()).hexdigest()
(root/"checkpoint.json").write_text(json.dumps(checkpoint,sort_keys=True,separators=(",",":"))+"\n")
PY
  if python3 "$controller" screen \
    --runner "$fixture_root/fake-runner.py" --corpus "$fixture_root/corpus.bin" \
    --prototype-manifest "$fixture_root/prototypes.json" --artifact-root "$fixture_root" \
    --screen "$fixture_root/screen-runtime.json" --output-root "$fixture_root/screen-out" \
    --gpu-lock none >/dev/null 2>&1; then
    echo "screen mutation unexpectedly reusable: $mutation" >&2
    exit 1
  fi
done
cp "$fixture_root/screen-rows.clean" "$screen_dir/rows.jsonl"
cp "$fixture_root/screen-checkpoint.clean" "$screen_dir/checkpoint.json"

python3 "$sanitizer_deriver" --manifest "$repo_root/gpu/gkr_windowed_bench/artifacts/windowed_r0_prototype_manifest_v1.json" \
  --output "$fixture_root/sanitizer-cover.json"
python3 - "$fixture_root/sanitizer-cover.json" <<'PY'
import json, sys
value=json.load(open(sys.argv[1]))
assert value["universe"] == value["covered"]
assert all(set(row["tools"]) == ({"memcheck","racecheck"} if row["source_policy"] == "materialized" else {"memcheck"}) for row in value["rows"])
assert sum(row["prior_failure"] for row in value["rows"]) == 2
PY
python3 "$sanitizer_runner" --runner "$fixture_root/fake-runner.py" \
  --artifact-root "$fixture_root" --cover "$fixture_root/sanitizer-cover.json" \
  --output-root "$fixture_root/sanitizer" --gpu-lock "$repo_root/.agents/bin/with_gpu_lock.sh" \
  --dry-run >"$fixture_root/sanitizer-dry.json"
python3 - "$fixture_root/sanitizer-dry.json" <<'PY'
import json, sys
value=json.load(open(sys.argv[1]))
assert value["sessions"] == sum(len(row["tools"]) for row in json.load(open(sys.argv[1].replace("sanitizer-dry.json","sanitizer-cover.json")))["rows"])
assert all("compute-sanitizer" in command for command in value["commands"])
PY

cat >"$fixture_root/compute-sanitizer" <<'PY'
#!/usr/bin/env python3
import pathlib, subprocess, sys
args=sys.argv[1:]
tool=args[args.index("--tool")+1]
log=pathlib.Path(args[args.index("--log-file")+1])
log.parent.mkdir(parents=True,exist_ok=True)
log.write_text("ERROR SUMMARY: 0 errors\n" if tool == "memcheck" else
    "RACECHECK SUMMARY: 0 hazards displayed (0 errors, 0 warnings)\n")
start=next(index for index,value in enumerate(args) if value.endswith("fake-runner.py"))
raise SystemExit(subprocess.run(args[start:]).returncode)
PY
chmod +x "$fixture_root/compute-sanitizer"
PATH="$fixture_root:$PATH" python3 "$sanitizer_runner" \
  --runner "$fixture_root/fake-runner.py" --corpus "$fixture_root/corpus.bin" \
  --artifact-root "$fixture_root" --cover "$fixture_root/sanitizer-cover.json" \
  --output-root "$fixture_root/sanitizer-live" --gpu-lock "$fixture_root/fake-lock.sh" \
  >"$fixture_root/sanitizer-live.txt"
python3 "$auditor" sanitizer --cover "$fixture_root/sanitizer-cover.json" \
  --output-root "$fixture_root/sanitizer-live" >"$fixture_root/sanitizer-audit.txt"
grep -q WINDOWED_R0_PROTOTYPE_SANITIZER_OK "$fixture_root/sanitizer-audit.txt"

python3 "$screen_deriver" --output "$fixture_root/screen.json" >"$fixture_root/screen.txt"
python3 "$report_fixture"
python3 "$sectioned_static" --self-test
python3 - "$fixture_root/screen.json" <<'PY'
import json, sys
value=json.load(open(sys.argv[1]))
assert value["version"] == 1 and len(value["rows"]) >= 12
assert value["rows"] == sorted(value["rows"], key=lambda row:(row["circuit"],row["layer"]))
assert all(row["reasons"] for row in value["rows"])
assert not ({"winner","selected","rejected","score"} & set().union(*(row.keys() for row in value["rows"])))
PY

python3 - "$fixture_root/out" <<'PY'
import json, pathlib, sys
row=next(pathlib.Path(sys.argv[1]).glob("**/rows.jsonl"))
lines=row.read_text().splitlines()
value=json.loads(lines[0]); value["cells"][0]["limbs"][0] += 1
lines[0]=json.dumps(value,sort_keys=True,separators=(",",":"))
row.write_text("\n".join(lines)+"\n")
PY
if python3 "$auditor" correctness \
  --corpus-manifest "$fixture_root/corpus.json" \
  --prototype-manifest "$fixture_root/prototypes.json" \
  --output-root "$fixture_root/out" --logs 3,12 >/dev/null 2>&1; then
  echo "tampered rows unexpectedly passed" >&2
  exit 1
fi

python3 - "$repo_root/gpu/gkr_windowed_bench/artifacts/windowed_r0_sectioned_manifest_v2.json" <<'PY'
import copy, hashlib, json, pathlib, struct, sys

manifest_path=pathlib.Path(sys.argv[1])
manifest_bytes=manifest_path.read_bytes()
manifest=json.loads(manifest_bytes)
manifest_sha=hashlib.sha256(manifest_bytes).hexdigest()
symbols={row["candidate_id"]:row for row in manifest["symbols"]}
shapes=manifest["specialized_shapes"]
cells=[{"limbs":[index,index+1,index+2,index+3]} for index in range(27)]
payload=b"".join(struct.pack("<I",limb) for cell in cells for limb in cell["limbs"])
checksum=hashlib.sha256(payload).hexdigest()

def coordinates(count):
    return [(f"fixture_{index}",index,shapes[index%len(shapes)]) for index in range(count)]

def make_rows(coords,policy):
    result=[]
    for circuit,layer,shape in coords:
        compiled=None if policy=="universal" else shape
        selected=[row for row in manifest["symbols"] if row["shape_bits"]==compiled]
        assert len(selected)==15
        for log_trace in (3,12):
            for symbol in selected:
                result.append({"version":2,"candidate_id":symbol["candidate_id"],
                    "symbol":symbol["symbol"],"geometry":symbol["geometry"],
                    "lowered_shape_bits":shape,"compiled_shape_bits":compiled,
                    "shape_policy":policy,"min_blocks":symbol.get("min_blocks"),
                    "manifest_sha256":manifest_sha,"executable_sha256":"e"*64,
                    "circuit":circuit,"layer":layer,"log_trace":log_trace,"seed":0,
                    "input_sha256":"i"*64,"expected_checksum":checksum,
                    "checksum":checksum,"cells":cells,"passing":True,"failure":None})
    return result

def validate(rows,coords,policy):
    expected={}
    for circuit,layer,shape in coords:
        compiled=None if policy=="universal" else shape
        ids={row["candidate_id"] for row in manifest["symbols"] if row["shape_bits"]==compiled}
        assert len(ids)==15
        for log_trace in (3,12):
            expected[(circuit,layer,log_trace)]=ids
    observed={key:set() for key in expected}
    seen=set()
    for row in rows:
        key=(row["circuit"],row["layer"],row["log_trace"])
        full=key+(row["candidate_id"],)
        assert key in expected and full not in seen
        seen.add(full); observed[key].add(row["candidate_id"])
        symbol=symbols[row["candidate_id"]]
        assert row["version"]==2 and row["shape_policy"]==policy
        assert row["symbol"]==symbol["symbol"] and row["geometry"]==symbol["geometry"]
        assert row["min_blocks"]==symbol.get("min_blocks")
        assert row["compiled_shape_bits"]==symbol["shape_bits"]
        assert row["manifest_sha256"]==manifest_sha
        assert row["executable_sha256"]=="e"*64 and row["input_sha256"]=="i"*64
        assert row["passing"] is True and row["failure"] is None
        assert len(row["cells"])==27 and all(len(cell["limbs"])==4 for cell in row["cells"])
        actual=b"".join(struct.pack("<I",limb) for cell in row["cells"] for limb in cell["limbs"])
        actual_sha=hashlib.sha256(actual).hexdigest()
        assert row["checksum"]==actual_sha==row["expected_checksum"]
    assert observed==expected

exact_coords=coordinates(57); universal_coords=coordinates(1)
exact=make_rows(exact_coords,"exact"); universal=make_rows(universal_coords,"universal")
assert len(exact)==1710 and len(universal)==30
validate(exact,exact_coords,"exact"); validate(universal,universal_coords,"universal")

mutations=[]
for field,value in [("min_blocks",99),("symbol","wrong"),
                    ("executable_sha256","x"*64),("input_sha256","x"*64),
                    ("shape_policy","universal")]:
    changed=copy.deepcopy(exact); changed[0][field]=value; mutations.append(changed)
changed=copy.deepcopy(exact); changed[0]["cells"][0]["limbs"][0]+=1; mutations.append(changed)
mutations.append(copy.deepcopy(exact[:-1]))
changed=copy.deepcopy(exact); changed[-1]=copy.deepcopy(changed[0]); mutations.append(changed)
for changed in mutations:
    try: validate(changed,exact_coords,"exact")
    except AssertionError: pass
    else: raise AssertionError("sectioned correctness mutation unexpectedly passed")
print("R0_SECTIONED_CORRECTNESS_FIXTURE_OK")
PY

echo TASK7_TASK8_PROTOTYPE_FIXTURES_OK
