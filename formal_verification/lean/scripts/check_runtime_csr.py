#!/usr/bin/env python3
"""Run inside bounded_fv.py: scoped native reduced runtime CSR export controls."""
from pathlib import Path
import argparse, json, os, re, subprocess, tempfile
ROOT = Path(__file__).resolve().parent.parent
REPO = ROOT.parent.parent
MANIFEST = ROOT.parent / "native_setup_exporter/Cargo.toml"
TARGET = ROOT / ".lake/native-setup-target"
ARTIFACT = ROOT / "artifacts/setup/reduced-runtime-csr-native.json"
BASE = "67ee094449abaebc77e58435f130ce6ea27721e5"

def runtime_config():
    paths = ["common_constants/src/delegation_types/mod.rs",
             "common_constants/src/delegation_types/blake2s_with_control.rs",
             "common_constants/src/delegation_types/bigint_with_control.rs",
             "circuit_defs/unrolled_circuits/unified_reduced_machine/src/lib.rs"]
    sources = {}
    for path in paths:
        blob = subprocess.check_output(["git", "show", BASE + ":" + path], cwd=REPO)
        assert (REPO / path).read_bytes() == blob, path
        sources[path] = blob.decode()
    constants = sources[paths[0]]
    base = int(re.search(r"pub const NON_DETERMINISM_CSR: u32 = (0x[0-9a-f]+);", constants)[1], 16)
    blake = base + int(re.search(r"BLAKE2S_DELEGATION_CSR_REGISTER: u32 = super::NON_DETERMINISM_CSR \+ (\d+);", sources[paths[1]])[1])
    bigint = base + int(re.search(r"BIGINT_OPS_WITH_CONTROL_CSR_REGISTER: u32 = super::NON_DETERMINISM_CSR \+ (\d+);", sources[paths[2]])[1])
    runtime = sources[paths[3]]
    expected = ["common_constants::NON_DETERMINISM_CSR", "common_constants::BLAKE2S_DELEGATION_CSR_REGISTER"]
    for name, suffix in [("ALLOWED_DELEGATION_CSRS", ""), ("ALLOWED_DELEGATION_CSRS_U16", " as u16")]:
        body = re.search(r"pub const " + name + r": &\[u(?:32|16)\] = &\[(.*?)\];", runtime, re.S)[1]
        assert [p.strip() for p in body.split(",") if p.strip()] == [p + suffix for p in expected]
    assert (base, blake, bigint) == (1984, 1991, 1994)
    return [base, blake]

def decode(block):
    kind = block["kind"]
    if kind == "dense": return block["values"]
    if kind == "affine": return [block["first"] + block["step"] * i for i in range(block["length"])]
    if kind == "periodic": return [value + block["stride"] * rep for rep in range(block["repetitions"]) for value in block["values"]]
    raise AssertionError(kind)

def main():
    args = argparse.ArgumentParser()
    args.add_argument("--write", action="store_true")
    options = args.parse_args()
    os.environ["RAYON_NUM_THREADS"] = "1"
    csrs = runtime_config()
    cargo = ["--offline", "--locked", "--manifest-path", str(MANIFEST), "--target-dir", str(TARGET), "-j1", "-p", "airbender-v2-native-setup-exporter", "--bin", "airbender-v2-native-setup-exporter"]
    subprocess.run(["cargo", "check", *cargo], cwd=ROOT, check=True)
    subprocess.run(["cargo", "build", *cargo], cwd=ROOT, check=True)
    binary = TARGET / "debug/airbender-v2-native-setup-exporter"
    with tempfile.TemporaryDirectory(prefix="v2-runtime-csr-") as directory:
        temp = Path(directory)
        config, output = temp / "csrs.json", temp / "out.json"
        config.write_text(json.dumps(csrs))
        command = [str(binary), "--reduced-csr", str(ROOT / "artifacts/circuits/reduced-native-layout.json"), str(config), str(output)]
        subprocess.run(command, check=True)
        data = json.loads(output.read_bytes())
        assert data["delegation_csrs"] == csrs and data["allow_non_determinism"] is True
        assert data["profile"] == "reduced_machine_csr_properties" and data["field_modulus"] == 2147483647
        assert data["generic_rows"] == 4096 and len(data["tables"]) == 1
        table = data["tables"][0]
        assert (table["id"], table["offset"], table["data"]["length"]) == (25,1507585,4096)
        columns = [[v for b in c["blocks"] for v in decode(b)] for c in table["data"]["columns"]]
        expected = [[i, int(i in csrs), int(i == 1991), 25] for i in range(4096)]
        assert list(map(list, zip(*columns))) == expected
        if options.write: ARTIFACT.write_bytes(output.read_bytes())
        else: assert output.read_bytes() == ARTIFACT.read_bytes()
        first = output.read_bytes()
        subprocess.run(command, check=True)
        assert output.read_bytes() == first
        for bad in [[4096], [-1], "bad", {"csrs": csrs}]:
            config.write_text(json.dumps(bad)); output.unlink(missing_ok=True)
            result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            assert result.returncode != 0 and not output.exists(), bad
        config.write_text(json.dumps(csrs))
        layout = json.loads((ROOT / "artifacts/circuits/reduced-native-layout.json").read_text())
        for key in ["offset", "extent"]:
            forged = json.loads(json.dumps(layout))
            if key == "offset": forged["table_offsets"][25] += 1
            else: forged["total_tables_size"] -= 1
            bad_layout = temp / "layout.json"; bad_layout.write_text(json.dumps(forged)); output.unlink(missing_ok=True)
            result = subprocess.run([str(binary), "--reduced-csr", str(bad_layout), str(config), str(output)], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            assert result.returncode != 0 and not output.exists(), key
    print("PASS pinned runtime allow-list, every4096 native CSR rows, byte reproduction, repeat export and6 malformed CLI/layout controls", flush=True)

if __name__ == "__main__": main()
