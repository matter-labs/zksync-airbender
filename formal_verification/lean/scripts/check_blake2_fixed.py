#!/usr/bin/env python3
"""Under bounded_fv.py: only fresh native worker fixed tables, not main pools."""
from pathlib import Path
import json, os, subprocess, tempfile
from check_native_blake2 import native_sources, BASE, REPO
ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT.parent / "native_setup_exporter/Cargo.toml"
TARGET = ROOT / ".lake/native-setup-target"
ARTIFACT = ROOT / "artifacts/setup/blake2-fixed-native.json"
LAYOUT = ROOT / "artifacts/circuits/blake2-native-layout.json"


def decode(block):
    kind = block["kind"]
    if kind == "dense": return block["values"]
    if kind == "affine": return [block["first"] + block["step"] * i for i in range(block["length"])]
    if kind == "periodic": return [value + block["stride"] * rep for rep in range(block["repetitions"]) for value in block["values"]]
    raise AssertionError(kind)


def verify(data):
    assert data["version"] == 1 and data["field_modulus"] == 2147483647
    assert data["profile"] == "blake2_extended_control_fixed" and data["generic_rows"] == 344384
    geometry = [(4,0,65536,256),(26,65536,64,8),(27,65600,256,16),(28,65856,16384,128),(29,82240,262144,512)]
    assert len(data["tables"]) == len(geometry)
    for region, (tag, offset, length, base) in zip(data["tables"], geometry):
        assert (region["id"],region["offset"],region["data"]["length"]) == (tag,offset,length)
        assert len(region["data"]["columns"]) == 4
        columns = [[value for block in c["blocks"] for value in decode(block)] for c in region["data"]["columns"]]
        assert all(len(c) == length for c in columns)
        for i in range(length):
            assert [c[i] for c in columns] == [i//base, i%base, (i//base) ^ (i%base), tag]
    original = json.loads((ROOT / "artifacts/setup/reduced-fixed-native.json").read_bytes())
    assert data["tables"][0]["data"] == next(region for region in original["tables"] if region["id"] == 4)["data"]


def main():
    os.environ["RAYON_NUM_THREADS"] = "1"
    native_sources()
    for path in ["cs/src/tables/binops.rs", "cs/src/tables/mod.rs"]:
        assert (REPO / path).read_bytes() == subprocess.check_output(["git", "show", BASE + ":" + path], cwd=REPO), path
    cargo = ["--offline", "--locked", "--manifest-path", str(MANIFEST), "--target-dir", str(TARGET), "-j1", "-p", "airbender-v2-native-setup-exporter", "--bin", "airbender-v2-native-setup-exporter"]
    subprocess.run(["cargo", "check", *cargo], cwd=ROOT, check=True)
    subprocess.run(["cargo", "build", *cargo], cwd=ROOT, check=True)
    binary = TARGET / "debug/airbender-v2-native-setup-exporter"
    with tempfile.TemporaryDirectory(prefix="v2-blake2-fixed-") as directory:
        temp = Path(directory); output = temp / "out.json"
        for _ in range(2):
            subprocess.run([str(binary), "--blake2-fixed", str(LAYOUT), str(output)], check=True)
            assert output.read_bytes() == ARTIFACT.read_bytes()
            verify(json.loads(output.read_bytes()))
        output.unlink()
        for kind in ["trace", "extent", "offset"]:
            forged = json.loads(LAYOUT.read_bytes())
            if kind == "trace": forged["trace_len"] -= 1
            elif kind == "extent": forged["total_tables_size"] -= 1
            else: forged["table_offsets"][29] += 1
            path = temp / "bad-layout.json"; path.write_text(json.dumps(forged))
            result = subprocess.run([str(binary), "--blake2-fixed", str(path), str(output)], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            assert result.returncode != 0 and not output.exists(), kind
        for args in [["--blake2-fixed"], ["--blake2-fixed", str(LAYOUT)]]:
            result = subprocess.run([str(binary), *args], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            assert result.returncode != 0 and not output.exists()
    print("PASS native worker five regions/every344384 rows,byte columns,repeat bytes,unchanged prior exporter and5 bad CLI/layout controls", flush=True)

if __name__ == "__main__": main()
