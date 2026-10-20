#!/usr/bin/env python3
"""Run inside bounded_fv.py: native exporter reproducibility and input checks."""
from pathlib import Path
import os
import json
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT.parent / "native_setup_exporter/Cargo.toml"
TARGET = ROOT / ".lake/native-setup-target"
CARGO = ["cargo"]
OPTIONS = ["--offline", "--locked", "--manifest-path", str(MANIFEST),
           "--target-dir", str(TARGET), "-j1"]

def main():
    os.environ["RAYON_NUM_THREADS"] = "1"
    native_source = (ROOT.parent.parent / "prover/src/prover_stages/mod.rs").read_text()
    exporter_source = (MANIFEST.parent / "src/main.rs").read_text()
    def timestamp_clause(source):
        start = source.index("let timestamp_range_check_table: Vec<_>")
        end = source.index(".collect();", start) + len(".collect();")
        return "\n".join(line.strip() for line in source[start:end].splitlines())
    assert timestamp_clause(native_source) == timestamp_clause(exporter_source)
    print("PASS unchanged pinned native timestamp generation clause", flush=True)
    subprocess.run([*CARGO, "check", *OPTIONS], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix="airbender-v2-native-") as directory:
        temp = Path(directory)
        output = temp / "setup.json"
        subprocess.run([*CARGO, "run", *OPTIONS, "--", "--fixture", str(output)], cwd=ROOT, check=True)
        assert output.read_bytes() == (ROOT / "artifacts/setup/word-memory-native.json").read_bytes()
        print("PASS reproducible native setup export", flush=True)
        binary = TARGET / "debug/airbender-v2-native-setup-exporter"
        subword_layout = ROOT / "../../cs/subword_only_load_store_preprocessed_layout.json"
        subprocess.run([str(binary), "--subword-offset", str(subword_layout), str(output)], check=True)
        assert output.read_bytes() == (ROOT / "artifacts/setup/subword-offset-native.json").read_bytes()
        subword = json.loads(output.read_bytes())
        region, = subword["tables"]
        assert (region["id"], region["offset"], region["data"]["length"]) == (44,65537,2097152)
        assert json.loads(subword_layout.read_bytes())["table_offsets"][region["id"]] == region["offset"]
        print("PASS reproducible actual native subword offset/trap region and compiled placement", flush=True)
        subprocess.run([str(binary), "--subword-load", str(subword_layout), str(output)], check=True)
        assert output.read_bytes() == (ROOT / "artifacts/setup/subword-load-native.json").read_bytes()
        load = json.loads(output.read_bytes())
        region, = load["tables"]
        assert (region["id"], region["offset"], region["data"]["length"]) == (45,2162689,2097152)
        assert json.loads(subword_layout.read_bytes())["table_offsets"][region["id"]] == region["offset"]
        print("PASS reproducible actual native subword load-data region and compiled placement", flush=True)
        subprocess.run([str(binary), "--subword-store-clear", str(subword_layout), str(output)], check=True)
        assert output.read_bytes() == (ROOT / "artifacts/setup/subword-store-clear-native.json").read_bytes()
        load = json.loads(output.read_bytes())
        region, = load["tables"]
        assert (region["id"], region["offset"], region["data"]["length"]) == (54,5308417,2097152)
        assert json.loads(subword_layout.read_bytes())["table_offsets"][region["id"]] == region["offset"]
        print("PASS reproducible actual native subword store-clear region and compiled placement", flush=True)
        subprocess.run([str(binary), "--control", str(output)], check=True)
        assert output.read_bytes() == (ROOT / "artifacts/setup/jump-control-native.json").read_bytes()
        print("PASS reproducible native jump/branch/SLT fixed tables", flush=True)
        subprocess.run([str(binary), "--binary-prefix", str(output)], check=True)
        assert output.read_bytes() == (ROOT / "artifacts/setup/shift-binary-native.json").read_bytes()
        layout = json.loads((ROOT / "../../cs/shift_binop_csrrw_preprocessed_layout.json").read_bytes())
        prefix = json.loads(output.read_bytes())
        assert [(r["id"], r["offset"]) for r in prefix["tables"]] == [(0,0),(4,1),(6,65537),(7,131073)]
        assert all(layout["table_offsets"][r["id"]] == r["offset"] for r in prefix["tables"])
        print("PASS reproducible actual native zero/XOR/OR/AND prefix and compiled offsets", flush=True)
        compiled = ROOT / "../../cs/shift_binop_csrrw_preprocessed_layout.json"
        subprocess.run([str(binary), "--shift-scalars", str(compiled), str(output)], check=True)
        assert output.read_bytes() == (ROOT / "artifacts/setup/shift-scalars-native.json").read_bytes()
        regions = json.loads(output.read_bytes())
        assert regions["generic_rows"] == sum(r["data"]["length"] for r in regions["tables"])
        assert [(r["id"], r["offset"], r["data"]["length"]) for r in regions["tables"]] == [
            (47,200705,65536),(52,8654849,2097152),(53,10752001,65536)]
        assert all(layout["table_offsets"][r["id"]] == r["offset"] for r in regions["tables"])
        print("PASS reproducible actual native truncation/sign-fill/padded-range regions and compiled offsets", flush=True)
        subprocess.run([str(binary), "--srl-low", str(compiled), str(output)], check=True)
        assert output.read_bytes() == (ROOT / "artifacts/setup/shift-srl-low-native.json").read_bytes()
        srl = json.loads(output.read_bytes())
        assert srl["generic_rows"] == 2097152 and len(srl["tables"]) == 1
        region = srl["tables"][0]
        assert (region["id"],region["offset"],region["data"]["length"]) == (50,4460545,2097152)
        assert layout["table_offsets"][region["id"]] == region["offset"]
        print("PASS reproducible actual native SRL-low table and compiled offset", flush=True)
        subprocess.run([str(binary), "--sll-high", str(compiled), str(output)], check=True)
        assert output.read_bytes() == (ROOT / "artifacts/setup/shift-sll-high-native.json").read_bytes()
        sll = json.loads(output.read_bytes())
        assert sll["generic_rows"] == 2097152 and len(sll["tables"]) == 1
        region = sll["tables"][0]
        assert (region["id"],region["offset"],region["data"]["length"]) == (49,2363393,2097152)
        assert layout["table_offsets"][region["id"]] == region["offset"]
        print("PASS reproducible actual native SLL-high table and compiled offset", flush=True)
        subprocess.run([str(binary), "--sll-low", str(compiled), str(output)], check=True)
        assert output.read_bytes() == (ROOT / "artifacts/setup/shift-sll-low-native.json").read_bytes()
        sll = json.loads(output.read_bytes())
        assert sll["generic_rows"] == 2097152 and len(sll["tables"]) == 1
        region = sll["tables"][0]
        assert (region["id"],region["offset"],region["data"]["length"]) == (48,266241,2097152)
        assert layout["table_offsets"][region["id"]] == region["offset"]
        print("PASS reproducible actual native SLL-low table and compiled offset", flush=True)
        subprocess.run([str(binary), "--shift-csr-properties", str(compiled), str(output)], check=True)
        assert output.read_bytes() == (ROOT / "artifacts/setup/shift-csr-properties-native.json").read_bytes()
        csr = json.loads(output.read_bytes())
        assert csr["generic_rows"] == 4096 and len(csr["tables"]) == 1
        region = csr["tables"][0]
        assert (region["id"],region["offset"],region["data"]["length"]) == (25,196609,4096)
        assert layout["table_offsets"][region["id"]] == region["offset"]
        print("PASS reproducible actual native CSR-properties table and compiled offset", flush=True)
        subprocess.run([str(binary), "--srl-high", str(compiled), str(output)], check=True)
        assert output.read_bytes() == (ROOT / "artifacts/setup/shift-srl-high-native.json").read_bytes()
        sll = json.loads(output.read_bytes())
        assert sll["generic_rows"] == 2097152 and len(sll["tables"]) == 1
        region = sll["tables"][0]
        assert (region["id"],region["offset"],region["data"]["length"]) == (51,6557697,2097152)
        assert layout["table_offsets"][region["id"]] == region["offset"]
        print("PASS reproducible actual native SRL-high table and compiled offset", flush=True)
        subprocess.run([str(binary), "--small-range", str(output)], check=True)
        assert output.read_bytes() == (ROOT / "artifacts/setup/mul-div-small-range-native.json").read_bytes()
        print("PASS reproducible native unsigned mul/div byte tables", flush=True)
        subprocess.run([str(binary), "--decoder-padding", str(output)], check=True)
        assert output.read_bytes() == (ROOT / "artifacts/setup/decoder-padding-native.json").read_bytes()
        print("PASS reproducible actual native decoder padding API export", flush=True)
        subprocess.run([str(binary), "--scalars", str(output)], check=True)
        assert output.read_bytes() == (ROOT / "artifacts/setup/scalars-native.json").read_bytes()
        print("PASS reproducible native range16/timestamp19 scalar export", flush=True)
        image, text = temp / "image.bin", temp / "text.bin"
        words = [0x0100a183, 0x0030a823, 0x0100a003, 0xc0001073]
        image.write_bytes(b"".join(word.to_bytes(4, "little") for word in words))
        text.write_bytes(image.read_bytes())
        subprocess.run([str(binary), str(image), str(text), str(output)], check=True)
        assert output.read_bytes() == (ROOT / "artifacts/setup/word-memory-native.json").read_bytes()
        print("PASS little-endian image/text CLI inputs", flush=True)
        holes = [0x0100a183, 0xc0001073, 0x0030a823, 0x0100a003]
        image.write_bytes(b"".join(word.to_bytes(4, "little") for word in holes))
        text.write_bytes(image.read_bytes())
        subprocess.run([str(binary), str(image), str(text), str(output)], check=True)
        assert output.read_bytes() == (ROOT / "artifacts/setup/word-memory-holes-native.json").read_bytes()
        print("PASS reproducible native interior-hole export", flush=True)
        arithmetic = [0x001080b3, 0xfff08113, 0x40208033, 0x000071b7,
                      0x00005217, 0xc0001073, 0x001080b3]
        subprocess.run([str(binary), "--arithmetic-fixture", str(output)], check=True)
        expected = (ROOT / "artifacts/setup/arithmetic-native.json").read_bytes()
        assert output.read_bytes() == expected
        print("PASS reproducible native arithmetic decoder export", flush=True)
        text.write_bytes(b"".join(word.to_bytes(4, "little") for word in arithmetic))
        subprocess.run([str(binary), "--arithmetic", str(text), str(output)], check=True)
        assert output.read_bytes() == expected
        print("PASS arithmetic little-endian text CLI input", flush=True)
        control = [0xffdff0ef, 0xc0001073, 0xfff0b013]
        subprocess.run([str(binary), "--control-decoder-fixture", str(output)], check=True)
        expected_control = (ROOT / "artifacts/setup/jump-decoder-native.json").read_bytes()
        assert output.read_bytes() == expected_control
        text.write_bytes(b"".join(word.to_bytes(4, "little") for word in control))
        subprocess.run([str(binary), "--control-decoder", str(text), str(output)], check=True)
        assert output.read_bytes() == expected_control
        print("PASS reproducible native signed control decoder and binary text input", flush=True)
        for label, content in [("partial control text", b"xx"),
                               ("oversized control text", bytes(4194308))]:
            text.write_bytes(content)
            output.unlink(missing_ok=True)
            result = subprocess.run([str(binary), "--control-decoder", str(text), str(output)],
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            assert result.returncode != 0 and not output.exists(), label
            print("PASS reject " + label, flush=True)
        for label, content in [("partial arithmetic text", b"xx"),
                               ("oversized arithmetic text", bytes(4194308))]:
            text.write_bytes(content)
            output.unlink(missing_ok=True)
            result = subprocess.run([str(binary), "--arithmetic", str(text), str(output)],
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            assert result.returncode != 0 and not output.exists(), label
            print("PASS reject " + label, flush=True)
        subprocess.run([str(binary), "--shift-decoder-fixture", str(output)], check=True)
        expected_shift = (ROOT / "artifacts/setup/shift-decoder-native.json").read_bytes()
        assert output.read_bytes() == expected_shift
        shift_words = [2134451, 2150835, 1075892659, 2146739, 2154931, 2159027, 32543123, 32559507, 1106301331, 4293968275, 2147541395, 2146496915, 2134067, 2150451, 1075892275, 2146355, 2154547, 2158643, 32542739, 32559123, 1106300947, 4293967891, 2147541011, 2146496531, 1081523]
        text.write_bytes(b"".join(word.to_bytes(4, "little") for word in shift_words))
        subprocess.run([str(binary), "--shift-decoder", str(text), str(output)], check=True)
        assert output.read_bytes() == expected_shift
        print("PASS reproducible native shift/binop decoder and original x0 binary text", flush=True)
        # Actual empty CSR allow-list rejects UNIMP/CSRRW; REV8/rotates and
        # illegal RV32 shift payloads belong outside this ordinary certificate.
        text.write_bytes(b"".join(word.to_bytes(4, "little") for word in
            [0xc0001073, 0x6980d193, 0x6010d193, 0x02009193]))
        subprocess.run([str(binary), "--shift-decoder", str(text), str(output)], check=True)
        rejected = json.loads(output.read_bytes())
        def sample(column, index):
            for block in column["blocks"]:
                kind = block["kind"]
                length = block.get("length", len(block.get("values", [])) * block.get("repetitions", 1))
                if index < length:
                    if kind == "affine": return block["first"] + block["step"] * index
                    if kind == "dense": return block["values"][index]
                    return block["values"][index % len(block["values"])] + block["stride"] * (index // len(block["values"]))
                index -= length
            raise AssertionError("missing native column value")
        assert all(sample(column, i) == (1 << 31) - 2 for i in range(4)
                   for column in rejected["decoder"]["columns"])
        print("PASS actual native empty-CSR filtering and unsupported REV8/rotate/shift words", flush=True)
        for label, content in [("partial shift text", b"xx"),
                               ("oversized shift text", bytes(4194308))]:
            text.write_bytes(content)
            output.unlink(missing_ok=True)
            result = subprocess.run([str(binary), "--shift-decoder", str(text), str(output)],
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            assert result.returncode != 0 and not output.exists(), label
            print("PASS reject " + label, flush=True)
        for label, image_bytes, text_bytes in [
            ("partial image word", b"xx", text.read_bytes()),
            ("partial text word", image.read_bytes(), b"xx"),
            ("oversized image", bytes(4194308), text.read_bytes()),
            ("oversized text", image.read_bytes(), bytes(4194308)),
        ]:
            image.write_bytes(image_bytes)
            text.write_bytes(text_bytes)
            output.unlink(missing_ok=True)
            result = subprocess.run([str(binary), str(image), str(text), str(output)],
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            assert result.returncode != 0 and not output.exists(), label
            print("PASS reject " + label, flush=True)

if __name__ == "__main__":
    main()
