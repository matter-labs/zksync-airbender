#!/usr/bin/env python3
"""Run inside bounded_fv.py: native exporter reproducibility and input checks."""
from pathlib import Path
import os
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
    subprocess.run([*CARGO, "check", *OPTIONS], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix="airbender-v2-native-") as directory:
        temp = Path(directory)
        output = temp / "setup.json"
        subprocess.run([*CARGO, "run", *OPTIONS, "--", "--fixture", str(output)], cwd=ROOT, check=True)
        assert output.read_bytes() == (ROOT / "artifacts/setup/word-memory-native.json").read_bytes()
        print("PASS reproducible native setup export", flush=True)
        binary = TARGET / "debug/airbender-v2-native-setup-exporter"
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
