#!/usr/bin/env python3
"""Check source generation and compare every interpreted capture byte."""

import argparse
import subprocess
import tempfile
from pathlib import Path

from generate_setup_source_banks import FAMILIES, LEAN, generate


def check(family=None):
    for label, filename in FAMILIES.items():
        if family and family != label:
            continue
        for module, expected in generate(label, filename).items():
            path = LEAN / (module.replace(".", "/") + ".lean")
            if not path.is_file() or path.read_text() != expected:
                raise ValueError(f"Stale setup source data: {path.relative_to(LEAN)}")
        source = f'''import Airbender.Data.Setup.Source.{label}
#eval show IO Unit from do
  let actual := Airbender.Setup.SourceCapture{label}.source
  let expected ← IO.FS.readFile "artifacts/setup/{filename}.json"
  unless actual == expected do
    throw (IO.userError "interpreted setup source changed a captured byte")
  IO.println "PASS exact {filename} source byte comparison"
'''
        with tempfile.TemporaryDirectory(prefix="airbender-source-bytes-") as directory:
            path = Path(directory) / "Check.lean"
            path.write_text(source)
            subprocess.run(["lean", "-j1", "-DElab.async=false", str(path)], cwd=LEAN, check=True)
    print("PASS setup source generation and byte identity")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", choices=FAMILIES)
    args = parser.parse_args()
    check(args.family)


if __name__ == "__main__":
    main()
