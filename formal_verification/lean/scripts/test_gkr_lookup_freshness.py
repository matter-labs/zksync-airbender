#!/usr/bin/env python3
"""Exercise actual Lake input invalidation and kernel rejection in a scratch project.

Run under bounded_fv.py. All compiler invocations are sequential. Retained repo
artifacts and their proof caches are never mutated by this control.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess

from check_gkr_lookup_certificates import verify
from export_gkr_translations import LEAN


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, required=True)
    args = parser.parse_args()
    verify()
    work = args.work_dir.resolve()
    if work.exists():
        raise SystemExit("Use a fresh scratch directory for the compiler freshness control")
    work.mkdir(parents=True)
    parent = LEAN / "artifacts/compiler"
    inputs = {"pair.json": parent / "add-sub-cached.json",
              "source.json": parent / "add-sub-cached-source.json",
              "certificate.json": parent / "lookup/add-sub-cached.json"}
    for name, original in inputs.items():
        shutil.copyfile(original, work / name)
    shutil.copyfile(LEAN / "lean-toolchain", work / "lean-toolchain")
    config = 'name = "gkr_freshness_probe"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "Probe"\nneeds = ["pairInput", "sourceInput", "certificateInput"]\n'
    # Reuse the exact locked dependency resolution and actual package folders.
    # No compiler traces, proof outputs or timestamps are copied. Normal Lake
    # input-file invalidation still runs in the independent Probe library.
    parent_manifest = json.loads((LEAN / "lake-manifest.json").read_text())
    config += f'\n[[require]]\nname = "airbender_circuits"\npath = {json.dumps(str(LEAN))}\n'
    resolution = dict(parent_manifest, name="gkr_freshness_probe",
                      packagesDir=str(LEAN / parent_manifest["packagesDir"]))
    resolution["packages"] = [dict(package, inherited=True) for package in parent_manifest["packages"]]
    resolution["packages"].append({"type": "path", "scope": "", "name": "airbender_circuits",
                                   "manifestFile": "lake-manifest.json", "inherited": False,
                                   "dir": str(LEAN), "configFile": "lakefile.toml"})
    (work / "lake-manifest.json").write_text(json.dumps(resolution, indent=2) + "\n")
    for name, path in (("pairInput", "pair.json"), ("sourceInput", "source.json"), ("certificateInput", "certificate.json")):
        config += f'\n[[input_file]]\nname = "{name}"\npath = "{path}"\ntext = true\n'
    (work / "lakefile.toml").write_text(config)
    (work / "Probe.lean").write_text('''import GKRProtocol.LookupImport
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace Probe
import_compiler_lookup_fields native from "pair.json"
  source "source.json" certificate "certificate.json"
end Probe
''')
    environment = dict(os.environ, LEAN_NUM_THREADS="1", MATHLIB_NO_CACHE_ON_UPDATE="1")
    command = ["lake", "--no-cache", "build", "+Probe:olean"]

    def run(label, success):
        log = work / (label + ".log")
        with log.open("x") as stream:
            result = subprocess.run(command, cwd=work, env=environment,
                                    stdout=stream, stderr=subprocess.STDOUT)
        text = log.read_text()
        if (result.returncode == 0) != success:
            raise RuntimeError(f"Unexpected {label} result {result.returncode}; see {log}")
        if not success and ("Probe.lean:" not in text or "decide" not in text or "error:" not in text):
            raise RuntimeError(f"Failure was not the intended kernel certificate rejection; see {log}")
        print(f"PASS {label}: {'valid proof' if success else 'dependency rebuilt and kernel rejected corruption'}", flush=True)

    run("warm", True)
    # Corrupt an actual native lookup coefficient while retaining the original
    # authored source, address bank, certificate, dimensions and module source.
    pair_path = work / "pair.json"
    original = pair_path.read_bytes()
    module_source = (work / "Probe.lean").read_bytes()
    try:
        pair = json.loads(original)
        geometry = (pair["source"]["num_variables"], pair["circuit"]["trace_len"],
                    len(pair["circuit"]["layers"]), pair["circuit"]["memory_layout"]["total_width"],
                    pair["circuit"]["witness_layout"]["total_width"])
        pair["circuit"]["range_check_16_lookup_expressions"][0]["input"]["constant"] = 1
        assert geometry == (pair["source"]["num_variables"], pair["circuit"]["trace_len"],
                            len(pair["circuit"]["layers"]), pair["circuit"]["memory_layout"]["total_width"],
                            pair["circuit"]["witness_layout"]["total_width"])
        pair_path.write_text(json.dumps(pair, separators=(",", ":")) + "\n")
        run("changed-native-coefficient", False)
    finally:
        pair_path.write_bytes(original)
    run("restored", True)
    if (work / "Probe.lean").read_bytes() != module_source:
        raise RuntimeError("Freshness control changed module source")
    print("PASS actual input-file invalidation; retained artifacts were unchanged", flush=True)


if __name__ == "__main__":
    main()
