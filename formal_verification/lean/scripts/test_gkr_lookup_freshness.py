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
from gkr_lookup_source_certificate import synthesis as source_synthesis
from gkr_memory_certificate import synthesis as memory_synthesis
from gkr_helper_instances import synthesis as helper_synthesis


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--stage", choices=("metadata", "consumed", "memory", "helper"), default="metadata")
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
    module = '''import GKRProtocol.LookupSourceImport
import GKRProtocol.NativeLookupImport
import GKRProtocol.ConsumerNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace Probe
import_compiler_lookup_fields native from "pair.json"
  source "source.json" certificate "certificate.json"
'''
    if args.stage == "consumed":
        selectors = source_synthesis(json.loads(inputs["pair.json"].read_text()),
                                     json.loads(inputs["certificate.json"].read_text()))
        encoded = json.dumps(json.dumps(selectors, separators=(",", ":")))
        module += ('import_native_lookups native from "pair.json"\n'
                   'import_source_lookups bridge from "pair.json"\n'
                   '  certificate "certificate.json"\n'
                   f'  selectors {encoded}\n'
                   '  reference Probe.native\n'
                   '  typing Airbender.Compiler.ConsumerNative.AddSubCached.native.typing\n'
                   f'  phase 3 start 0 stop {len(selectors["operands"])}\n')
    elif args.stage == "memory":
        selectors = memory_synthesis(json.loads(inputs["pair.json"].read_text()),
                                     json.loads(inputs["source.json"].read_text()))
        encoded = json.dumps(json.dumps(selectors, separators=(",", ":")))
        module = ('import GKRProtocol.MemoryImport\n'
                  'import GKRProtocol.ConsumerNative.AddSubCached\n'
                  'open Airbender Airbender.Compiler\n'
                  'set_option warningAsError true\n'
                  'set_option Elab.async false\n'
                  'set_option maxRecDepth 32768\n'
                  'set_option maxHeartbeats 4000000\n'
                  'namespace Probe\n'
                  'import_native_products native from "pair.json"\n'
                  'import_source_memory bridge from "pair.json" source "source.json"\n'
                  f'  selectors {encoded}\n'
                  '  word_bits 2 native_model Probe.native\n'
                  '  typing Airbender.Compiler.ConsumerNative.AddSubCached.native.typing\n')
    elif args.stage == "helper":
        selectors = helper_synthesis(json.loads(inputs["pair.json"].read_text()),
                                     json.loads(inputs["source.json"].read_text()),
                                     json.loads(inputs["certificate.json"].read_text()))
        encoded = json.dumps(json.dumps(selectors, separators=(",", ":")))
        module = ('import GKRProtocol.HelperImport\n'
                  'import GKRProtocol.NativeLookupImport\n'
                  'import GKRProtocol.MemoryNative.AddSubCached\n'
                  'open Airbender Airbender.Compiler\n'
                  'set_option warningAsError true\n'
                  'set_option Elab.async false\n'
                  'set_option maxRecDepth 32768\n'
                  'set_option maxHeartbeats 4000000\n'
                  'namespace Probe\n'
                  'import_native_lookups native from "pair.json"\n'
                  'import_source_helpers bridge from "pair.json" source "source.json"\n'
                  f'  selectors {encoded}\n'
                  '  memory_model Airbender.Compiler.MemoryNative.AddSubCached.native\n'
                  '  lookup_model Probe.native\n'
                  '  typing Airbender.Compiler.ConsumerNative.AddSubCached.native.typing\n')
    (work / "Probe.lean").write_text(module + 'end Probe\n')
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
        if not success and args.stage == "consumed" and "bank.placement" not in text:
            raise RuntimeError(f"Failure was not in the consumed source-column checker; see {log}")
        if not success and args.stage == "memory" and "memoryReadCertificate0" not in text:
            raise RuntimeError(f"Failure was not in the source-memory fingerprint checker; see {log}")
        if not success and args.stage == "helper" and "candidate9" not in text:
            raise RuntimeError(f"Failure was not in the consumed timestamp-helper checker; see {log}")
        print(f"PASS {label}: {'valid proof' if success else 'dependency rebuilt and kernel rejected corruption'}", flush=True)

    run("warm", True)
    # Corrupt an actual native lookup input while retaining the original
    # authored source, address bank, certificate, dimensions and module source.
    pair_path = work / "pair.json"
    original = pair_path.read_bytes()
    module_source = (work / "Probe.lean").read_bytes()
    try:
        pair = json.loads(original)
        geometry = (pair["source"]["num_variables"], pair["circuit"]["trace_len"],
                    len(pair["circuit"]["layers"]), pair["circuit"]["memory_layout"]["total_width"],
                    pair["circuit"]["witness_layout"]["total_width"])
        if args.stage == "metadata":
            pair["circuit"]["range_check_16_lookup_expressions"][0]["input"]["constant"] = 1
        elif args.stage == "consumed":
            # Mutate the consumed query operand alone. Original source and native
            # request metadata remain unchanged, so the source-operand bridge
            # must be the rejecting boundary.
            gates = [gate["enforced_relation"] for layer in pair["circuit"]["layers"]
                     for gate in layer["gates"] + layer["gates_with_external_connections"]]
            selected = next(operand for operand in selectors["operands"]
                            if operand["kind"] == "query" and not operand["expansion"] and
                            "LookupFromMaterializedBaseInputWithSetup" in gates[operand["locator"][0]])
            gate = gates[selected["locator"][0]]["LookupFromMaterializedBaseInputWithSetup"]
            replacement = {"BaseLayerWitness": 0}
            if gate["input"] == replacement:
                raise ValueError("consumed operand fixture already uses the corruption target")
            gate["input"] = replacement
        elif args.stage == "memory":
            # Keep the original source, metadata, ports and selector witnesses.
            # The actual cached read tuple alone acquires a different timestamp.
            cache = next(cache[1]["MemoryTuple"] for layer in pair["circuit"]["layers"]
                         for cache in layer["cached_relations"] if "MemoryTuple" in cache[1])
            cache["timestamp_offset"] += 1
        else:
            # Change the consumed low-comparison cache for the first memory
            # port, retaining the original source and timestamp query metadata.
            selected = next(operand for operand in selectors["operands"] if operand["source_index"] == 2)
            caches = [cache for layer in pair["circuit"]["layers"] for cache in layer["cached_relations"]]
            choices = [caches[index][1]["SingleColumnLookup"] for index in selected["expansion"]
                       if index < len(caches) and "SingleColumnLookup" in caches[index][1]]
            if len(choices) != 1:
                raise ValueError("timestamp helper fixture requires one actual scalar cache")
            row = choices[0]["relation"]["input"]
            row["constant"] = (row["constant"] + 268435454) % 2013265921
        assert geometry == (pair["source"]["num_variables"], pair["circuit"]["trace_len"],
                            len(pair["circuit"]["layers"]), pair["circuit"]["memory_layout"]["total_width"],
                            pair["circuit"]["witness_layout"]["total_width"])
        pair_path.write_text(json.dumps(pair, separators=(",", ":")) + "\n")
        label = {"metadata": "changed-native-coefficient", "consumed": "changed-consumed-operand",
                 "memory": "changed-memory-timestamp", "helper": "changed-helper-timestamp"}[args.stage]
        run(label, False)
    finally:
        pair_path.write_bytes(original)
    run("restored", True)
    if (work / "Probe.lean").read_bytes() != module_source:
        raise RuntimeError("Freshness control changed module source")
    print("PASS actual input-file invalidation; retained artifacts were unchanged", flush=True)


if __name__ == "__main__":
    main()
