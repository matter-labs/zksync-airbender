#!/usr/bin/env python3
"""Validate the retained Sail snapshot without regeneration or a compiler."""

import argparse
import hashlib
import json
from pathlib import Path

import generate_sail as generation

# Independent pin of the original compiler output, before the recorded platform
# header/flag transformation. Updating manifest hashes cannot relax this check.
ORIGINAL_FUNCTIONS_SHA256 = "2b0d862a9feff63d32fefd0a1f967bd4c75485601387cb8e4b258a73bd2bd492"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check(root=generation.ROOT):
    root = Path(root).resolve()
    snapshot = root / "generated/sail-rv32"
    manifest = json.loads((snapshot / "provenance.json").read_text())
    for key, expected in (("model_revision", generation.MODEL_REV),
                          ("compiler_revision", generation.COMPILER_REV),
                          ("runtime_revision", generation.RUNTIME_REV)):
        require(manifest[key] == expected, "Changed Sail pin: " + key)
    binding = manifest["platform_parameterization"]
    require(binding["original_functions_sha256"] == ORIGINAL_FUNCTIONS_SHA256,
            "Changed original compiler-output pin")
    require(binding["inserted_header"] == generation.MEMORY_PLATFORM_HEADER,
            "Changed recorded platform header")
    require(binding["insertion_marker"] == "namespace Functions\n\n",
            "Changed insertion marker")
    require(binding["flag_bindings"] == generation.PLATFORM_FLAG_BINDINGS,
            "Changed recorded device transformation")
    require(binding["externs"] == ["plat_term_write", "load_reservation", "match_reservation"],
            "Changed platform handler bindings")
    require(binding["upstream_devices"] == {"clint": True, "sig": True},
            "Changed upstream devices")
    require(binding["airbender_devices"] == {"clint": False, "sig": False},
            "Changed Airbender devices")
    source = (snapshot / "SailRV32.lean").read_text()
    original = generation.restore_functions(source)
    require(hashlib.sha256(original.encode()).hexdigest() == ORIGINAL_FUNCTIONS_SHA256,
            "Recovered source differs from pinned original compiler output")
    require(generation.parameterize_functions(original) == source,
            "Platform transformation is not reversible")
    fingerprints = generation.instruction_fingerprints(original)
    require(generation.instruction_fingerprints(source) == fingerprints,
            "A standard instruction declaration changed")
    require(binding["instruction_sha256"] == fingerprints,
            "Instruction fingerprints differ from recovered original")
    expected = manifest["generated_sha256"]
    actual = {str(path.relative_to(snapshot)): generation.digest(path)
              for path in snapshot.rglob("*.lean")}
    require(actual == expected, "Generated Lean inventory or hashes differ")
    platform = root / "scripts/SailPlatform.lean"
    require(manifest["platform_binding"]["source"] == "scripts/SailPlatform.lean",
            "Changed platform support source")
    require(generation.digest(platform) == manifest["platform_binding"]["sha256"],
            "Platform support source hash differs")
    require(platform.read_bytes() == (snapshot / "SailRV32/SailPlatform.lean").read_bytes(),
            "Source and copied platform support differ")
    for relative, key in (("scripts/sail_slice.ml", "adapter_sha256"),
                          ("generated/sail-rv32/rv32d_v256_e32.json", "config_sha256"),
                          ("generated/sail-rv32/extracted_base_pc.sail", "extracted_source_sha256")):
        require(generation.digest(root / relative) == manifest[key],
                "Changed retained generation input: " + relative)
    evidence = binding["airbender_evidence_sha256"]
    require(set(evidence) == {
        "riscv_transpiler/src/vm/ram_with_rom_region.rs", "riscv_transpiler/src/jit/impls.rs",
        "cs/src/gkr_circuits/unified_reduced_machine/mem_word_only_lw_sw.rs",
        "riscv_common/src/lds/1gb_total/memory.x"}, "Changed native platform evidence inventory")
    for relative, expected_hash in evidence.items():
        require(generation.digest(root.parent.parent / relative) == expected_hash,
                "Changed native platform evidence: " + relative)
    return {"generated_files": len(actual), "instructions": len(fingerprints),
            "native_evidence": len(evidence), "original_functions_sha256": ORIGINAL_FUNCTIONS_SHA256}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=generation.ROOT,
                        help="Lean project root (supports isolated failure-control fixtures)")
    args = parser.parse_args()
    try:
        result = check(args.root)
    except (ValueError, KeyError, OSError) as error:
        parser.exit(1, f"Sail reference check failed: {error}\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
