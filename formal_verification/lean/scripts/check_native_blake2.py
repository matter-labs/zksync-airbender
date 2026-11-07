#!/usr/bin/env python3
"""Run under bounded_fv.py: selected native Blake2 compilation, no workspace build."""
from pathlib import Path
import json, os, re, subprocess, tempfile
ROOT = Path(__file__).resolve().parent.parent
REPO = ROOT.parent.parent
MANIFEST = ROOT.parent / "native_setup_exporter/Cargo.toml"
TARGET = ROOT / ".lake/native-setup-target"
ARTIFACT = ROOT / "artifacts/circuits/blake2-native-layout.json"
BASE = "67ee094449abaebc77e58435f130ce6ea27721e5"
PARENT = "a873bb0f7ca6cacd3ff4641dc8c85970c970184e"


def native_sources():
    paths = ["cs/src/delegation/blake2_round_with_extended_control/mod.rs",
             "circuit_defs/blake2_with_compression/src/lib.rs",
             "common_constants/src/delegation_types/blake2s_with_control.rs",
             "circuit_defs/unrolled_circuits/unified_reduced_machine/src/lib.rs",
             "cs/src/one_row_compiler/compile_layout.rs",
             "cs/src/definitions/memory_tree.rs",
             "cs/src/delegation/blake2_single_round/mod.rs",
             "blake2s_u32/src/lib.rs",
             "cs/src/definitions/table_type.rs"]
    sources = {}
    for path in paths:
        blob = subprocess.check_output(["git", "show", BASE + ":" + path], cwd=REPO)
        assert (REPO / path).read_bytes() == blob, path
        sources[path] = blob.decode()
    enum = sources[paths[-1]].split("pub enum TableType {",1)[1].split("}",1)[0]
    ids, current = {}, -1
    for name, explicit in re.findall(r"^\s+(\w+)(?: = (\d+))?,", enum, re.M):
        current = int(explicit) if explicit else current + 1
        ids[name] = current
    assert [ids[name] for name in ("Xor","Xor3","Xor4","Xor7","Xor9")] == [4,26,27,28,29]
    worker = sources[paths[1]]
    assert "pub const DOMAIN_SIZE: usize = 1 << 20;" in worker
    assert "pub const NUM_DELEGATION_CYCLES: usize = DOMAIN_SIZE - 1;" in worker
    assert "common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER" in worker
    assert "BLAKE2S_DELEGATION_CSR_REGISTER" in sources[paths[3]]
    assert "BLAKE2S_DELEGATION_CSR_REGISTER: u32 = super::NON_DETERMINISM_CSR + 7;" in sources[paths[2]]
    # Exact selected native constructor statements, with the source constant
    # DOMAIN_SIZE.trailing_zeros() reduced to its independently checked value20.
    source = (MANIFEST.parent / "src/main.rs").read_text()
    start = source.index('    if args.len() == 3 && args[1] == "--blake2-layout" {')
    end = source.index('    if args.len() == 3 && args[1] == "--reduced-layout" {', start)
    branch = source[start:end]
    for clause in ["let mut cs = BasicAssembly::<Mersenne31Field>::new();",
                   "define_blake2_with_extended_control_delegation_circuit(&mut cs);",
                   "let (circuit_output, _) = cs.finalize();", "let compiler = OneRowCompiler::default();"]:
        assert clause in worker and clause in branch
    assert ".compile_to_evaluate_delegations(circuit_output, DOMAIN_SIZE.trailing_zeros() as usize)" in worker
    assert "compiler.compile_to_evaluate_delegations(circuit_output, 20)" in branch
    previous = subprocess.check_output(["git", "show", PARENT + ":formal_verification/native_setup_exporter/src/main.rs"], cwd=REPO).decode()
    function_start = source.index("fn export_blake2_fixed(")
    function_end = source.index("/// Materialize each native region once", function_start)
    stripped = source[:function_start] + source[function_end:]
    mode_start = stripped.index('    if args.len() == 4 && args[1] == "--blake2-fixed" {')
    mode_end = stripped.index('    if args.len() == 5 && args[1] == "--reduced-csr" {', mode_start)
    stripped = stripped[:mode_start] + stripped[mode_end:]
    assert stripped == previous, "unrelated exporter branches changed"


def inspect(data):
    assert data["trace_len"] == 1048576 and data["executor_family_decoder_table_size"] == 0
    assert [len(data[k]) for k in ("degree_2_constraints", "degree_1_constraints", "variable_mapping")] == [301, 51, 871]
    w, m = data["witness_layout"], data["memory_layout"]
    assert [len(w[k]) for k in ("range_check_16_lookup_expressions", "timestamp_range_check_lookup_expressions", "width_3_lookups")] == [2, 86, 208]
    assert [w["total_width"], m["total_width"], data["setup_layout"]["total_width"]] == [648, 226, 6]
    assert m["delegation_request_layout"] is None and m["machine_state_layout"] is None
    assert m["delegation_processor_layout"] == {"multiplicity":{"start":0,"num_elements":1}, "abi_mem_offset_high":{"start":1,"num_elements":1}, "write_timestamp":{"start":2,"num_elements":1}}
    accesses = m["register_and_indirect_accesses"]
    count = 0
    for slot, entry in enumerate(accesses):
        tag = "WriteAccess" if slot == 2 else "ReadAccess"
        assert list(entry["register_access"]) == [tag]
        assert entry["register_access"][tag]["register_index"] == 10 + slot
        indirects = entry["indirect_accesses"]
        assert len(indirects) == [24,16,0][slot]
        for i, item in enumerate(indirects):
            tag = "WriteAccess" if slot == 0 else "ReadAccess"
            assert list(item) == [tag]
            body = item[tag]
            assert body["offset_constant"] == 4*i and body["variable_dependent"] is None
            assert body["address_derivation_carry_bit"]["num_elements"] == 0
        count += 1 + len(indirects)
    assert len(accesses) == 3 and count == 43
    assert data["total_tables_size"] == 344384
    assert data["stage_2_layout"]["delegation_processing_aux_poly"] == {"start":1064,"num_elements":1}


def main():
    os.environ["RAYON_NUM_THREADS"] = "1"
    native_sources()
    cargo = ["--offline", "--locked", "--manifest-path", str(MANIFEST), "--target-dir", str(TARGET), "-j1", "-p", "airbender-v2-native-setup-exporter", "--bin", "airbender-v2-native-setup-exporter"]
    subprocess.run(["cargo", "check", *cargo], cwd=ROOT, check=True)
    subprocess.run(["cargo", "build", *cargo], cwd=ROOT, check=True)
    binary = TARGET / "debug/airbender-v2-native-setup-exporter"
    with tempfile.TemporaryDirectory(prefix="v2-blake2-native-") as directory:
        output = Path(directory) / "layout.json"
        for _ in range(2):
            subprocess.run([str(binary), "--blake2-layout", str(output)], check=True)
            assert output.read_bytes() == ARTIFACT.read_bytes()
            inspect(json.loads(output.read_bytes()))
        historical = REPO / "circuit_defs/blake2_with_compression/generated/layout"
        assert historical.read_bytes() == subprocess.check_output(["git", "show", BASE + ":circuit_defs/blake2_with_compression/generated/layout"], cwd=REPO)
        assert json.loads(historical.read_bytes()) == json.loads(output.read_bytes())
        output.unlink()
        for args in [["--blake2-layout"], ["--blake2-layout", str(output), "extra"]]:
            result = subprocess.run([str(binary), *args], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            assert result.returncode != 0 and not output.exists()
    print("PASS native source/configuration and constructor,352 equations/296 lookups/43 ABI accesses,repeat byte reproduction,historical parsed identity and2 malformed CLI controls", flush=True)

if __name__ == "__main__": main()
