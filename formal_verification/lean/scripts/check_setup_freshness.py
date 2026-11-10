#!/usr/bin/env python3
"""Reconstruct all sixteen retained native setups with existing scoped commands.

Each regenerate/export invocation is ONE job for the external bounded single
worker. This script never raises resource limits, schedules parallel jobs, runs
GPU work or changes native generators or retained setup payloads. Explicit
requalification promotes source receipts only after all native comparisons and
dep-info checks succeed; candidates alone never satisfy the retained drift guard.
"""

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import struct
import subprocess
import sys
import tempfile

import check_setup_artifacts as retained
import check_native_evidence as evidence

REPO = retained.REPO
GENERATORS = {
    "add-sub": ("gkr_circuits::add_sub_family::circuit::test", "add_sub_lui_auipc_mop"),
    "jump-branch": ("gkr_circuits::jump_branch_slt_family::circuit::test", "jump_branch_slt_circuit"),
    "mul-div": ("gkr_circuits::mul_div::circuit::test", "unsigned_mul_div"),
    "shift-binop": ("gkr_circuits::binary_shifts_family::circuit::test", "shift_binop"),
    "word-memory": ("gkr_circuits::mem_word_only::circuit::test", "mem_word_only_circuit"),
    "subword-memory": ("gkr_circuits::mem_subword_only::circuit::test", "mem_subword_only_circuit"),
    "unified": ("gkr_circuits::unified_reduced_machine::circuit::test", "unified_reduced_machine"),
    "bigint": ("gkr_circuits::delegation::bigint_with_control::test", "bigint_with_extended_control"),
    "blake-g": ("gkr_circuits::delegation::blake2_g_function::test", "blake2_g_function"),
    "blake-round": ("gkr_circuits::delegation::blake2_round_with_extended_control::test", "blake2_with_extended_control"),
    "keccak": ("gkr_circuits::delegation::keccak_special5::test", "keccak_special5"),
    "inits-and-teardowns": ("gkr_compiler::inits_and_teardowns::test", "inits_and_teardowns"),
}
EXPORT_ONLY_FAMILIES = ("keccak-column-parity", "keccak-theta-rho", "keccak-chi5")
FAMILIES = tuple(GENERATORS) + EXPORT_ONLY_FAMILIES + ("decoder-smoke",)
PROGRAM_FAMILIES = {"add-sub", "jump-branch", "mul-div", "shift-binop", "word-memory", "subword-memory", "unified"}


def require_native_environment(environment):
    # skip_if_ci! tests PRESENCE, not a parsed boolean. CI=false also skips.
    if "CI" in environment:
        raise ValueError("Native freshness requires CI absent: invoke with env -u CI (CI=false still skips)")


def generator_test(family):
    module, suffix = GENERATORS[family]
    return f"{module}::compile_{suffix}_into_no_caches_gkr"


def test_command(package, test):
    return ["cargo", "test", "--locked", "-p", package, "--lib", test,
            "--", "--exact", "--nocapture", "--test-threads=1"]


def validate_test_output(output, test):
    if re.search(r"skipping\b.*\bCI\b", output, re.IGNORECASE):
        raise ValueError(f"Native generator skipped in CI: {test}")
    if len(re.findall(r"(?m)^running 1 test\s*$", output)) != 1:
        raise ValueError(f"Expected exactly one executed native test: {test}")
    # --nocapture may interleave compiler prints after the named test prefix.
    if len(re.findall(r"(?m)^test " + re.escape(test) + r" \.\.\.(?: .*)?$", output)) != 1:
        raise ValueError(f"Exact selected native test did not pass: {test}")
    summaries = re.findall(r"(?m)^test result: ok\. 1 passed; 0 failed; 0 ignored; 0 measured; \d+ filtered out;.*$", output)
    if len(summaries) != 1 or len(re.findall(r"(?m)^test result:", output)) != 1:
        raise ValueError(f"Expected one passing native test summary with no skips: {test}")


def compare_artifact(fresh, expected):
    if not Path(fresh).is_file() or not Path(fresh).stat().st_size:
        raise ValueError(f"Missing fresh setup artifact: {Path(fresh).name}")
    actual, original = retained.read_json(fresh), retained.read_json(expected)
    # Preserve JSON scalar types and all array orders; object-key whitespace/order
    # is immaterial. No geometry-only comparison, row sorting or block expansion.
    encode = lambda item: json.dumps(item, sort_keys=True, separators=(",", ":"), allow_nan=False)
    if encode(actual) != encode(original):
        raise ValueError(f"Fresh setup differs from retained complete JSON: {Path(fresh).name}; {first_difference(actual, original)}")
    return retained.sha256(fresh)


def first_difference(actual, expected, path='$'):
    """A bounded field diagnostic; never dump a generated circuit into logs."""
    if type(actual) is not type(expected):
        return f"{path}: type {type(actual).__name__} != {type(expected).__name__}"
    if isinstance(actual, dict):
        if actual.keys() != expected.keys():
            return f"{path}: object keys differ"
        for key in actual:
            difference = first_difference(actual[key], expected[key], path + '.' + key)
            if difference:
                return difference
    elif isinstance(actual, list):
        if len(actual) != len(expected):
            return f"{path}: length {len(actual)} != {len(expected)}"
        for index, (left, right) in enumerate(zip(actual, expected)):
            difference = first_difference(left, right, f'{path}[{index}]')
            if difference:
                return difference
    elif actual != expected:
        return f"{path}: {str(actual)[:120]} != {str(expected)[:120]}"
    return None


def compare_directory(directory, artifacts=retained.ARTIFACTS):
    directory, artifacts = Path(directory), Path(artifacts)
    expected = {family + ".json" for family in FAMILIES}
    actual = {path.name for path in directory.glob("*.json")}
    if actual != expected:
        raise ValueError(f"Fresh setup inventory differs; missing={sorted(expected-actual)}, unexpected={sorted(actual-expected)}")
    for name in sorted(expected):
        compare_artifact(directory / name, artifacts / name)
    return len(expected)


def manifest_path(repo):
    return repo / "formal_verification/lean/artifacts/setup/manifest.json"


def requalification_manifest(repo):
    """Snapshot current source pins without asserting native reconstruction."""
    manifest = retained.read_json(manifest_path(repo))
    sources, crates = retained.source_inventory(repo)
    inventory = manifest["source_inventory"]
    if (inventory["root_crates"] != list(retained.SOURCE_ROOT_CRATES) or
            inventory["local_crates"] != crates or set(sources) != set(manifest["source_sha256"])):
        raise ValueError("Requalification cannot change the source inventory; review the Cargo closure first")
    candidate = copy.deepcopy(manifest)
    candidate["source_sha256"] = {name: retained.sha256(retained.checked_path(repo, name)) for name in sources}
    smoke = candidate["circuit_identities"]["decoder-smoke.json"]
    smoke["constructor_test"] = retained.SMOKE_TEST
    smoke["constructor_sha256"] = retained.sha256(retained.checked_path(repo, smoke["constructor_path"]))
    return candidate


def prepare_requalification(repo, work):
    """Write an unqualified snapshot outside the checkout; keep retained pins."""
    retained.prepare_native_lock(repo, retained.read_json(manifest_path(repo)), prepare=True)
    candidate = requalification_manifest(repo)
    retained.check(repo, manifest=candidate)
    evidence.check(repo)
    work = work_directory(work, repo)
    record = {"schema_version": 1, "status": "unqualified",
              "retained_manifest_sha256": retained.sha256(manifest_path(repo)), "manifest": candidate}
    path = work / "requalification.json"
    with path.open("x") as stream:
        stream.write(json.dumps(record, indent=2) + "\n")
    print("Prepared UNQUALIFIED source snapshot; retained manifest unchanged; 28 native jobs still required")


def preflight(repo, work=None, requalify=False):
    manifest = retained.read_json(manifest_path(repo))
    if requalify:
        record = retained.read_json(Path(work) / "requalification.json")
        if (record["schema_version"] != 1 or record["status"] != "unqualified" or
                record["retained_manifest_sha256"] != retained.sha256(manifest_path(repo)) or
                record["manifest"] != requalification_manifest(repo)):
            raise ValueError("Requalification snapshot changed or inputs drifted; start again in a new work directory")
        manifest = record["manifest"]
    retained.check(repo, manifest=manifest)
    evidence.check(repo)
    return manifest


def work_directory(path, repo):
    work = Path(path).resolve()
    if work.is_relative_to(repo):
        raise ValueError("Use an external empty scratch directory for native freshness outputs")
    work.mkdir(parents=True, exist_ok=True)
    for name in ("artifacts", "logs", "receipts"):
        (work / name).mkdir(exist_ok=True)
    return work


def run_command(command, repo, environment, log):
    if log.exists():
        raise ValueError(f"Freshness log already exists; use a new work directory: {log}")
    with log.open("x") as stream:
        process = subprocess.Popen(command, cwd=repo, env=environment,
                                   stdout=stream, stderr=subprocess.STDOUT, text=True)
        code = process.wait()
    if code:
        raise ValueError(f"Native command exited {code}; inspect {log}")
    return log.read_text()


def job(mode, family, repo, work, requalify=False):
    require_native_environment(os.environ)
    work = work_directory(work, repo)
    manifest = preflight(repo, work, requalify)
    receipt_path = work / "receipts" / f"{mode}-{family}.json"
    if receipt_path.exists():
        raise ValueError(f"Native job receipt already exists; use a new work directory: {receipt_path}")
    environment = dict(os.environ, CARGO_BUILD_JOBS="1", RAYON_NUM_THREADS="1", CARGO_TERM_COLOR="never")
    environment.pop("AIRBENDER_SETUP_JSON_FIXTURE", None)
    test = None
    before = None
    if mode == "regenerate":
        if family not in GENERATORS:
            raise ValueError(f"No native generator is registered for {family}")
        test = generator_test(family)
        command = test_command("cs", test)
        relative = manifest["circuit_identities"][family + ".json"]["retained_path"]
        output = retained.checked_path(repo, relative)
        before = (output.stat().st_mtime_ns, output.stat().st_ctime_ns)
    else:
        output = work / "artifacts" / (family + ".json")
        if output.exists():
            raise ValueError(f"Fresh output already exists: {output}")
        if family == "decoder-smoke":
            test = retained.SMOKE_TEST
            command = test_command("prover", test)
            environment["AIRBENDER_SETUP_JSON_FIXTURE"] = str(output)
        else:
            args = ["-", "-"]
            if family in PROGRAM_FAMILIES:
                binary = work / "program.bin"
                data = struct.pack("<" + "I" * len(manifest["program_words_unpadded"]), *manifest["program_words_unpadded"])
                if binary.exists() and binary.read_bytes() != data:
                    raise ValueError("Scratch program does not match manifest input words")
                binary.write_bytes(data)
                args = [str(binary), str(binary)]
            command = ["cargo", "run", "--locked", "-p", "execution_prover", "--example",
                       "export_setup_json", "--", family, *args, str(output)]
    log = work / "logs" / f"{mode}-{family}.log"
    print(f"Running {mode} {family}; native output: {log}", flush=True)
    output_text = run_command(command, repo, environment, log)
    if test:
        validate_test_output(output_text, test)
    if mode == "regenerate":
        if not output.is_file() or before == (output.stat().st_mtime_ns, output.stat().st_ctime_ns):
            raise ValueError(f"Selected generator did not rewrite its expected circuit: {output}")
        artifacts = repo / "formal_verification/lean/artifacts/setup"
        fresh = retained.read_json(output)
        expected = retained.read_json(artifacts / (family + ".json"))["circuit"]
        difference = first_difference(fresh, expected)
        if difference:
            failures = work / "failures"
            failures.mkdir(exist_ok=True)
            shutil.copyfile(output, failures / (family + '-circuit.json'))
            raise ValueError(f"Regenerated production circuit differs from retained setup identity: {family}; {difference}")
    else:
        compare_artifact(output, repo / "formal_verification/lean/artifacts/setup" / (family + ".json"))
    # Recheck all pinned inputs after the native process as well.
    preflight(repo, work, requalify)
    receipt = {"mode": mode, "family": family, "command": command, "ci_absent": True,
               "cargo_build_jobs": 1, "test": test, "executed_tests": 1 if test else None,
               "output_sha256": retained.sha256(output), "log_sha256": retained.sha256(log),
               "manifest_sha256": retained.sha256(manifest_path(repo)),
               "requalification_sha256": retained.sha256(work / "requalification.json") if requalify else None}
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"PASS {mode} {family}; compared full {'circuit' if mode == 'regenerate' else 'setup JSON'}")


def verify(work, repo, dep_info, requalify=False, promote=False):
    if promote and not requalify:
        raise ValueError("Source receipt promotion requires explicit requalification")
    work = Path(work).resolve()
    manifest = preflight(repo, work, requalify)
    artifacts = repo / "formal_verification/lean/artifacts/setup"
    compare_directory(work / "artifacts", artifacts)
    manifest_sha = retained.sha256(artifacts / "manifest.json")
    for mode, families in (("regenerate", GENERATORS), ("export", FAMILIES)):
        for family in families:
            record = retained.read_json(work / "receipts" / f"{mode}-{family}.json")
            if (record["mode"] != mode or record["family"] != family or
                    record["ci_absent"] is not True or record["cargo_build_jobs"] != 1 or
                    record["manifest_sha256"] != manifest_sha or
                    record.get("requalification_sha256") != (
                        retained.sha256(work / "requalification.json") if requalify else None)):
                raise ValueError(f"Invalid or stale native job receipt: {mode} {family}")
            log = work / "logs" / f"{mode}-{family}.log"
            if record["log_sha256"] != retained.sha256(log):
                raise ValueError(f"Changed native job log: {mode} {family}")
            if mode == "regenerate" or family == "decoder-smoke":
                test = generator_test(family) if mode == "regenerate" else retained.SMOKE_TEST
                if record["test"] != test or record["executed_tests"] != 1:
                    raise ValueError(f"Missing exact native test execution: {mode} {family}")
                validate_test_output(log.read_text(), test)
                command = test_command("cs" if mode == "regenerate" else "prover", test)
                if record["command"] != command:
                    raise ValueError(f"Wrong native test command receipt: {mode} {family}")
            if mode == "regenerate":
                output = repo / retained.read_json(artifacts / "manifest.json")["circuit_identities"][family + ".json"]["retained_path"]
            else:
                output = work / "artifacts" / (family + ".json")
                if family != "decoder-smoke":
                    program = work / "program.bin"
                    args = [str(program), str(program)] if family in PROGRAM_FAMILIES else ["-", "-"]
                    command = ["cargo", "run", "--locked", "-p", "execution_prover", "--example",
                               "export_setup_json", "--", family, *args, str(output)]
                    if record["command"] != command:
                        raise ValueError(f"Wrong native export command receipt: {family}")
            if record["output_sha256"] != retained.sha256(output):
                raise ValueError(f"Changed native job output: {mode} {family}")
    if not dep_info:
        raise ValueError("Full freshness verification requires --dep-info from the scoped native build (repeat for dependencies)")
    required = ("cs/src/lib.rs", "prover/src/lib.rs", "execution_prover/src/lib.rs",
                "execution_prover/examples/export_setup_json.rs")
    covered = retained.check_dep_info(repo, manifest, dep_info, required)
    # Recheck the complete source snapshot after the comparisons and dep-info.
    preflight(repo, work, requalify)
    if requalify:
        qualified = work / "qualified-manifest.json"
        with qualified.open("x") as stream:
            stream.write(json.dumps(manifest, indent=2) + "\n")
        report = {"schema_version": 1, "status": "qualified",
                  "retained_manifest_sha256": manifest_sha,
                  "requalification_sha256": retained.sha256(work / "requalification.json"),
                  "qualified_manifest_sha256": retained.sha256(qualified),
                  "native_jobs": 28, "complete_setup_comparisons": 16,
                  "receipts_sha256": {path.name: retained.sha256(path) for path in sorted((work / "receipts").glob("*.json"))},
                  "dep_info_sha256": {str(path): retained.sha256(path) for path in dep_info}}
        (work / "qualified-receipt.json").write_text(json.dumps(report, indent=2) + "\n")
        if promote:
            # Promotion is reachable only after all 28 execution receipts, full
            # payload comparisons, input rechecks and native dep-info pass.
            destination = manifest_path(repo)
            with tempfile.NamedTemporaryFile(dir=destination.parent, prefix=".requalified-", delete=False) as stream:
                stream.write(qualified.read_bytes())
                temporary = Path(stream.name)
            try:
                os.replace(temporary, destination)
            finally:
                temporary.unlink(missing_ok=True)
            retained.check(repo)
            print("Promoted verified source receipts; setup payload bytes unchanged")
    print(f"PASS 12 executed native generators, 16 complete fresh setups, 15 production/1 derived identities; {covered} native dep-info inputs covered")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=REPO)
    sub = parser.add_subparsers(dest="mode", required=True)
    plan = sub.add_parser("plan", help="Print the exact serial job inventory; does not run native tools")
    plan.add_argument("--work-dir", type=Path, required=True)
    item = sub.add_parser("prepare-requalification", help="Snapshot unqualified current source pins; never update retained pins")
    item.add_argument("--work-dir", type=Path, required=True)
    for mode in ("regenerate", "export"):
        item = sub.add_parser(mode, help="Run one native job inside the external bounded worker")
        item.add_argument("family", choices=tuple(GENERATORS) if mode == "regenerate" else FAMILIES)
        item.add_argument("--work-dir", type=Path, required=True)
        item.add_argument("--requalify", action="store_true", help="Use the explicit unqualified source snapshot")
    item = sub.add_parser("compare", help="Compare all sixteen complete fresh JSONs only; not execution evidence")
    item.add_argument("--fresh-dir", type=Path, required=True)
    item = sub.add_parser("verify", help="Verify all native execution receipts, outputs and dep-info coverage")
    item.add_argument("--work-dir", type=Path, required=True)
    item.add_argument("--dep-info", type=Path, action="append", required=True)
    item.add_argument("--requalify", action="store_true", help="Verify the explicit source requalification snapshot")
    item.add_argument("--promote", action="store_true", help="Promote source pins only after successful full native verification")
    args = parser.parse_args()
    repo = args.repo.resolve()
    if args.mode == "plan":
        script = str(repo / "formal_verification/lean/scripts/check_setup_freshness.py")
        for mode, families in (("regenerate", GENERATORS), ("export", FAMILIES)):
            for family in families:
                print(json.dumps([sys.executable, script, "--repo", str(repo), mode, family, "--work-dir", str(args.work_dir)]))
    elif args.mode == "prepare-requalification":
        prepare_requalification(repo, args.work_dir)
    elif args.mode in ("regenerate", "export"):
        job(args.mode, args.family, repo, args.work_dir, args.requalify)
    elif args.mode == "compare":
        preflight(repo)
        print(f"PASS {compare_directory(args.fresh_dir, repo / 'formal_verification/lean/artifacts/setup')} complete fresh JSON comparisons (comparison only)")
    else:
        verify(args.work_dir, repo, args.dep_info, args.requalify, args.promote)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise SystemExit(f"FAIL {error}") from error
