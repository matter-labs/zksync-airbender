#!/usr/bin/env python3
"""Serial, cached verification with the shared macOS process-tree watchdog."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT / ".lake/build/lib/lean"
STATE = ROOT / ".lake/bounded-check-state.json"
LOGS = ROOT / ".lake/bounded-logs"
LEAN = ["lake", "env", "lean", "-j1", "-M3072"]

def bounded(command, label, seconds=300):
    LOGS.mkdir(parents=True, exist_ok=True)
    log = LOGS / (label + ".log")
    result = subprocess.run([sys.executable, str(ROOT / "scripts/bounded_fv.py"),
        "--mib", "3072", "--resident-mib", "4096", "--seconds", str(seconds),
        "--log", str(log), "--", *command], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    try:
        report = json.loads(result.stdout.strip())
    except ValueError:
        raise RuntimeError(result.stdout[-3000:]) from None
    print(f"{label}: {report['reason']}; footprint={report['footprint_peak_mib']} MiB; "
          f"resident={report['resident_peak_mib']} MiB; {report['seconds']}s", flush=True)
    if result.returncode or report["live_owned_after"]:
        print(log.read_text()[-5000:], file=sys.stderr)
        raise RuntimeError(f"bounded check failed: {label}; see {log}")
    return log.read_text()

def project_modules():
    modules = {}
    for directory in (ROOT / "Airbender", ROOT / "Tests"):
        for path in directory.rglob("*.lean"):
            modules[".".join(path.relative_to(ROOT).with_suffix("").parts)] = path
    modules["Airbender"] = ROOT / "Airbender.lean"
    for path in (ROOT / "generated/sail-rv32").rglob("*.lean"):
        modules[".".join(path.relative_to(ROOT / "generated/sail-rv32").with_suffix("").parts)] = path
    return modules

def build(targets):
    modules = project_modules()
    dependencies = {name: [dep for line in path.read_text().splitlines()
                          if line.startswith("import ") for dep in line.split()[1:]
                          if dep in modules] for name, path in modules.items()}
    ordered, visiting, visited = [], set(), set()
    def visit(name):
        if name in visited:
            return
        if name in visiting:
            raise RuntimeError(f"cyclic project imports: {name}")
        visiting.add(name)
        for dep in dependencies[name]:
            visit(dep)
        visiting.remove(name)
        visited.add(name)
        ordered.append(name)
    for name in targets or sorted(modules):
        if name not in modules:
            raise RuntimeError(f"unknown project module: {name}")
        visit(name)
    stamp = hashlib.sha256((ROOT / "lake-manifest.json").read_bytes() +
        (ROOT / "lean-toolchain").read_bytes() +
        (ROOT / "artifacts/provenance.json").read_bytes()).hexdigest()
    state = json.loads(STATE.read_text()) if STATE.exists() else {}
    hashes = {}
    for name in ordered:
        source = modules[name]
        artifact = BUILD.joinpath(*name.split(".")).with_suffix(".olean")
        fingerprint = hashlib.sha256(stamp.encode() + source.read_bytes() +
            "".join(hashes[dep] for dep in dependencies[name]).encode()).hexdigest()
        hashes[name] = fingerprint
        if state.get(name) == fingerprint and artifact.exists():
            continue
        # A failed compile must not leave an old state entry that can be reused.
        state.pop(name, None)
        STATE.parent.mkdir(parents=True, exist_ok=True)
        STATE.write_text(json.dumps(state, indent=2) + "\n")
        artifact.parent.mkdir(parents=True, exist_ok=True)
        root = ROOT / "generated/sail-rv32" if name.startswith("SailRV32") else ROOT
        output = bounded([*LEAN, "--root=" + str(root), str(source), "-o", str(artifact),
            "-i", str(artifact.with_suffix(".ilean"))], name.replace(".", "-"))
        if re.search(r"(?m)^(?:.*?/)?(?:Airbender|Tests)/.*?\.lean:[0-9]+:[0-9]+: warning:|^warning: (?:Airbender|Tests)/", output):
            raise RuntimeError(f"handwritten diagnostic: {name}; inspect {LOGS}")
        state[name] = fingerprint
        STATE.write_text(json.dumps(state, indent=2) + "\n")

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--build-only", action="store_true")
    parser.add_argument("modules", nargs="*")
    args = parser.parse_args()
    os.chdir(ROOT)
    build(args.modules)
    if args.build_only:
        return
    bounded([sys.executable, "scripts/check_native_setup.py"], "native-setup-export")
    bounded([*LEAN, "--run", "Tests/ArtifactImport.lean"], "importer-tests")
    bounded([*LEAN, "--run", "Tests/ReducedMachineImport.lean"], "reduced-importer-tests")
    bounded([*LEAN, "--run", "Tests/ReducedSignHighImport.lean"], "reduced-sign-high-importer-tests")
    bounded([*LEAN, "--run", "Tests/NativeReducedImport.lean"], "native-reduced-importer-tests")
    bounded([*LEAN, "--run", "Airbender/Import/Main.lean",
        "../../cs/add_sub_lui_auipc_mop_preprocessed_layout.json",
        "../../cs/word_only_load_store_preprocessed_layout.json",
        "../../cs/jump_branch_slt_preprocessed_layout.json",
        "../../cs/mul_div_unsigned_preprocessed_layout.json",
        "../../cs/shift_binop_csrrw_preprocessed_layout.json",
        "../../cs/subword_only_load_store_preprocessed_layout.json",
        "../../cs/reduced_machine_preprocessed_layout.json",
        "artifacts/circuits/reduced-native-layout.json"], "importer-cli")
    bounded([sys.executable, "scripts/check_review.py", "--no-build"], "review-and-axioms")
    print("PASS all serial bounded verification gates", flush=True)

if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, subprocess.CalledProcessError) as error:
        raise SystemExit(f"FAIL {error}") from error
