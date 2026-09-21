#!/usr/bin/env python3
"""Check CUDA-free dependency graphs and execution-backend layering."""

import argparse
import json
import subprocess

CUDA_ANCHORS = {"era_cudart", "era_cudart_sys", "gpu_native_build"}
CUDA_FREE_ROOTS = (
    "execution_prover_model", "execution_prover", "cpu_execution_prover",
    "program_prover", "prover_pipeline", "cli",
)
FORBIDDEN = {
    "execution_prover": {"cpu_execution_prover", "gpu_execution_prover", "full_statement_verifier"},
    "gpu_core": {"execution_prover_model", "setups"},
}


def cargo(*args):
    return subprocess.check_output(["cargo", *args], text=True)


def graph(root, flags=()):
    output = cargo("tree", "-p", root, "-e", "normal,build,dev", "--prefix", "none",
                   "--format", "{p}", *flags)
    packages = {line.split()[0] for line in output.splitlines() if line.strip()}
    assert root in packages, f"missing root {root} in cargo tree"
    return packages


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()
    metadata = json.loads(cargo("metadata", "--no-deps", "--format-version", "1"))
    features = {package["name"]: package["features"] for package in metadata["packages"]}
    checks = 0
    for root in (*CUDA_FREE_ROOTS, "gpu_core"):
        configs = [(), ("--no-default-features",)]
        if "deterministic_pow" in features[root]:
            configs.append(("--no-default-features", "--features", "deterministic_pow"))
        for flags in configs:
            packages = graph(root, flags)
            forbidden = FORBIDDEN.get(root, set())
            if root in CUDA_FREE_ROOTS:
                forbidden = forbidden | CUDA_ANCHORS
            found = packages & forbidden
            assert not found, f"{root} {flags} reaches forbidden packages: {sorted(found)}"
            checks += 1
            if args.verbose:
                print(f"{root} {flags}: {len(packages)} packages")
    # Ensure the detector observes CUDA when that backend is enabled.
    assert graph("cli", ("--features", "gpu")) & CUDA_ANCHORS, "GPU feature did not reach CUDA"
    print(f"dependency guard passed: {checks} configurations and GPU positive control")


if __name__ == "__main__":
    main()
