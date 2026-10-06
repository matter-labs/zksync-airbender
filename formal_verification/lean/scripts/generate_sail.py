#!/usr/bin/env python3
"""Generate the pinned upstream RV32 execution slice, without an ISA rewrite.

Requires the compiler's OCaml build dependencies, Dune, and Z3 in PATH.
The generated Lean snapshot is built using this project's pinned Lean runtime.
"""
import argparse
import hashlib
import json
from pathlib import Path
import os
import shutil
import subprocess

MODEL_REV = "bf32036e9aea614298e3ccf32d7a33d71ddc7c1b"
COMPILER_REV = "3df54034910b31a1e00d948ee965b2e9603d68e0"
RUNTIME_REV = "c816ea7ad03cce98d51acee252540fd4215fede8"
ROOT = Path(__file__).resolve().parents[1]


def command(args, cwd=None, env=None):
    subprocess.run([str(a) for a in args], cwd=cwd, env=env, check=True)


def check_revision(path, revision):
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=path, text=True).strip()
    if actual != revision:
        raise ValueError(f"{path}: expected {revision}, found {actual}")
    command(["git", "diff", "--quiet", "HEAD", "--"], cwd=path)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler-source", required=True, type=Path)
    parser.add_argument("--model-source", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path,
                        help="Fresh output directory; the checked-in snapshot is never overwritten")
    parser.add_argument("--smt-cache", type=Path, help="Optional reusable Sail solver cache")
    args = parser.parse_args()
    compiler = args.compiler_source.resolve()
    model = args.model_source.resolve()
    output = args.output.resolve()
    if output.exists():
        raise ValueError("Choose a fresh output directory")
    check_revision(compiler, COMPILER_REV)
    check_revision(model, MODEL_REV)
    plugin_dir = compiler / "src/airbender_slice"
    plugin_dir.mkdir(exist_ok=True)
    plugin_source = ROOT / "scripts/sail_slice.ml"
    target_source = plugin_dir / "sail_slice.ml"
    if target_source.exists() and target_source.read_bytes() != plugin_source.read_bytes():
        raise ValueError("Existing slice adapter differs; use a clean compiler checkout")
    shutil.copyfile(plugin_source, target_source)
    (plugin_dir / "dune").write_text(
        "(executable (name sail_slice) (modes (native plugin)) (libraries libsail))\n")
    command(["dune", "build", "--release", "src/bin/sail.exe",
             "src/sail_lean_backend/sail_plugin_lean.cmxs",
             "src/airbender_slice/sail_slice.cmxs"], cwd=compiler)
    config = ROOT / "generated/sail-rv32/rv32d_v256_e32.json"
    output.mkdir(parents=True)
    smt_cache = args.smt_cache.resolve() if args.smt_cache else output / "smt-cache"
    env = dict(os.environ, SAIL_DIR=str(compiler))
    command([
            compiler / "_build/default/src/bin/sail.exe",
            "-plugin", compiler / "_build/default/src/sail_lean_backend/sail_plugin_lean.cmxs",
            "-plugin", compiler / "_build/default/src/airbender_slice/sail_slice.cmxs",
            "--lean-slice", "--strict-var", "--strict-bitvector", "--strict-exponentials",
            "--require-version", "0.20.3", "--memo-z3", "--memo-z3-path", smt_cache,
            "--config", config, "--lean-single-file", "--lean-output-dir", output,
            "--lean-non-beq-type", "instruction", "--lean-non-beq-type", "ExecutionResult",
            "--lean-lib-rev", RUNTIME_REV, "-o", "SailRV32",
            "--project", "riscv.sail_project", "I_insts",
        ], cwd=model / "model", env=env)
    generated = output / "SailRV32"
    manifest = {
        "model_repository": "https://github.com/riscv/sail-riscv",
        "model_revision": MODEL_REV,
        "compiler_repository": "https://github.com/rems-project/sail",
        "compiler_revision": COMPILER_REV,
        "runtime_revision": RUNTIME_REV,
        "xlen": 32,
        "module": "I_insts",
        "roots": ["execute_RTYPE", "execute_ITYPE"],
        "config_sha256": digest(config),
        "adapter_sha256": digest(plugin_source),
        "generated_sha256": {
            str(p.relative_to(generated)): digest(p)
            for p in sorted(generated.rglob("*.lean"))
        },
    }
    (output / "provenance.json").write_text(json.dumps(manifest, indent=2) + "\n")


if __name__ == "__main__":
    main()
