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
import re
import shutil
import subprocess
import tempfile

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


def extract_base_pc(model):
    """Copy the unique nextPC assignment in upstream's normal F_Base branch.

    This is an unchecked extraction boundary, not a replacement PC formula.
    The pinned source, expression and location are retained for review.
    """
    path = model / "model/postlude/step.sail"
    source = path.read_text()
    start = source.index("private function run_hart_active(")
    end = source.index("\nprivate function wait_is_nop", start)
    branch = source.index("F_Base(w) => {", start, end)
    matches = list(re.finditer(r"^[ \t]*(nextPC[ \t]*=[^;\n]+;)[ \t]*$",
                              source[branch:end], re.MULTILINE))
    if len(matches) != 1:
        raise ValueError("Expected exactly one F_Base nextPC assignment")
    statement = matches[0].group(1)
    line = source[:branch + matches[0].start(1)].count("\n") + 1
    helper = ("// Extracted verbatim from the pinned normal F_Base path.\n"
              "val normal_base_next_pc : unit -> unit\n"
              "function normal_base_next_pc() = {\n  " + statement + "\n  ()\n}\n")
    return helper, {"source": "model/postlude/step.sail", "sha256": digest(path),
                    "function": "run_hart_active", "branch": "normal F_Base",
                    "line": line, "statement": statement}


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
    helper, extraction = extract_base_pc(model)
    (output / "extracted_base_pc.sail").write_text(helper)
    # Project files resolve relative sources beside the original project. Keep
    # this temporary wrapper there and remove it even if Sail fails.
    with tempfile.NamedTemporaryFile(mode="w", suffix=".sail_project",
                                     prefix=".airbender-pc-", dir=model / "model",
                                     delete=False) as project:
        project.write((model / "model/riscv.sail_project").read_text())
        helper_path = os.path.relpath(output / "extracted_base_pc.sail", model / "model")
        project.write("\nairbender_pc_slice {\n  requires prelude, core, I_insts, M_insts\n  files " +
                      json.dumps(helper_path) + "\n}\n")
        project_path = Path(project.name)
    try:
        command([
            compiler / "_build/default/src/bin/sail.exe",
            "-plugin", compiler / "_build/default/src/sail_lean_backend/sail_plugin_lean.cmxs",
            "-plugin", compiler / "_build/default/src/airbender_slice/sail_slice.cmxs",
            "--lean-slice", "--strict-var", "--strict-bitvector", "--strict-exponentials",
            "--require-version", "0.20.3", "--memo-z3", "--memo-z3-path", smt_cache,
            "--config", config, "--lean-single-file", "--lean-output-dir", output,
            "--lean-non-beq-type", "instruction", "--lean-non-beq-type", "ExecutionResult",
            "--lean-lib-rev", RUNTIME_REV, "-o", "SailRV32",
            "--project", project_path, "airbender_pc_slice",
        ], cwd=model / "model", env=env)
    finally:
        project_path.unlink()
    generated = output / "SailRV32"
    manifest = {
        "model_repository": "https://github.com/riscv/sail-riscv",
        "model_revision": MODEL_REV,
        "compiler_repository": "https://github.com/rems-project/sail",
        "compiler_revision": COMPILER_REV,
        "runtime_revision": RUNTIME_REV,
        "xlen": 32,
        "module": "airbender_pc_slice (requires I_insts, M_insts)",
        "roots": ["execute_RTYPE", "execute_ITYPE", "execute_UTYPE", "execute_MUL", "execute_DIV", "execute_REM",
                  "get_arch_pc", "get_next_pc", "tick_pc", "normal_base_next_pc"],
        "extractions": [extraction],
        "extracted_source_sha256": digest(output / "extracted_base_pc.sail"),
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
