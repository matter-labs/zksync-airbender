"""Run selected Lean modules with the normal guarded frontend, without claiming FV."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ASSURANCE_FLAGS = (
    "FV_COLD_BUILD", "FV_FULL_ASSURANCE", "FV_REFRESH_AXIOM_BASELINE",
    "FV_REQUALIFY_SETUPS",
)
OMITTED = (
    "fresh native generators and setup exports", "fresh compiler captures",
    "complete source/runtime verification", "generated-source and decoder checks",
    "environment/axiom audit", "independent kernel replay and false-proof controls",
)


def requested_modules(environ):
    modules = environ.get("FV_DIAGNOSE_MODULES", "").split()
    if not modules:
        return ()
    if any(environ.get(flag) == "true" for flag in ASSURANCE_FLAGS):
        raise ValueError("Lean diagnosis cannot be combined with assurance, cold-build, baseline or requalification flags")
    if len(modules) > 16 or len(set(modules)) != len(modules):
        raise ValueError("Request 1–16 distinct Lean modules")
    for module in modules:
        if not re.fullmatch(r"(?:Tests|Airbender)(?:\.[A-Za-z_][A-Za-z0-9_]*)+", module):
            raise ValueError(f"Invalid project module: {module!r}")
        if not ROOT.joinpath(*module.split(".")).with_suffix(".lean").is_file():
            raise ValueError(f"Missing project module: {module}")
    return tuple(modules)


def command(modules, output):
    return ["python3", "scripts/check_lean.py", "--guard", "scripts/bounded_fv.py",
            "--workers", "1", "--output", str(output),
            *[arg for module in modules for arg in ("--module", module)]]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate-only", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        modules = requested_modules(os.environ)
    except ValueError as error:
        parser.error(str(error))
    if not modules:
        if args.validate_only:
            return
        parser.error("Lean diagnosis requires explicit project modules")
    report = {"scope": "selected_modules_only_not_fv_assurance", "modules": modules,
              "omitted": OMITTED, "cache_upload": False}
    print(json.dumps(report, indent=2), flush=True)
    if args.validate_only:
        return
    if args.output is None:
        parser.error("--output is required")
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "scope.json").write_text(json.dumps(report, indent=2) + "\n")
    subprocess.run(command(modules, args.output), cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
