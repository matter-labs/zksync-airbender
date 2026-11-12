#!/usr/bin/env python3
"""Check public Review theorem audit coverage and the review guide's references."""

from pathlib import Path
from collections import deque
import re
import subprocess
import tempfile
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parent
GUIDES = tuple(ROOT.parent / name for name in (
    "README.md", "docs/VERIFICATION_STATUS.md", "docs/TRUST_AND_REVIEW.md",
    "docs/FORMAL_VERIFICATION_PLAN.md",
)) + tuple(sorted((ROOT / "human/Human").rglob("README.md")))
# The claim modules: the specification (human/) and the proofs of its public theorems (proven/Proven/Final/).
CLAIM_PREFIXES = ("Human.", "Proven.Final.")


def module_path(module):
    """Source file of a module, by its library's srcDir."""
    src = {"Human": "human", "Proven": "proven", "Tests": "test", "Checks": "test"}[module.split(".")[0]]
    return ROOT.joinpath(src, *module.split(".")).with_suffix(".lean")


def claim_modules():
    return [".".join(path.relative_to(ROOT / src).with_suffix("").parts)
            for src, sub in (("human", "Human"), ("proven", "Proven/Final"))
            for path in sorted((ROOT / src / sub).rglob("*.lean"))]
# File names, source-only Rust/Sail names, and prose are not emitted Lean declarations.
SOURCE_NAMES = {
    "Model.lean", "lakefile.toml", "av_gkr_compiler",
    "inits_or_teardowns_as_flattened_relation", "mask_read_for_witness",
    "run_hart_active", "F_Base", "FormalCircuit", "sorry",
    "PROVENANCE.txt", "regen.sh", "sail_rv32", "Zalrsc",
    # the build budget (README): script, environment variables, Lake's input hash, OS tools
    "verify.sh", "MODULE_BUDGET_JOBS", "MODULE_BUDGET_LEDGER", "MODULE_BUDGET_S", "depHash", "ps", "wait4",
    "CALIBRATION_REFERENCE_S",
    # CI (docs/TRUST_AND_REVIEW.md, What CI re-checks): verify.sh's audit modes, the kernel checker
    "VERIFY_AUDITS", "fresh", "replay", "leanchecker", "kernel_replay", "native_decide",
    # Lean 4.35: lake check's sandbox tool, lean-sail's codegen wrapper command (sail/README.md)
    "bwrap", "skip_inductive_codegen", "ci.yml", "mop.r.N", "mop.rr.N",
    # the no-warnings gate (README): Lake library names and Lake's option for non-module files
    "Proven", "CleanAudit", "allowNonModules",
}


def guide_names():
    names = set()
    for path in GUIDES:
        text = re.sub(r"```.*?```", "", path.read_text(), flags=re.S)
        names.update(name for name in re.findall(r"`([^`\n]+)`", text)
                     if re.fullmatch(r"[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*", name)
                     and name not in SOURCE_NAMES
                     and not re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})", name))
    return names


def check_links():
    count = 0
    for guide in GUIDES:
        for target in re.findall(r"\[[^]\n]*\]\(([^)\n]+)\)", guide.read_text()):
            link = urlsplit(target.strip("<>"))
            if link.scheme:
                continue
            path = (guide.parent / unquote(link.path)).resolve() if link.path else guide
            if not path.is_file():
                raise ValueError(f"{guide.name}: missing link target {target}")
            if link.fragment:
                anchors = set()
                for heading in re.findall(r"^#+\s+(.+)$", path.read_text(), re.M):
                    slug = re.sub(r"[^\w\s-]", "", heading.strip().lower()).replace(" ", "-")
                    base, suffix = slug, 0
                    while slug in anchors:
                        suffix += 1
                        slug = f"{base}-{suffix}"
                    anchors.add(slug)
                if unquote(link.fragment) not in anchors:
                    raise ValueError(f"{guide.name}: missing heading {target}")
            count += 1
    return count


def inventory(modules, references):
    """Run Lean on the claim modules: `DOC_DECL ref` for each guide name that resolves to a public declaration (the
    name itself or a dotted suffix of one), `REVIEW_THEOREM` for each public theorem of a claim module. Only the claim
    modules' own declarations are visited for theorems, and only names not found exactly are matched against every
    declaration (visiting all ~540k imported declarations for theorems cost ~25 s)."""
    imports = ["Checks.Axioms", *modules, "Lean"]
    names = ", ".join('"' + name + '"' for name in sorted(references))
    code = "\n".join("import " + module for module in imports) + f'''
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut refs : Std.HashMap String (List String) := {{}}
  for ref in ([{names}] : List String) do
    let name := ref.toName
    if env.contains name && !isPrivateName name && name.toString == ref then
      logInfo m!"DOC_DECL {{ref}}"
    else
      let last := (ref.splitOn ".").getLast!
      refs := refs.insert last (ref :: refs[last]?.getD [])
  if !refs.isEmpty then
    for (name, _) in env.constants.toList do
      if !isPrivateName name then
        if let .str _ last := name then
          for ref in refs[last]?.getD [] do
            if name.toString == ref || name.toString.endsWith ("." ++ ref) then
              logInfo m!"DOC_DECL {{ref}}"
  for h : idx in [0:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[idx]
    if mod.toString.startsWith "Human." || mod.toString.startsWith "Proven.Final." then
      for name in env.header.moduleData[idx]!.constNames do
        if !isPrivateName name then
          if let some (.thmInfo _) := env.find? name then
            if let some ranges ← findDeclarationRanges? name then
              let start := ranges.range.pos
              let finish := ranges.selectionRange.endPos
              logInfo m!"REVIEW_THEOREM {{mod}} {{name}} {{start.line}} {{start.column}} {{finish.line}} {{finish.column}}"
'''
    with tempfile.TemporaryDirectory(prefix="airbender-review-") as directory:
        path = Path(directory) / "Inventory.lean"
        path.write_text(code)
        result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise ValueError(result.stdout[-4000:])
    return result.stdout


def check_theorems(output, audit):
    declarations = set()
    pattern = r"^REVIEW_THEOREM (\S+) (\S+) (\d+) (\d+) (\d+) (\d+)$"
    for module, name, first, start, last, finish in re.findall(pattern, output, re.M):
        path = module_path(module)
        lines = path.read_text().splitlines()[int(first) - 1:int(last)]
        lines[-1] = lines[-1][:int(finish)]
        lines[0] = lines[0][int(start):]
        header = re.sub(r"/-.*?-/|--[^\n]*", "", "\n".join(lines), flags=re.S)
        declared = re.search(r"\b(?:theorem|lemma)\s+([\w'.]+)\s*$", header)
        if declared and name.endswith("." + declared[1]):
            declarations.add(name)
    if not declarations:
        raise ValueError("No source-declared public Review theorems found")
    roots = re.findall(r"^#print axioms (\S+)\s*$", audit.read_text(), re.M)
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate axiom audit roots")
    missing = declarations - set(roots)
    if missing:
        raise ValueError("Missing public theorem audit roots:\n" + "\n".join(sorted(missing)))
    return len(declarations)


def check_layers():
    from scripts.check_import_closure import load_graph
    roots = [".".join(path.relative_to(ROOT / src).with_suffix("").parts)
             for src in ("human", "proven") for path in (ROOT / src).rglob("*.lean")]
    graph = load_graph(roots)
    for module, dependencies in graph.items():
        for dependency in dependencies:
            if dependency.startswith(CLAIM_PREFIXES) and dependency not in graph:
                raise ValueError(f"Missing review module: {module} → {dependency}")
        if not module.startswith(tuple(p + s for p in CLAIM_PREFIXES for s in ("Helpers.", "Circuits."))):
            continue
        pending, seen = deque([[module]]), set()
        while pending:
            path = pending.popleft()
            current = path[-1]
            if current in seen:
                continue
            seen.add(current)
            if current.startswith(tuple(p + "Trace." for p in CLAIM_PREFIXES)):
                raise ValueError("Whole-execution dependency in circuit context: " + " → ".join(path))
            pending.extend(path + [dependency] for dependency in graph.get(current, []))


def inputs_key(modules):
    """Everything the Lean part of the check reads: this script, the guides, the audit file, and Lake's input hash of
    every module it imports (which covers their sources and all their imports)."""
    import hashlib
    import json
    h = hashlib.sha256()
    for path in (Path(__file__), *GUIDES, ROOT / "test/Checks/Axioms.lean"):
        h.update(str(path.relative_to(ROOT.parent)).encode() + b"\0" + path.read_bytes() + b"\0")
    for module in ["Checks.Axioms", *modules]:
        trace = ROOT.joinpath(".lake/build/lib/lean", *module.split(".")).with_suffix(".trace")
        h.update(module.encode() + b"\0" + json.loads(trace.read_text())["depHash"].encode() + b"\0")
    return h.hexdigest()


def main():
    import sys
    # --key FILE: record the inputs of a passing run; --reuse: skip the Lean part when FILE records these inputs;
    # --built: do not build the claim modules first
    key_file = Path(sys.argv[sys.argv.index("--key") + 1]) if "--key" in sys.argv else None
    reuse = "--reuse" in sys.argv
    modules = claim_modules()
    # Build first so the compiler inventory describes the current source tree (--built: the caller just built them,
    # as verify.sh does; a second `lake build` would only re-check the whole build graph).
    if "--built" not in sys.argv:
        subprocess.run(["lake", "build", "Checks.Axioms", *modules], cwd=ROOT, check=True)
    references = guide_names()
    key = inputs_key(modules) if key_file else None
    if reuse and key_file and key_file.exists() and key_file.read_text().strip() == key:
        print(f"PASS claim theorem audit roots and {len(references)} guide declaration names: inputs unchanged since "
              f"the passing check recorded in {key_file.name}")
    else:
        output = inventory(modules, references)
        missing = references - set(re.findall(r"^DOC_DECL (\S+)$", output, re.M))
        if missing:
            raise ValueError("Unresolved guide declarations: " + ", ".join(sorted(missing)))
        count = check_theorems(output, ROOT / "test/Checks/Axioms.lean")
        print(f"PASS {count} public claim theorems have explicit axiom audit roots")
        print(f"PASS {len(references)} guide declaration names resolve in Lean")
        if key_file:
            key_file.write_text(key + "\n")
    print(f"PASS {check_links()} local guide links and heading anchors resolve")
    check_layers()
    print("PASS context/trace separation")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, subprocess.CalledProcessError) as error:
        raise SystemExit(f"FAIL {error}") from error
