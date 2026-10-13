#!/usr/bin/env python3
"""Check public Review theorem audit coverage and the review guide's references."""

from pathlib import Path
from collections import deque
import re
import subprocess
import tempfile
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parent.parent
GUIDES = tuple(ROOT / name for name in (
    "README.md", "VERIFICATION_STATUS.md", "TRUST_AND_REVIEW.md",
    "FORMAL_VERIFICATION_PLAN.md",
))
# File names, source-only Rust/Sail names, and prose are not emitted Lean declarations.
SOURCE_NAMES = {
    "Model.lean", "extracted_base_pc.sail", "lakefile.toml", "av_gkr_compiler",
    "inits_or_teardowns_as_flattened_relation", "mask_read_for_witness",
    "run_hart_active", "F_Base", "FormalCircuit", "sorry",
}


def guide_names():
    names = set()
    for path in GUIDES:
        text = re.sub(r"```.*?```", "", path.read_text(), flags=re.S)
        names.update(name for name in re.findall(r"`([^`\n]+)`", text)
                     if re.fullmatch(r"[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*", name)
                     and name not in SOURCE_NAMES
                     and not re.fullmatch(r"[0-9a-f]{40}", name))
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
    imports = ["Airbender.Checks.Axioms", *modules, "Lean"]
    names = ", ".join('"' + name + '"' for name in sorted(references))
    code = "\n".join("import " + module for module in imports) + f'''
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut refs : Std.HashMap String (List String) := {{}}
  for ref in ([{names}] : List String) do
    let last := (ref.splitOn ".").getLast!
    refs := refs.insert last (ref :: refs[last]?.getD [])
  for (name, info) in env.constants.toList do
    if !isPrivateName name then
      if let .str _ last := name then
        for ref in refs[last]?.getD [] do
          if name.toString == ref || name.toString.endsWith ("." ++ ref) then
            logInfo m!"DOC_DECL {{ref}}"
      if let .thmInfo _ := info then
        if let some idx := env.getModuleIdxFor? name then
          let mod := env.header.moduleNames[idx]!
          if mod.toString.startsWith "Airbender.Review." then
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
        path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
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
    graph = {".".join(path.relative_to(ROOT).with_suffix("").parts):
             re.findall(r"^import (\S+)$", path.read_text(), re.M)
             for path in (ROOT / "Airbender").rglob("*.lean")}
    if (ROOT / "Airbender.lean").is_file():
        graph["Airbender"] = re.findall(r"^import (\S+)$", (ROOT / "Airbender.lean").read_text(), re.M)
    # These existing proof assemblies reuse pooled retirement lemmas. Their
    # circuit models and statements do not require a whole-execution contract.
    assemblies = {f"Airbender.Review.Circuits.{family}.Theorems"
                  for family in ("JumpBranchSlt", "MulDiv", "ShiftBinop")}
    coupled = set()
    for module, dependencies in graph.items():
        for dependency in dependencies:
            if dependency.startswith("Airbender.Review.") and dependency not in graph:
                raise ValueError(f"Missing review module: {module} → {dependency}")
        if not module.startswith(("Airbender.Review.Helpers.", "Airbender.Review.Circuits.")):
            continue
        pending, seen = deque([[module]]), set()
        while pending:
            path = pending.popleft()
            current = path[-1]
            if current in seen:
                continue
            seen.add(current)
            if current.startswith("Airbender.Review.Trace."):
                if module in assemblies and path[1].startswith("Airbender.Proofs."):
                    coupled.add(module)
                    break
                raise ValueError("Whole-execution dependency in circuit context: " + " → ".join(path))
            pending.extend(path + [dependency] for dependency in graph.get(current, []))
    return len(coupled)


def main():
    modules = [".".join(path.relative_to(ROOT).with_suffix("").parts)
               for path in sorted((ROOT / "Airbender/Review").rglob("*.lean"))]
    # Build first so the compiler inventory describes the current source tree.
    subprocess.run(["lake", "build", "Airbender.Checks.Axioms", *modules], cwd=ROOT, check=True)
    references = guide_names()
    output = inventory(modules, references)
    missing = references - set(re.findall(r"^DOC_DECL (\S+)$", output, re.M))
    if missing:
        raise ValueError("Unresolved guide declarations: " + ", ".join(sorted(missing)))
    count = check_theorems(output, ROOT / "Airbender/Checks/Axioms.lean")
    print(f"PASS {count} public Review theorems have explicit axiom audit roots")
    print(f"PASS {len(references)} guide declaration names resolve in Lean")
    print(f"PASS {check_links()} local guide links and heading anchors resolve")
    print(f"PASS context/trace separation; {check_layers()} documented proof-assembly dependencies")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, subprocess.CalledProcessError) as error:
        raise SystemExit(f"FAIL {error}") from error
