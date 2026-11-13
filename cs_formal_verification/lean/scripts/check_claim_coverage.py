#!/usr/bin/env python3
"""Require a final proof and a separate proved witness for every public claim."""
from pathlib import Path
import argparse
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "claim_coverage.json"
SPECIAL_MODULES = {
    "Human.Compiler.NativeTargets", "Human.Trace.Machine.Theorems",
    "Human.Trace.Machine.Padding", "Human.ISA.DelegationRuns",
}


def inventory():
    modules = [".".join(p.relative_to(ROOT / folder).with_suffix("").parts)
               for folder, prefix in [("human", "Human"), ("proven", "Proven/Final")]
               for p in sorted((ROOT / folder / prefix).rglob("*.lean"))]
    code = "\n".join("import " + m for m in modules) + '''
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for h : index in [0:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[index]
    if mod.toString.startsWith "Human." || mod.toString.startsWith "Proven.Final." then
      for name in env.header.moduleData[index]!.constNames do
        if !isPrivateName name then
          match env.find? name with
          | some (.defnInfo info) =>
            if mod.toString.startsWith "Human." && info.type.consumeMData == .sort .zero then
              let value := info.value.consumeMData
              let head := if value.isForall then "forall" else
                if value.isAppOfArity ``Exists 2 then "exists" else "constant"
              let combined := if value.isAppOfArity ``And 2 then
                (value.getAppArgs[1]!).consumeMData.isAppOfArity ``Exists 2 else false
              logInfo m!"HUMAN_PROP {name} {mod} {head} {combined}"
          | some (.thmInfo info) =>
            if mod.toString.startsWith "Proven.Final." then
              logInfo m!"FINAL_DECL {name} {mod}"
              if let .const claim _ := info.type.consumeMData then
                logInfo m!"FINAL_PROOF {name} {claim}"
          | _ => pure ()
'''
    # Recheck the ordinary theorem forms against their named Human statements.
    # These assertions also cover generic final theorems whose type unfolds the claim.
    for claim, proof in re.findall(r"^example : ([\w.]+) := @?([\w.]+)\s*$",
                                   (ROOT / "test/Checks/Claims.lean").read_text(), re.M):
        code += f"\nexample : {claim} := @{proof}\n"
        code += f'run_cmd logInfo "TYPED_PROOF {proof} {claim}"\n'
    with tempfile.TemporaryDirectory(prefix="airbender-claims-") as directory:
        path = Path(directory) / "Inventory.lean"
        path.write_text(code)
        result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise ValueError(result.stdout[-5000:])
    props, proofs, declarations, proof_modules = {}, {}, set(), {}
    for line in result.stdout.splitlines():
        fields = line.split()
        if fields and fields[0] == "HUMAN_PROP":
            _, name, module, head, combined = fields
            props[name] = {"module": module, "head": head, "combined": combined == "true"}
        elif fields and fields[0] == "FINAL_DECL":
            _, proof, module = fields
            declarations.add(proof)
            proof_modules[proof] = module
        elif fields and fields[0] in {"FINAL_PROOF", "TYPED_PROOF"}:
            _, proof, claim = fields
            if proof in declarations:
                proofs.setdefault(claim, []).append(proof)
    claims = {name: info for name, info in props.items()
              if name.endswith("Claim") or info["module"] in SPECIAL_MODULES or name in proofs}
    return {"claims": claims, "proofs": {k: sorted(set(v)) for k, v in proofs.items() if k in claims},
            "proof_modules": proof_modules}


def allowed_exception(name, info, kind):
    module = info["module"]
    if kind == "import":
        return module.startswith("Human.Import.")
    if kind == "artifact":
        return (name.endswith(("ImportClaim", "BytesClaim", "BindingClaim", "DescriptionClaim"))
                and (".Artifact" in module or module.endswith("UnifiedArtifact") or ".Native." in module or ".Captures." in module))
    if kind == "constant":
        return info["head"] == "constant" and module.startswith(("Human.ISA.", "Human.Import."))
    return False


def validate(data, manifest):
    claims, proofs = data["claims"], data["proofs"]
    rows = manifest["claims"]
    if set(rows) != set(claims):
        missing = sorted(set(claims) - set(rows))
        stale = sorted(set(rows) - set(claims))
        raise ValueError(f"Claim inventory mismatch. Missing: {missing}. Stale: {stale}")
    for name, info in claims.items():
        row = rows[name]
        if not proofs.get(name):
            raise ValueError("Missing final proof: " + name)
        if info["combined"]:
            raise ValueError("Soundness and non-vacuity are joined: " + name)
        if "Satisfiable" in name:
            if info["head"] != "exists":
                raise ValueError("Witness statement must expose its existential: " + name)
            continue
        if "exception" in row:
            if not row.get("reason") or not allowed_exception(name, info, row["exception"]):
                raise ValueError("Invalid non-vacuity exception: " + name)
            continue
        witness = row.get("witness")
        if witness not in claims or "Satisfiable" not in witness:
            raise ValueError("Missing separate non-vacuity statement: " + name)
        if not proofs.get(witness):
            raise ValueError("Missing non-vacuity proof: " + witness)
    return len(claims)


def initialize(data):
    claims = data["claims"]
    rows = {}
    for name, info in claims.items():
        if "Satisfiable" in name:
            rows[name] = {}
            continue
        stem = name.removesuffix("Claim")
        candidates = [stem + "SatisfiableClaim", stem.replace("Soundness", "") + "SatisfiableClaim"]
        witness = next((x for x in candidates if x in claims), None)
        if witness:
            rows[name] = {"witness": witness}
            continue
        exception = next((x for x in ["import", "artifact", "constant"] if allowed_exception(name, info, x)), None)
        rows[name] = ({"exception": exception, "reason": "This claim checks fixed imported data or a constant proposition."}
                      if exception else {"witness": "TODO"})
    return {"claims": dict(sorted(rows.items()))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--initialize", action="store_true")
    parser.add_argument("--inventory", type=Path)
    args = parser.parse_args()
    data = inventory()
    if args.inventory:
        args.inventory.write_text(json.dumps(data, indent=2) + "\n")
    if args.initialize:
        MANIFEST.write_text(json.dumps(initialize(data), indent=2) + "\n")
        print(f"Initialized {len(data['claims'])} claim rows")
        return
    count = validate(data, json.loads(MANIFEST.read_text()))
    print(f"PASS {count} public claims have final proofs and separate proved non-vacuity statements or fixed-data exceptions")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        raise SystemExit("FAIL " + str(error))
