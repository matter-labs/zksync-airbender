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
STATUS = ROOT.parent / "docs/VERIFICATION_STATUS.md"
EVIDENCE_MODULE = "Checks.Satisfiable"
EVIDENCE_FILE = ROOT / "test/Checks/Satisfiable.lean"
SPECIAL_MODULES = {
    "Human.Compiler.NativeTargets", "Human.Trace.Machine.Theorems",
    "Human.Trace.Machine.Padding", "Human.ISA.DelegationRuns",
}



def evidence_source(source):
    """Name the existing Lean examples so that the audit can read their proof terms."""
    names = []
    def name_example(match):
        name = f"Checks.ClaimCoverage.case{len(names)}"
        names.append(name)
        return f"theorem _root_.{name} (claim :"
    source = re.sub(r"(?m)^import [^\n]+\n", "", source)
    source = re.sub(r"(?m)^example \(claim\s*:", name_example, source)
    return source, names


EVIDENCE_AUDIT = r'''
namespace ClaimCoverageAudit
open Lean Elab Command

def claimProjection (env : Environment) : Nat → Lean.Expr → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, expression, index =>
    match expression.consumeMData with
    | .bvar i => i == index
    | .proj _ _ body => claimProjection env fuel body index
    | e@(.app ..) =>
        match e.getAppFn with
        | .const name _ =>
            match env.getProjectionFnInfo? name with
            | some projection =>
                match e.getAppArgs[projection.numParams]? with
                | some argument => claimProjection env fuel argument index
                | none => false
            | none => false
        | _ => false
    | _ => false

def appliedParameter (env : Environment) : Lean.Expr → Nat → Bool
  | .app f a, index =>
      claimProjection env 64 f index || appliedParameter env f index || appliedParameter env a index
  | .lam _ type body _, index | .forallE _ type body _, index =>
      appliedParameter env type index || appliedParameter env body (index + 1)
  | .letE _ type value body _, index =>
      appliedParameter env type index || appliedParameter env value index || appliedParameter env body (index + 1)
  | .mdata _ body, index | .proj _ _ body, index => appliedParameter env body index
  | _, _ => false

def mentionsParameter : Lean.Expr → Nat → Bool
  | .bvar i, index => i == index
  | .app f a, index => mentionsParameter f index || mentionsParameter a index
  | .lam _ type body _, index | .forallE _ type body _, index =>
      mentionsParameter type index || mentionsParameter body (index + 1)
  | .letE _ type value body _, index =>
      mentionsParameter type index || mentionsParameter value index || mentionsParameter body (index + 1)
  | .mdata _ body, index | .proj _ _ body, index => mentionsParameter body index
  | _, _ => false

def audit (name : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some (.thmInfo info) := env.find? name | throwError "Missing evidence theorem {name}"
  let .forallE _ (.const claim _) body _ := info.type.consumeMData |
    throwError "Evidence must take its named claim first: {name}"
  let .forallE _ (.const witness _) _ _ := body.consumeMData |
    throwError "Evidence must take its named witness second: {name}"
  let .lam _ _ proof _ := info.value.consumeMData |
    throwError "Evidence must use its claim parameter: {name}"
  unless appliedParameter env proof 0 do
    throwError "Evidence does not apply its claim: {name}"
  let .lam _ _ proof _ := proof.consumeMData |
    throwError "Evidence must use its witness parameter: {name}"
  unless mentionsParameter proof 0 do
    throwError "Evidence does not use its witness: {name}"
  logInfo m!"WITNESS_APPLICATION {claim} {witness}"
end ClaimCoverageAudit
'''

EXCEPTIONS = {
    'artifact': {
        'Airbender.AddSub.ArtifactImportClaim',
        'Airbender.Bigint.ArtifactImportClaim',
        'Airbender.Blake2G.ArtifactImportClaim',
        'Airbender.Blake2Round.ArtifactImportClaim',
        'Airbender.Compiler.AddSubCachedDescriptionClaim',
        'Airbender.Compiler.BigintCachedDescriptionClaim',
        'Airbender.Compiler.BlakeGCachedDescriptionClaim',
        'Airbender.Compiler.BlakeRoundCachedDescriptionClaim',
        'Airbender.Compiler.JumpBranchCachedDescriptionClaim',
        'Airbender.Compiler.KeccakCachedDescriptionClaim',
        'Airbender.Compiler.KeccakColumnParityCachedDescriptionClaim',
        'Airbender.Compiler.KeccakThetaRhoCachedDescriptionClaim',
        'Airbender.Compiler.KeccakChi5CachedDescriptionClaim',
        'Airbender.Compiler.MulDivCachedDescriptionClaim',
        'Airbender.Compiler.ShiftBinopCachedDescriptionClaim',
        'Airbender.Compiler.SubwordMemoryCachedDescriptionClaim',
        'Airbender.Compiler.UnifiedCachedDescriptionClaim',
        'Airbender.Compiler.WordMemoryCachedDescriptionClaim',
        'Airbender.InitsTeardowns.Native.StandaloneBindingClaim',
        'Airbender.InitsTeardowns.Native.UnifiedBindingClaim',
        'Airbender.InitsTeardowns.StandaloneBytesClaim',
        'Airbender.InitsTeardowns.SharedBytesClaim',
        'Airbender.InitsTeardowns.StandaloneImportClaim',
        'Airbender.InitsTeardowns.UnifiedImportClaim',
        'Airbender.JumpBranchSlt.ArtifactImportClaim',
        'Airbender.Keccak.ArtifactImportClaim',
        'Airbender.Keccak.Split.Chi5.ArtifactImportClaim',
        'Airbender.Keccak.Split.ColumnParity.ArtifactImportClaim',
        'Airbender.Keccak.Split.ThetaRho.ArtifactImportClaim',
        'Airbender.MulDiv.ArtifactImportClaim',
        'Airbender.ShiftBinop.ArtifactImportClaim',
        'Airbender.SubwordMemory.ArtifactImportClaim',
        'Airbender.UnifiedReduced.ArtifactImportClaim',
        'Airbender.WordMemory.ArtifactImportClaim',
    },
    'constant': {
        'Airbender.MachineChecksClaim',
        'RV.StandardVectors',
    },
    'import': {
        'Airbender.ConstantsClaim',
    },
}

def inventory():
    modules = [".".join(p.relative_to(ROOT / folder).with_suffix("").parts)
               for folder, prefix in [("human", "Human"), ("proven", "Proven/Final")]
               for p in sorted((ROOT / folder / prefix).rglob("*.lean"))]
    evidence, evidence_names = evidence_source(EVIDENCE_FILE.read_text())
    code = "\n".join("import " + m for m in modules) + "\nimport Lean\n" + evidence + '''
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for h : index in [0:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[index]
    if mod.toString.startsWith "Human." || mod.toString.startsWith "Proven.Final." then
      for name in env.header.moduleData[index]!.constNames do
        if !isPrivateName name then
          if mod.toString.startsWith "Human." && name.toString.endsWith "Claim" then
            if let some info := env.find? name then
              if info.type.consumeMData != .sort .zero then
                logInfo m!"NON_PROP_CLAIM {name}"
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
    code += EVIDENCE_AUDIT
    for name in evidence_names:
        code += f'\nrun_cmd ClaimCoverageAudit.audit ``{name}\n'
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
    applications, non_props = set(), []
    for line in result.stdout.splitlines():
        fields = line.split()
        if fields and fields[0] == "NON_PROP_CLAIM":
            non_props.append(fields[1])
        elif fields and fields[0] == "WITNESS_APPLICATION":
            applications.add((fields[1], fields[2]))
        elif fields and fields[0] == "HUMAN_PROP":
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
            "proof_modules": proof_modules, "applications": sorted(applications), "non_props": non_props,
            "status_claims": re.findall(r"^\| \[`([^`]+)`\]\(", STATUS.read_text(), re.M)}


def allowed_exception(name, info, kind):
    """Only the listed fixed-data statements have a non-vacuity exception."""
    return name in EXCEPTIONS.get(kind, set())


def validate(data, manifest):
    if data.get("non_props"):
        raise ValueError("Public claim is not a proposition: " + ", ".join(data["non_props"]))
    claims, proofs = data["claims"], data["proofs"]
    rows = manifest["claims"]
    if set(rows) != set(claims):
        missing = sorted(set(claims) - set(rows))
        stale = sorted(set(rows) - set(claims))
        raise ValueError(f"Claim inventory mismatch. Missing: {missing}. Stale: {stale}")
    if "status_claims" in data:
        missing_status = sorted(set(claims) - set(data["status_claims"]))
        if missing_status:
            raise ValueError("Missing claim status rows: " + ", ".join(missing_status))
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
        if row.get("evidence") != EVIDENCE_MODULE:
            raise ValueError("Missing typed witness evidence: " + name)
        if (name, witness) not in {tuple(pair) for pair in data.get("applications", [])}:
            raise ValueError("Missing claim application to its own witness: " + name)
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
            rows[name] = {"witness": witness, "evidence": EVIDENCE_MODULE}
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
