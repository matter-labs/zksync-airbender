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

/-- A claim is a definition whose type is `Prop`. -/
def isPropDefinition : ConstantInfo → Bool
  | .defnInfo info => info.type.consumeMData == .sort .zero
  | _ => false

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

/-- Whether a term at binder depth `depth` mentions a variable whose binder level is in `levels`. -/
def mentionsLevels (levels : List Nat) (depth : Nat) : Lean.Expr → Bool
  | .bvar i => i < depth && levels.contains (depth - 1 - i)
  | .app f a => mentionsLevels levels depth f || mentionsLevels levels depth a
  | .lam _ type body _ | .forallE _ type body _ =>
      mentionsLevels levels depth type || mentionsLevels levels (depth + 1) body
  | .letE _ type value body _ =>
      mentionsLevels levels depth type || mentionsLevels levels depth value || mentionsLevels levels (depth + 1) body
  | .mdata _ body | .proj _ _ body => mentionsLevels levels depth body
  | _ => false

/-- The binder kinds of the premises of a claim definition, outermost first. -/
def premiseBinders : Lean.Expr → List BinderInfo
  | .forallE _ _ body binder => binder :: premiseBinders body
  | .mdata _ body => premiseBinders body
  | _ => []

/-- The arguments that must carry witness data in an application whose head is the claim (binder level 0) or a
    projection of it. When the claim itself is the head, these are its explicit arguments. Otherwise they are all
    arguments after the projection. -/
def claimArguments (env : Environment) (binders : List BinderInfo) (depth : Nat) (expression : Lean.Expr) :
    Option (Array Lean.Expr) :=
  let function := expression.getAppFn.consumeMData
  let arguments := expression.getAppArgs
  let headSize := (List.range (arguments.size + 1)).find? fun split =>
    0 < depth && claimProjection env 64 (mkAppN function (arguments.extract 0 split)) (depth - 1)
  headSize.map fun split =>
    if split == 0 then
      (arguments.toList.zipIdx.filter fun (_, index) => (binders[index]?.getD .default).isExplicit).toArray.map
        Prod.fst
    else arguments.extract split arguments.size

/-- Whether the evidence applies its claim to data of its witness: every explicit argument mentions witness data.
    Witness data is the witness (binder level 1), a `let` variable bound to witness data, and a variable that a
    function argument binds when its application eliminates witness data (a `match` alternative or a `casesOn`
    minor premise). -/
partial def appliesToWitness (env : Environment) (binders : List BinderInfo) (levels : List Nat) (depth : Nat)
    (binds : Bool) (expression : Lean.Expr) : Bool :=
  let recurse := appliesToWitness env binders
  match expression.consumeMData with
  | .lam _ type body _ =>
      recurse levels depth false type || recurse (if binds then depth :: levels else levels) (depth + 1) binds body
  | .forallE _ type body _ => recurse levels depth false type || recurse levels (depth + 1) false body
  | .letE _ type value body _ =>
      recurse levels depth false type || recurse levels depth false value ||
        recurse (if mentionsLevels levels depth value then depth :: levels else levels) (depth + 1) false body
  | .proj _ _ body => recurse levels depth false body
  | application@(.app ..) =>
      let arguments := application.getAppArgs
      let eliminates := arguments.any (mentionsLevels levels depth)
      let applied := match claimArguments env binders depth application with
        | some claimed => !claimed.isEmpty && claimed.all (mentionsLevels levels depth)
        | none => false
      applied || recurse levels depth false application.getAppFn || arguments.any (recurse levels depth eliminates)
  | _ => false

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
  let binders := match env.find? claim with
    | some (.defnInfo definition) => premiseBinders definition.value
    | _ => []
  unless appliesToWitness env binders [1] 0 false info.value do
    throwError "Evidence does not apply its claim to its witness data: {name}"
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
    code = "\n".join("import " + m for m in modules) + "\nimport Lean\n" + evidence + EVIDENCE_AUDIT + '''
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for h : index in [0:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[index]
    if mod.toString.startsWith "Human." || mod.toString.startsWith "Proven.Final." then
      for name in env.header.moduleData[index]!.constNames do
        if mod.toString.startsWith "Human." && name.toString.endsWith "Claim" then
          if let some info := env.find? name then
            unless ClaimCoverageAudit.isPropDefinition info do
              logInfo m!"NON_DEF_CLAIM {name}"
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
    applications, non_props, non_definitions = set(), [], []
    for line in result.stdout.splitlines():
        fields = line.split()
        if fields and fields[0] == "NON_PROP_CLAIM":
            non_props.append(fields[1])
        elif fields and fields[0] == "NON_DEF_CLAIM":
            non_definitions.append(fields[1])
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
            "non_definitions": non_definitions,
            "status_claims": re.findall(r"^\| \[`([^`]+)`\]\(", STATUS.read_text(), re.M)}


def allowed_exception(name, info, kind):
    """Only the listed fixed-data statements have a non-vacuity exception."""
    return name in EXCEPTIONS.get(kind, set())


def expected_witness(name, claims):
    """The witness of a claim is `<stem>SatisfiableClaim`. The stem is the name without `Claim`, or without
    `SoundnessClaim` when only that witness exists."""
    candidates = [name.removesuffix("Claim") + "SatisfiableClaim"]
    if name.endswith("SoundnessClaim"):
        candidates.append(name.removesuffix("SoundnessClaim") + "SatisfiableClaim")
    return next((candidate for candidate in candidates if candidate in claims), None)


def validate(data, manifest):
    if data.get("non_props"):
        raise ValueError("Public claim is not a proposition: " + ", ".join(data["non_props"]))
    if data.get("non_definitions"):
        raise ValueError("Claim is not a Prop-typed definition: " + ", ".join(data["non_definitions"]))
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
    witnessed = {}
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
        if witness != expected_witness(name, claims):
            raise ValueError(f"Witness of {name} must be its stem SatisfiableClaim, not {witness}")
        if witness in witnessed:
            raise ValueError(f"Witness {witness} serves two claims: {witnessed[witness]} and {name}")
        witnessed[witness] = name
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
        witness = expected_witness(name, claims)
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
