#!/usr/bin/env python3
"""Require a final proof for every public claim, and a separate proved witness with exactly its premises."""
from pathlib import Path
import argparse
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "claim_coverage.json"
STATUS = ROOT.parent / "docs/VERIFICATION_STATUS.md"
SPECIAL_MODULES = {
    "Human.Compiler.NativeTargets", "Human.Trace.Machine.Theorems",
    "Human.Trace.Machine.Padding", "Human.ISA.DelegationRuns",
}

# The Lean audit. A witness `W` matches its claim `C := ∀ x₁ … xₙ, P₁ → … → Pₘ → Q` when `W` unfolds to
# `∃ y₁ … yₖ, P₁ ∧ … ∧ Pₘ ∧ extra`: each premise is definitionally equal to the conjunct at its position, the witness
# binders are the claim binders in the same order with the same types, and a claim binder that the witness does not
# bind takes a closed value (a fixed parameter such as the field modulus). Instance binders take synthesized instances.
# Conjuncts after the m premises are extra facts, such as `rows ≠ []`. The premises end at the last premise binder.
AUDIT = r'''
namespace ClaimCoverageAudit
open Lean Meta Elab Command

/-- A claim is a definition of type `Prop`, or a structure of type `Prop` without parameters. -/
def isClaimDeclaration (env : Environment) : ConstantInfo → Bool
  | .defnInfo info => info.type.consumeMData == .sort .zero
  | .inductInfo info => isStructure env info.name && info.numParams == 0 && info.type.consumeMData == .sort .zero
  | _ => false

/-- The statement of a claim. A structure claim states its fields: a structure with one field states that field,
    and a structure with more fields states their conjunction, which has no premises. -/
def claimStatement (claim : Name) : MetaM (Option Lean.Expr) := do
  match (← getEnv).find? claim with
  | some (.defnInfo info) => return some info.value
  | some (.inductInfo info) =>
      let [constructorName] := info.ctors | return none
      let some (.ctorInfo constructor) := (← getEnv).find? constructorName | return none
      forallTelescope constructor.type fun fields _ => do
        let types ← fields.mapM inferType
        match types.toList with
        | [single] => return some single
        | many => return some (many.foldr (fun type rest => mkAnd type rest) (mkConst ``True))
  | _ => return none

/-- Open a witness statement as its telescope: the existential binders and the conjuncts of its right spine, in
    order. Each binder records the number of conjuncts before it. -/
partial def openWitness {α : Type} (expression : Lean.Expr) (binders : Array (Lean.Expr × Nat))
    (conjuncts : Array Lean.Expr) (continuation : Array (Lean.Expr × Nat) → Array Lean.Expr → MetaM α) : MetaM α := do
  let expression := expression.consumeMData
  match expression.getAppFnArgs with
  | (``Exists, #[type, predicate]) =>
      let name := match predicate.consumeMData with | .lam name _ _ _ => name | _ => `x
      withLocalDeclD name type fun bound =>
        openWitness (predicate.beta #[bound]) (binders.push (bound, conjuncts.size)) conjuncts continuation
  | (``And, #[left, right]) => openWitness right binders (conjuncts.push left) continuation
  | _ => continuation binders (conjuncts.push expression)

/-- Soundness templates whose definitions state premises. The audit unfolds them in a claim conclusion. -/
def premiseTemplates : List Name := [`Airbender.Properties.Soundness, `Airbender.Verification.CircuitModel.SoundnessUnder]

/-- Unfold the premise templates at the conclusion of a statement. -/
partial def unfoldTemplates (statement : Lean.Expr) : MetaM Lean.Expr :=
  forallTelescope statement fun binders conclusion => do
    let template := match conclusion.getAppFn with
      | .const name _ => premiseTemplates.contains name
      | _ => false
    if template then
      if let some unfolded ← unfoldDefinition? conclusion then
        return ← mkForallFVars binders (← unfoldTemplates unfolded.headBeta)
    mkForallFVars binders conclusion

/-- Match one premise against the witness conjuncts from `position`. A conjunction premise matches one conjunct, or
    one conjunct for each of its parts. Returns the position after the matched conjuncts. -/
partial def matchPremise (premise : Lean.Expr) (conjuncts : Array Lean.Expr) (position : Nat) : MetaM (Option Nat) := do
  let some conjunct := conjuncts[position]? | return none
  if ← isDefEq premise conjunct then return some (position + 1)
  if let some (left, right) := (← whnfR premise).and? then
    if let some afterLeft ← matchPremise left conjuncts position then
      return ← matchPremise right conjuncts afterLeft
  return none

/-- Why a witness statement is not the premise telescope of its claim, or `none` when it is. `some "no premises"`
    marks a claim without premises. -/
def telescopeMismatch (claim witness : Name) : MetaM (Option String) := do
  let some claimValue ← claimStatement claim | return some "the claim is not a definition or a structure"
  let some (.defnInfo witnessInfo) := (← getEnv).find? witness | return some "the witness is not a definition"
  let statement ← unfoldTemplates claimValue
  let premiseEnd ← forallTelescope statement fun binders _ => do
    let mut last := 0
    for h : index in [0:binders.size] do
      let declaration ← binders[index].fvarId!.getDecl
      if !declaration.binderInfo.isInstImplicit && (← isProp declaration.type) then last := index + 1
    return last
  if premiseEnd == 0 then return some "no premises"
  openWitness witnessInfo.value #[] #[] fun witnessBinders conjuncts => do
    -- The claim metavariables live in the context of the witness binders, so that they can take them as values.
    let (claimBinders, binderInfos, _) ← forallMetaBoundedTelescope statement premiseEnd
    let mut position := 0
    let mut premise := 0
    for h : index in [0:claimBinders.size] do
      let type ← instantiateMVars (← inferType claimBinders[index])
      if binderInfos[index]!.isInstImplicit || !(← isProp type) then continue
      premise := premise + 1
      if position ≥ conjuncts.size then return some s!"the witness omits premise {premise}"
      let some after ← matchPremise type conjuncts position
        | return some s!"premise {premise} differs from the conjunct at its position"
      position := after
    -- Witness binders before the last premise conjunct are the claim binders; later binders belong to extra facts.
    let required := (witnessBinders.filter fun (_, before) => before < position).map Prod.fst
    let mut mapped := 0
    for h : index in [0:claimBinders.size] do
      let type ← instantiateMVars (← inferType claimBinders[index])
      if binderInfos[index]!.isInstImplicit || (← isProp type) then continue
      let value ← instantiateMVars claimBinders[index]
      if value.isMVar then
        let some bound := required[mapped]? | return some s!"claim binder {index + 1} has no witness binder"
        unless ← isDefEq value bound do return some s!"claim binder {index + 1} has another type"
        mapped := mapped + 1
      else if value.isFVar then
        unless required[mapped]? == some value do
          return some s!"claim binder {index + 1} takes a witness binder out of order"
        unless ← isDefEq (← inferType value) type do return some s!"claim binder {index + 1} has another type"
        mapped := mapped + 1
      else if value.hasFVar || value.hasMVar then
        return some s!"claim binder {index + 1} is a term of witness binders, not a witness binder"
    unless mapped == required.size do return some "the witness has a binder that the claim does not have"
    for h : index in [0:claimBinders.size] do
      if binderInfos[index]!.isInstImplicit then
        let value ← instantiateMVars claimBinders[index]
        if value.isMVar then
          let some found ← synthInstance? (← instantiateMVars (← inferType value))
            | return some s!"no instance for claim binder {index + 1}"
          unless ← isDefEq value found do return some s!"claim binder {index + 1} has another instance"
    return none

/-- Log whether the witness statement is the premise telescope of the claim. -/
def audit (claim witness : Name) : CommandElabM Unit := do
  match ← liftTermElabM (telescopeMismatch claim witness) with
  | none => logInfo m!"TELESCOPE_MATCH {claim} {witness}"
  | some reason => logInfo m!"TELESCOPE_MISMATCH {claim} {witness} {reason}"
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
        'Airbender.Bigint.SetupImportClaim',
        'Airbender.Blake2G.Control.SetupImportClaim',
        'Airbender.Keccak.Controller.SetupImportClaim',
        'Airbender.Blake2Round.SetupImportClaim',
        'Airbender.Compiler.NativeWorkerSetup.SetupImportClaim',
        'Airbender.Verification.ShiftBinopImportClaim',
        'Airbender.Compiler.NativeFixedRows.AddSubImportClaim',
        'Airbender.Compiler.NativeFixedRows.JumpBranchImportClaim',
        'Airbender.Compiler.NativeFixedRows.MulDivImportClaim',
        'Airbender.Compiler.NativeFixedRows.WordMemoryImportClaim',
        'Airbender.Compiler.NativeSetups.Range13ImportClaim',
        'Airbender.Compiler.NativeSetups.CPURangesImportClaim',
        'Airbender.Compiler.NativeFixedRows.SubwordMemoryImportClaim',
        'Airbender.Compiler.NativeFixedRows.UnifiedImportClaim',
    },
    'constant': {
        'Airbender.MachineChecksClaim',
        'RV.StandardVectors',
    },
    'import': {
        'Airbender.ConstantsClaim',
    },
}

def witness_pairs(manifest):
    """The (claim, witness) rows of the coverage map."""
    return sorted((name, row["witness"]) for name, row in manifest["claims"].items() if "witness" in row)


# The Lean audit's report for a claim without premises, and the only exception reason.
NO_PREMISES_FOUND = "no premises"
NO_PREMISES = "The claim has no premises. Its witness shows a nonempty instance of the claim's data."
TELESCOPE_EXCEPTIONS = {
    "Airbender.AgreeExistsClaim": NO_PREMISES,
    "Airbender.Compiler.NativeLookups.CachedLookupSelectorsClaim": NO_PREMISES,
    "Airbender.Compiler.NativeWorkerLookups.CachedWorkerLookupSelectorsClaim": NO_PREMISES,
    "Airbender.DecodeClaim": NO_PREMISES,
    "Airbender.InitsTeardowns.SharedBytesClaim": NO_PREMISES,
    "Airbender.InitsTeardowns.StandaloneClaim": NO_PREMISES,
    "Airbender.InitsTeardowns.UnifiedClaim": NO_PREMISES,
    "Airbender.PlacementsClaim": NO_PREMISES,
}


def inventory(pairs):
    modules = [".".join(p.relative_to(ROOT / folder).with_suffix("").parts)
               for folder, prefix in [("human", "Human"), ("proven", "Proven/Final")]
               for p in sorted((ROOT / folder / prefix).rglob("*.lean"))]
    code = "\n".join("import " + m for m in modules) + "\nimport Lean\n" + AUDIT + '''
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for h : index in [0:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[index]
    if mod.toString.startsWith "Human." || mod.toString.startsWith "Proven.Final." then
      for name in env.header.moduleData[index]!.constNames do
        if mod.toString.startsWith "Human." && name.toString.endsWith "Claim" then
          if let some info := env.find? name then
            unless ClaimCoverageAudit.isClaimDeclaration env info do
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
          | some (.inductInfo info) =>
            if mod.toString.startsWith "Human." && name.toString.endsWith "Claim" &&
                ClaimCoverageAudit.isClaimDeclaration env (.inductInfo info) then
              logInfo m!"HUMAN_PROP {name} {mod} structure false"
          | some (.thmInfo info) =>
            if mod.toString.startsWith "Proven.Final." then
              logInfo m!"FINAL_DECL {name} {mod}"
              if let .const claim _ := info.type.consumeMData then
                logInfo m!"FINAL_PROOF {name} {claim}"
          | _ => pure ()
'''
    for claim, witness in pairs:
        code += f'\nrun_cmd ClaimCoverageAudit.audit ``{claim} ``{witness}\n'
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
    telescopes, non_props, non_definitions = {}, [], []
    for line in result.stdout.splitlines():
        fields = line.split()
        if fields and fields[0] == "NON_PROP_CLAIM":
            non_props.append(fields[1])
        elif fields and fields[0] == "NON_DEF_CLAIM":
            non_definitions.append(fields[1])
        elif fields and fields[0] in {"TELESCOPE_MATCH", "TELESCOPE_MISMATCH"}:
            reason = line.split(None, 3)[3] if fields[0] == "TELESCOPE_MISMATCH" else None
            telescopes[f"{fields[1]} {fields[2]}"] = reason
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
            "proof_modules": proof_modules, "telescopes": telescopes, "non_props": non_props,
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
        raise ValueError("Claim is not a Prop-typed definition or structure: " + ", ".join(data["non_definitions"]))
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
        telescopes = data.get("telescopes", {})
        if f"{name} {witness}" not in telescopes:
            raise ValueError(f"Missing premise telescope check: {name} {witness}")
        mismatch = telescopes[f"{name} {witness}"]
        if name in TELESCOPE_EXCEPTIONS:
            # An exception covers only the checked form: Lean finds no premises, and the reason states that.
            if mismatch is None:
                raise ValueError(f"Stale premise telescope exception: {name}")
            if mismatch != NO_PREMISES_FOUND or TELESCOPE_EXCEPTIONS[name] != NO_PREMISES:
                raise ValueError(f"Premise telescope exception does not hold for {name}: {mismatch}")
        elif mismatch is not None:
            raise ValueError(f"Witness {witness} is not the premise telescope of {name}: {mismatch}")
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
    manifest = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else {"claims": {}}
    data = inventory(witness_pairs(manifest))
    if args.inventory:
        args.inventory.write_text(json.dumps(data, indent=2) + "\n")
    if args.initialize:
        MANIFEST.write_text(json.dumps(initialize(data), indent=2) + "\n")
        print(f"Initialized {len(data['claims'])} claim rows")
        return
    count = validate(data, manifest)
    print(f"PASS {count} public claims have final proofs and separate proved non-vacuity statements or fixed-data exceptions")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        raise SystemExit("FAIL " + str(error))
