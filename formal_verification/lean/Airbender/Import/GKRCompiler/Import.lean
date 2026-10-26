import Airbender.Proofs.GKRCompiler.Arithmetic
import Airbender.Import.Schema
import Mathlib.Data.ZMod.Basic
import Lean

namespace Airbender.Compiler.Import
open Lean Elab Command
set_option warningAsError true

structure RemainingInputs where
  delegation : Bool
  executor : Bool
  lookups : Nat
  memory_queries : Nat
  range_checks : Nat
  register_and_indirect_accesses : Nat
  deriving FromJson

structure Source where
  num_variables : Nat
  statements : Array StructuredStatement
  booleans : Array Nat
  layers : Array (Nat × Nat)
  remaining_inputs : RemainingInputs
  deriving FromJson

structure Pair where
  format_version : Nat
  family : String
  cached : Bool
  source : Source
  circuit : Circuit
  deriving FromJson

abbrev EncodedPolynomial := Array (Nat × Array Nat)
abbrev EncodedCombination := Array (EncodedPolynomial × Nat)

structure IdentityCertificate where
  format_version : Nat
  addresses : Array GKRAddress
  selected : Array Nat
  extension : Array EncodedPolynomial
  backward : Array EncodedCombination
  forward : Array EncodedCombination
  deriving FromJson

private def finSyntax (index bound : Nat) : CommandElabM (TSyntax `term) := do
  unless index < bound do throwError "compiler certificate index {index} is outside bound {bound}"
  `(⟨$(quote index), by decide⟩)

private def fieldSyntax (raw : Coefficient) : CommandElabM (TSyntax `term) :=
  `((($(quote raw.raw.val) : ZMod babyBearModulus) * $(quote montgomeryInverse)))

private def constantSyntax (raw : Coefficient) : CommandElabM (TSyntax `term) := do
  `(Compiler.Expression.constant $(← fieldSyntax raw))

private def zeroSyntax : CommandElabM (TSyntax `term) := `(Compiler.Expression.constant 0)
private def oneSyntax : CommandElabM (TSyntax `term) := `(Compiler.Expression.constant 1)

private def atomSyntax (index bound : Nat) : CommandElabM (TSyntax `term) := do
  `(Compiler.Expression.atom $(← finSyntax index bound))

private def addSyntax (left right : TSyntax `term) : CommandElabM (TSyntax `term) :=
  `(Compiler.Expression.add $left $right)

private def mulSyntax (left right : TSyntax `term) : CommandElabM (TSyntax `term) :=
  `(Compiler.Expression.mul $left $right)

private partial def sourceSyntax (bound : Nat) : Expr → CommandElabM (TSyntax `term)
  | .Constant raw => constantSyntax raw
  | .Var index => atomSyntax index bound
  | .Sum terms => do terms.foldlM (fun result term => do addSyntax result (← sourceSyntax bound term)) (← zeroSyntax)
  | .Product terms => do terms.foldlM (fun result term => do mulSyntax result (← sourceSyntax bound term)) (← oneSyntax)

private def statementSyntax (bound : Nat) : StructuredStatement → CommandElabM (TSyntax `term)
  | .AssertZero expression _ _ => sourceSyntax bound expression
  | .Define dst _ expression _ => do
      let negative ← `(Compiler.Expression.constant (-1))
      addSyntax (← atomSyntax dst bound) (← mulSyntax negative (← sourceSyntax bound expression))

private def addressIndex (addresses : Array GKRAddress) (address : GKRAddress) : CommandElabM Nat := do
  match addresses.findIdx? (· == address) with
  | some index => return index
  | none => throwError "native GKR dependency is absent from the certificate address bank: {repr address}"

private def addressSyntax (addresses : Array GKRAddress) (address : GKRAddress) : CommandElabM (TSyntax `term) := do
  atomSyntax (← addressIndex addresses address) addresses.size

private partial def structuredSyntax (addresses : Array GKRAddress) : StructuredExpression → CommandElabM (TSyntax `term)
  | .Constant raw => constantSyntax raw
  | .Place address => addressSyntax addresses address
  | .Sum terms => do terms.foldlM (fun result term => do addSyntax result (← structuredSyntax addresses term)) (← zeroSyntax)
  | .Product terms => do terms.foldlM (fun result term => do mulSyntax result (← structuredSyntax addresses term)) (← oneSyntax)

private def linearSyntax (addresses : Array GKRAddress) (relation : LinearRelation) : CommandElabM (TSyntax `term) := do
  relation.linear_terms.foldlM (fun result (coefficient, address) => do
    addSyntax result (← mulSyntax (← constantSyntax coefficient) (← addressSyntax addresses address)))
    (← constantSyntax relation.constant)

private def quadraticSyntax (addresses : Array GKRAddress) (relation : CompiledMaxQuadraticGKRRelation) :
    CommandElabM (TSyntax `term) := do
  let linear : LinearRelation := ⟨relation.linear_terms, relation.constant⟩
  relation.quadratic_terms.foldlM (fun result (left, terms) => do
    terms.foldlM (fun result (coefficient, right) => do
      let term ← mulSyntax (← mulSyntax (← constantSyntax coefficient) (← addressSyntax addresses left))
        (← addressSyntax addresses right)
      addSyntax result term) result) (← linearSyntax addresses linear)

private def gateSyntax (addresses : Array GKRAddress) : GKRRelation → CommandElabM (Option (TSyntax `term))
  | .EnforceSingleMaxQuadraticConstraint input expression => do
      return some (← `(Compiler.ArithmeticGate.assertZero
        $(← quadraticSyntax addresses input) $(← structuredSyntax addresses expression)))
  | .MaxQuadratic input expression output => do
      return some (← `(Compiler.ArithmeticGate.define
        $(← finSyntax (← addressIndex addresses output) addresses.size)
        $(← quadraticSyntax addresses input) $(← structuredSyntax addresses expression)))
  | .LinearBaseFieldRelation input output => do
      let expression ← linearSyntax addresses input
      return some (← `(Compiler.ArithmeticGate.define
        $(← finSyntax (← addressIndex addresses output) addresses.size) $expression $expression))
  | .CopyInBaseField input output => do
      return some (← `(Compiler.ArithmeticGate.copy
        $(← finSyntax (← addressIndex addresses output) addresses.size)
        $(← finSyntax (← addressIndex addresses input) addresses.size)))
  | .EnforceConstraintsMaxQuadratic _ => throwError "batched arithmetic requires a separate checked adapter"
  | _ => return none

private def polynomialSyntax (arity : Nat) (encoded : EncodedPolynomial) : CommandElabM (TSyntax `term) := do
  let terms ← encoded.mapM fun (coefficient, monomial) => do
    unless coefficient < babyBearModulus do throwError "noncanonical certificate coefficient"
    let wires ← monomial.mapM fun wire => finSyntax wire arity
    `((($(quote coefficient) : ZMod babyBearModulus), [$[$wires],*]))
  `([$[$terms],*])

private def combinationSyntax (arity count : Nat) (encoded : EncodedCombination) : CommandElabM (TSyntax `term) := do
  let terms ← encoded.mapM fun (polynomial, index) => do
    `(($(← polynomialSyntax arity polynomial), $(← finSyntax index count)))
  `([$[$terms],*])

private def checksSyntax (proofs : Array (TSyntax `ident)) : CommandElabM (TSyntax `term) := do
  let mut result ← `(Compiler.BoolChecks.nil)
  for proof in proofs.reverse do
    result ← `(Compiler.BoolChecks.cons $proof $result)
  return result

/-- Load actual pre-compiler expressions and actual native arithmetic gates.
The external certificate supplies identities/selection, never replacement
source equations or replacement lowered equations. File parsing/emission is
the same explicit data-binding boundary used by the existing native importer. -/
elab "import_compiler_arithmetic " name:ident " from " pairPath:str " certificate " certPath:str : command => do
  let pairBytes ← IO.FS.readFile pairPath.getString
  let certBytes ← IO.FS.readFile certPath.getString
  let pair : Pair ← match Json.parse pairBytes >>= (fromJson? (α := Pair)) with
    | .ok value => pure value
    | .error error => throwError "native compiler pair parse failed: {error}"
  let certificate : IdentityCertificate ← match Json.parse certBytes >>= (fromJson? (α := IdentityCertificate)) with
    | .ok value => pure value
    | .error error => throwError "compiler identity parse failed: {error}"
  unless pair.format_version == 1 && certificate.format_version == 1 do
    throwError "unsupported compiler translation format"
  unless certificate.addresses.toList.eraseDups.length == certificate.addresses.size do
    throwError "compiler address bank contains duplicate native addresses"
  let n := pair.source.num_variables
  let m := certificate.addresses.size
  let mut source ← pair.source.statements.mapM (statementSyntax n)
  for wire in pair.source.booleans do
    let atom ← atomSyntax wire n
    let negative ← `(Compiler.Expression.constant (-1))
    source := source.push (← mulSyntax atom (← addSyntax atom negative))
  let mut gates := #[]
  for layer in pair.circuit.layers do
    for gate in layer.gates ++ layer.gates_with_external_connections do
      if let some gateTerm ← gateSyntax certificate.addresses gate.enforced_relation then
        gates := gates.push gateTerm
  let mut placement := #[]
  for index in [:n] do
    let found := pair.circuit.placement_data.entries.filter (·.1 == index)
    let #[( _, address)] := found | throwError "source variable {index} has missing/ambiguous native placement"
    placement := placement.push (← finSyntax (← addressIndex certificate.addresses address) m)
  unless certificate.extension.size == m && certificate.backward.size == source.size &&
      certificate.forward.size == certificate.selected.size do
    throwError "compiler certificate dimensions disagree with actual source/gate counts"
  let selected ← certificate.selected.mapM fun index => finSyntax index gates.size
  let extension ← certificate.extension.mapM (polynomialSyntax n)
  let backward ← certificate.backward.mapM (combinationSyntax m selected.size)
  let forward ← certificate.forward.mapM (combinationSyntax n source.size)
  let artifactName := mkIdent (name.getId ++ `artifact)
  let selectedName := mkIdent (name.getId ++ `selected)
  let extensionDataName := mkIdent (name.getId ++ `extensionData)
  let extensionName := mkIdent (name.getId ++ `extension)
  let translationName := mkIdent (name.getId ++ `translation)
  let backwardName := mkIdent (name.getId ++ `backwardData)
  let forwardName := mkIdent (name.getId ++ `forwardData)
  let certificateName := mkIdent (name.getId ++ `certificate)
  let checkedName := mkIdent (name.getId ++ `checked)
  let gatesCheckedName := mkIdent (name.getId ++ `gatesChecked)
  let mut sourceReferences := #[]
  for index in [:source.size] do
    let reference := mkIdent (name.getId ++ Name.mkSimple s!"sourceExpression{index}")
    let expression := source[index]!
    elabCommand (← `(def $reference : Compiler.Expression $(quote n) (ZMod babyBearModulus) := $expression))
    sourceReferences := sourceReferences.push reference
  let mut gateReferences := #[]
  for index in [:gates.size] do
    let reference := mkIdent (name.getId ++ Name.mkSimple s!"gate{index}")
    let gateTerm := gates[index]!
    elabCommand (← `(def $reference : Compiler.ArithmeticGate $(quote m) (ZMod babyBearModulus) := $gateTerm))
    gateReferences := gateReferences.push reference
  elabCommand (← `(def $artifactName : Compiler.ArithmeticArtifact $(quote n) $(quote m) (ZMod babyBearModulus) := {
    source := [$[$sourceReferences],*]
    gates := [$[$gateReferences],*]
    placement := fun index => (#v[$[$placement],*] : Vector (Fin $(quote m)) $(quote n))[index] }))
  elabCommand (← `(def $selectedName : List (Fin ($artifactName).gates.length) := [$[$selected],*]))
  elabCommand (← `(def $extensionDataName : Vector (Compiler.Polynomial $(quote n) (ZMod babyBearModulus)) $(quote m) := #v[$[$extension],*]))
  elabCommand (← `(def $extensionName (index : Fin $(quote m)) := $extensionDataName[index]))
  elabCommand (← `(def $translationName := ($artifactName).translation $selectedName $extensionName))
  elabCommand (← `(def $backwardName : Vector (Compiler.Combination ($translationName).lowered) ($translationName).source.length := #v[$[$backward],*]))
  elabCommand (← `(def $forwardName : Vector (Compiler.Combination ($translationName).source) ($translationName).lowered.length := #v[$[$forward],*]))
  elabCommand (← `(def $certificateName : Compiler.Certificate $translationName := {
    backward := fun index => $backwardName[index]
    forward := fun index => $forwardName[index] }))
  let mut gateProofs := #[]
  for index in [:gates.size] do
    let gateName := gateReferences[index]!
    let proof := mkIdent (name.getId ++ Name.mkSimple s!"gateChecked{index}")
    elabCommand (← `(theorem $proof : ($gateName).check = true := by decide +kernel))
    gateProofs := gateProofs.push proof
  elabCommand (← `(theorem $gatesCheckedName : ($artifactName).gates.all Compiler.ArithmeticGate.check = true :=
    Compiler.BoolChecks.all_true $(← checksSyntax gateProofs)))
  let mut projectionProofs := #[]
  for index in [:n] do
    let wire ← finSyntax index n
    let proof := mkIdent (name.getId ++ Name.mkSimple s!"projectionChecked{index}")
    elabCommand (← `(theorem $proof : Compiler.equal
      (($translationName).extension (($translationName).projection $wire)) (Compiler.atom $wire) = true := by decide +kernel))
    projectionProofs := projectionProofs.push proof
  let projectionCheckedName := mkIdent (name.getId ++ `projectionChecked)
  elabCommand (← `(theorem $projectionCheckedName :
    (List.finRange $(quote n)).all (fun wire => Compiler.equal
      (($translationName).extension (($translationName).projection wire)) (Compiler.atom wire)) = true :=
    Compiler.BoolChecks.all_true $(← checksSyntax projectionProofs)))
  let mut backwardProofs := #[]
  for index in [:source.size] do
    let position ← finSyntax index source.size
    let proof := mkIdent (name.getId ++ Name.mkSimple s!"backwardChecked{index}")
    elabCommand (← `(theorem $proof : Compiler.equal
      (Compiler.rename ($translationName).projection (($translationName).source.get $position))
      (Compiler.combination ($translationName).lowered (($certificateName).backward $position)) = true := by decide +kernel))
    backwardProofs := backwardProofs.push proof
  let backwardCheckedName := mkIdent (name.getId ++ `backwardChecked)
  elabCommand (← `(theorem $backwardCheckedName :
    (List.finRange ($translationName).source.length).all (fun index => Compiler.equal
      (Compiler.rename ($translationName).projection (($translationName).source.get index))
      (Compiler.combination ($translationName).lowered (($certificateName).backward index))) = true :=
    Compiler.BoolChecks.all_true $(← checksSyntax backwardProofs)))
  let mut forwardProofs := #[]
  for index in [:selected.size] do
    let position ← finSyntax index selected.size
    let proof := mkIdent (name.getId ++ Name.mkSimple s!"forwardChecked{index}")
    elabCommand (← `(theorem $proof : Compiler.equal
      (Compiler.substitute ($translationName).extension (($translationName).lowered.get $position))
      (Compiler.combination ($translationName).source (($certificateName).forward $position)) = true := by decide +kernel))
    forwardProofs := forwardProofs.push proof
  let forwardCheckedName := mkIdent (name.getId ++ `forwardChecked)
  elabCommand (← `(theorem $forwardCheckedName :
    (List.finRange ($translationName).lowered.length).all (fun index => Compiler.equal
      (Compiler.substitute ($translationName).extension (($translationName).lowered.get index))
      (Compiler.combination ($translationName).source (($certificateName).forward index))) = true :=
    Compiler.BoolChecks.all_true $(← checksSyntax forwardProofs)))
  elabCommand (← `(theorem $checkedName : Compiler.check $translationName $certificateName = true :=
    Compiler.and_checked (Compiler.and_checked $projectionCheckedName $backwardCheckedName) $forwardCheckedName))

end Airbender.Compiler.Import
