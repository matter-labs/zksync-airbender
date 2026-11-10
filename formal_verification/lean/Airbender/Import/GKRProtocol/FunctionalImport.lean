import Airbender.Proofs.GKRProtocol.BaseAffine
import Airbender.Import.GKRProtocol.NativeLookupImport
import Airbender.Import.GKRProtocol.NativeProductImport
import Airbender.Import.GKRProtocol.LookupSourceData

namespace Airbender.Compiler.FunctionalImport
open Lean Elab Command
set_option warningAsError true

private def addressSyntax : GKRAddress → CommandElabM (TSyntax `term)
  | .BaseLayerWitness index => `(GKRAddress.BaseLayerWitness $(quote index))
  | .BaseLayerMemory index => `(GKRAddress.BaseLayerMemory $(quote index))
  | .InnerLayer layer index => `(GKRAddress.InnerLayer $(quote layer) $(quote index))
  | .Cached layer index => `(GKRAddress.Cached $(quote layer) $(quote index))
  | .Setup index => `(GKRAddress.Setup $(quote index))
  | .ScratchSpace _ => throwError "functional graph contains an unallocated scratch alias"
  | .VirtualSetup kind => do
      let kind ← match kind with
        | .RangeCheck16Bits => `(VirtualSetupPoly.RangeCheck16Bits)
        | .RangeCheckTimestamp => `(VirtualSetupPoly.RangeCheckTimestamp)
        | .InitsAndTeardownsLow => `(VirtualSetupPoly.InitsAndTeardownsLow)
        | .InitsAndTeardownsHigh => `(VirtualSetupPoly.InitsAndTeardownsHigh)
      `(GKRAddress.VirtualSetup $kind)

private def definitionSyntax (definition : LookupSourceData.Definition) : CommandElabM (TSyntax `term) := do
  let program ← match definition with
    | .cache _ relation => CacheImport.program relation
    | .copy _ input => `(AffineProgram.input (R := CacheCoefficient) $(← addressSyntax input))
    | .scalar _ row => CacheImport.program (.SingleColumnLookup row 0)
    | .vector _ row => CacheImport.program (.VectorizedLookup row)
  `(AffineDefinition.mk $(← addressSyntax definition.output) $program)

private def recipeSyntax : NativeBaseRecipe → CommandElabM (TSyntax `term)
  | .constant scalar => `(AffineProgram.constant (Address := GKRAddress) (R := Nat) $(quote scalar))
  | .input address => do `(AffineProgram.input (R := Nat) $(← addressSyntax address))
  | .add left right => do `(AffineProgram.add $(← recipeSyntax left) $(← recipeSyntax right))
  | .scale coefficient inner => do `(AffineProgram.scale $(quote coefficient) $(← recipeSyntax inner))

private def memberName (owner : Ident) (stem : String) (index : Nat) : Ident :=
  mkIdent (owner.getId ++ Name.mkSimple s!"{stem}{index}")

private def fieldName (owner : Ident) (stem : String) : Ident :=
  mkIdent (owner.getId ++ Name.mkSimple stem)

structure BaseBinding where
  affine : Nat
  output : GKRAddress
  recipe : NativeBaseRecipe
  gate : Nat

structure Reflection where
  definitions : Array (TSyntax `term)
  steps : Array (TSyntax `term)
  affineSteps : Array (Option Nat)
  base : Array BaseBinding
  lookupSteps : Array Nat
  productSteps : Array Nat

/-- Partition every actual opcode. Only base arithmetic is absent from the
functional program; its complete relation is certified separately. -/
private def reflect (pair : Import.Pair) (name lookupName productName : Ident) : CommandElabM Reflection := do
  let definitions := LookupSourceData.definitions pair.circuit
  let definitionTerms ← definitions.mapM definitionSyntax
  let memoryCaches := pair.circuit.layers.flatMap fun layer =>
    layer.cached_relations.filterMap fun (address, relation) =>
      match relation with | .MemoryTuple _ => some address | _ => none
  let mut baseOutputs : Array (GKRAddress × Nat) := #[]
  let mut gateIndex := 0
  for layer in pair.circuit.layers do
    for (output, relation) in layer.cached_relations do
      if let .SingleColumnLookup _ _ := relation then
        baseOutputs := baseOutputs.push (output, gateIndex)
        gateIndex := gateIndex + 1
  for layer in pair.circuit.layers do
    for gate in layer.gates ++ layer.gates_with_external_connections do
      match gate.enforced_relation with
      | .LinearBaseFieldRelation _ output | .MaxQuadratic _ _ output |
        .CopyInBaseField _ output | .MaterializeSingleLookupInput _ output _ =>
          baseOutputs := baseOutputs.push (output, gateIndex)
          gateIndex := gateIndex + 1
      | .EnforceSingleMaxQuadraticConstraint _ _ => gateIndex := gateIndex + 1
      | _ => pure ()
  let mut base := #[]
  for (definition, index) in definitions.toList.zipIdx do
    if let some (_, ordinal) := baseOutputs.find? (fun entry => entry.1 == definition.output) then
      let recipe ← match definition.input with
        | .ok (.address address) => pure (AffineProgram.input (R := Nat) address)
        | .ok (.scalar row) => pure (LookupSourceData.baseRecipe row.input)
        | _ => throwError "base affine definition has a non-base native recipe"
      base := base.push ⟨index, definition.output, recipe, ordinal⟩
  let mut steps := #[]
  let mut affineSteps : Array (Option Nat) := definitions.map (fun _ => none)
  let mut cacheIndex := 0
  for layer in pair.circuit.layers do
    for (_, relation) in layer.cached_relations do
      match relation with
      | .SingleColumnLookup _ _ => pure ()
      | _ =>
          affineSteps := affineSteps.set! cacheIndex (some steps.size)
          steps := steps.push (← `(($(memberName name "affine" cacheIndex)).functional))
      cacheIndex := cacheIndex + 1
  let mut lookupSteps := #[]
  let mut productSteps := #[]
  for layer in pair.circuit.layers do
    for gate in layer.gates ++ layer.gates_with_external_connections do
      let relation := gate.enforced_relation
      let operands ← match LookupSourceData.operands relation with
        | .ok operands => pure operands | .error error => throwError "{error}"
      let isLookup := !operands.isEmpty || match relation with
        | .AggregateLookupRationalPair _ _ | .CopyInExtensionField _ _ => true | _ => false
      let productPiece ← NativeProductImport.pieces pair.circuit memoryCaches 0 relation
      let stepIndex := steps.size
      if isLookup then
        steps := steps.push (← `(($(memberName lookupName "gate" lookupSteps.size)).functional))
        lookupSteps := lookupSteps.push stepIndex
      if productPiece.isSome then
        unless isLookup do
          steps := steps.push (← `(($(memberName productName "gate" productSteps.size)).functional))
        productSteps := productSteps.push stepIndex
      match relation with
      | .CopyInExtensionField _ output =>
          let some index := definitions.findIdx? (fun definition => definition.output == output)
            | throwError "extension copy omitted from actual affine definitions"
          affineSteps := affineSteps.set! index (some stepIndex)
      | .MaterializedVectorLookupInput _ output =>
          let some index := definitions.findIdx? (fun definition => definition.output == output)
            | throwError "vector materializer omitted from actual affine definitions"
          affineSteps := affineSteps.set! index (some stepIndex)
          steps := steps.push (← `(($(memberName name "affine" index)).functional))
      | .LinearBaseFieldRelation _ _ | .MaxQuadratic _ _ _ | .EnforceSingleMaxQuadraticConstraint _ _ |
        .CopyInBaseField _ _ | .MaterializeSingleLookupInput _ _ _ => pure ()
      | _ => unless isLookup || productPiece.isSome do
          throwError "actual native opcode has no base or functional semantics"
  for index in [:definitions.size] do
    unless (affineSteps[index]!).isSome || base.any (fun binding => binding.affine == index) do
      throwError "actual affine definition is absent from complete graph semantics"
  return ⟨definitionTerms, steps, affineSteps, base, lookupSteps, productSteps⟩

private def readPair (path : StrLit) : CommandElabM Import.Pair := do
  match Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := Import.Pair)) with
  | .ok pair =>
      unless pair.format_version == 1 do throwError "unsupported functional graph artifact"
      pure pair
  | .error error => throwError "invalid native functional graph: {error}"

syntax (name := importFunctionalGraph) "import_functional_graph " ident " from " str
  " typing " ident " lookup " ident " product " ident " base " ident : command

elab_rules : command
  | `(import_functional_graph $name:ident from $path:str typing $typingName:ident
      lookup $lookupName:ident product $productName:ident base $baseName:ident) => do
    let data ← reflect (← readPair path) name lookupName productName
    let definitions := fieldName name "definitions"
    let mut affineNames := #[]
    for (definition, index) in data.definitions.toList.zipIdx do
      let affine := memberName name "affine" index
      elabCommand (← `(noncomputable def $affine : AffineDefinition := $definition))
      affineNames := affineNames.push (← `($affine))
    elabCommand (← `(noncomputable def $definitions : List AffineDefinition := [$affineNames,*]))
    let isBase := fieldName name "isBase"
    elabCommand (← `(noncomputable def $isBase (address : GKRAddress) : Bool := ($typingName).compatible (address, .base)))
    let known := memberName name "known" 0
    elabCommand (← `(def $known : List GKRAddress := []))
    let mut stepNames := #[]
    for (step, index) in data.steps.toList.zipIdx do
      let stepName := memberName name "step" index
      let previous := memberName name "known" index
      let next := memberName name "known" (index + 1)
      elabCommand (← `(noncomputable def $stepName : FunctionalStep := $step))
      elabCommand (← `(noncomputable def $next : List GKRAddress := ($stepName).outputs ++ $previous))
      stepNames := stepNames.push (← `($stepName))
    let program := fieldName name "program"
    elabCommand (← `(noncomputable def $program : FunctionalProgram := [$stepNames,*]))
    for (binding, index) in data.base.toList.zipIdx do
      let recipe := memberName name "baseRecipe" index
      let output := memberName name "baseOutput" index
      let gate := memberName baseName "gate" binding.gate
      let bank := fieldName baseName "bank"
      let ports := memberName name "basePorts" index
      let relation := memberName name "baseRelation" index
      elabCommand (← `(def $recipe : NativeBaseRecipe := $(← recipeSyntax binding.recipe)))
      elabCommand (← `(def $output : GKRAddress := $(← addressSyntax binding.output)))
      elabCommand (← `(noncomputable def $ports : Bool := ($recipe).portsCheck $bank $isBase $output))
      elabCommand (← `(noncomputable def $relation : Bool := equal (($recipe).relation $bank $output) ($gate).inputResidual))

syntax (name := checkFunctionalGraph) "check_functional_graph " ident " phase " num
  " start " num " stop " num : command

elab_rules : command
  | `(check_functional_graph $name:ident phase $phaseNumber:num start $first:num stop $last:num) => do
    for index in [first.getNat:last.getNat] do
      if phaseNumber.getNat == 0 then
        let step := memberName name "step" index
        let known := memberName name "known" index
        let isBase := fieldName name "isBase"
        let checked := memberName name "stepChecked" index
        elabCommand (← `(theorem $checked : ($step).check $isBase $known = true := by decide +kernel))
      else if phaseNumber.getNat == 1 then
        let ports := memberName name "basePorts" index
        let relation := memberName name "baseRelation" index
        let portsChecked := memberName name "basePortsChecked" index
        let relationChecked := memberName name "baseRelationChecked" index
        elabCommand (← `(theorem $portsChecked : $ports = true := by decide +kernel))
        elabCommand (← `(theorem $relationChecked : $relation = true := by decide +kernel))
      else throwError "unknown native functional graph check phase"

end Airbender.Compiler.FunctionalImport
