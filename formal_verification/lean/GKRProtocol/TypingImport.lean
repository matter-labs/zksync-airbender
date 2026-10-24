import GKRProtocol.Typing
import GKRCompiler.WiringImport

namespace Airbender.Compiler.TypingImport
open Lean Elab Command
set_option warningAsError true

private def vectorAddresses (row : VectorLookupRelation) : List GKRAddress :=
  row.columns.toList.flatMap (fun column => column.linear_terms.toList.map (·.2))

private def memoryAddresses (row : SpecialMemoryContributionRelation) : Except String (List GKRAddress) := do
  let ports ← WiringImport.relationPorts 0 (.MaterializeGrandProductTermExpression row (.InnerLayer 1 0))
  return ports.inputs

private def scalarAddresses (row : SingleColumnLookupRelation) : List GKRAddress :=
  row.input.linear_terms.toList.map (·.2)

private def consumerGroups : GKRRelation → Except String (List (List GKRAddress))
  | .MaterializedVectorLookupInput row _ => pure [vectorAddresses row]
  | .LookupWithDensAndSetupExpressions input setup _ => pure [vectorAddresses input.2, setup.2.toList]
  | .LookupPairFromVectorInputs input _ => pure (input.values.toList.map vectorAddresses)
  | .LookupFromVectorInputWithSetup input setup _ => pure [vectorAddresses input, setup.2.toList]
  | .LookupUnbalancedPairWithVectorInputs _ remainder _ => pure [vectorAddresses remainder]
  | .MaterializeSingleLookupInput row _ _ => pure [scalarAddresses row]
  | .LookupPairFromBaseInputs input _ _ => pure (input.values.toList.map scalarAddresses)
  | .LookupFromBaseInputsWithSetup input _ _ _ => pure [scalarAddresses input]
  | .MaterializeGrandProductTermExpression row _ => do return [← memoryAddresses row]
  | .InitialGrandProductWithoutCaches input _ => input.values.toList.mapM memoryAddresses
  | .InitsOrTeardownsInitialPair state setup _ _ =>
      match state with
      | .Init => pure [setup.values.toList]
      | .Teardown lt lv rt rv => pure
          [(lt.values.toList ++ lv.values.toList).map .BaseLayerMemory ++ setup.values.toList,
           (rt.values.toList ++ rv.values.toList).map .BaseLayerMemory ++ setup.values.toList]
  | _ => pure []

/-- Field roles match native helper input/output categories. Every relation
constructor is explicit; obsolete unsupported consumer variants fail closed. -/
private def gateKinds (relation : GKRRelation) (ports : GatePorts) :
    Except String (List WireKind × List WireKind) := do
  let bases := List.replicate ports.inputs.length WireKind.base
  let extensions := List.replicate ports.inputs.length WireKind.extension
  let baseOutputs := List.replicate ports.outputs.length WireKind.base
  let extensionOutputs := List.replicate ports.outputs.length WireKind.extension
  match relation with
  | .LinearBaseFieldRelation _ _ | .MaxQuadratic _ _ _ |
      .EnforceSingleMaxQuadraticConstraint _ _ | .CopyInBaseField _ _ |
      .MaterializeSingleLookupInput _ _ _ => return (bases, baseOutputs)
  | .CopyInExtensionField _ _ | .InitialGrandProductFromCaches _ _ |
      .TrivialProduct _ _ | .LookupPairFromMaterializedVectorInputs _ _ |
      .LookupUnbalancedPairWithMaterializedVectorInputs _ _ _ |
      .AggregateLookupRationalPair _ _ => return (extensions, extensionOutputs)
  | .InitialGrandProductWithoutCaches _ _ | .MaterializeGrandProductTermExpression _ _ |
      .MaterializedVectorLookupInput _ _ | .LookupWithDensAndSetupExpressions _ _ _ |
      .LookupPairFromBaseInputs _ _ _ | .LookupPairFromMaterializedBaseInputs _ _ |
      .LookupFromBaseInputsWithSetup _ _ _ _ | .LookupFromMaterializedBaseInputWithSetup _ _ _ |
      .LookupPairFromVectorInputs _ _ | .LookupFromVectorInputWithSetup _ _ _ |
      .InitsOrTeardownsInitialPair _ _ _ _ => return (bases, extensionOutputs)
  | .MaskIntoIdentityProduct _ _ _ => return ([.extension, .base], extensionOutputs)
  | .LookupWithCachedDensAndSetup _ _ _ => return ([.base, .extension, .base, .extension], extensionOutputs)
  | .LookupUnbalancedPairWithMaterializedBaseInputs _ _ _ => return ([.base, .extension, .extension], extensionOutputs)
  | .LookupFromMaterializedVectorInputWithSetup _ _ _ => return ([.extension, .base, .extension], extensionOutputs)
  | .LookupUnbalancedPairWithVectorInputs _ _ _ =>
      return ([.extension, .extension] ++ List.replicate (ports.inputs.length - 2) .base, extensionOutputs)
  | .EnforceConstraintsMaxQuadratic _ => throw "retired batched arithmetic consumer"
  | .UnbalancedGrandProductWithCache _ _ _ => throw "unsupported retired unbalanced product consumer"
  | .LookupPairFromCachedVectorInputs _ _ => throw "unsupported retired vector lookup consumer"

private def kindSyntax : WireKind → CommandElabM (TSyntax `term)
  | .base => `(WireKind.base)
  | .extension => `(WireKind.extension)

private def kindsSyntax (kinds : List WireKind) : CommandElabM (TSyntax `term) := do
  let terms ← kinds.toArray.mapM kindSyntax
  `([$terms,*])

private def addressSyntax : GKRAddress → CommandElabM (TSyntax `term)
  | .BaseLayerMemory index => `(GKRAddress.BaseLayerMemory $(quote index))
  | .BaseLayerWitness index => `(GKRAddress.BaseLayerWitness $(quote index))
  | .InnerLayer layer offset => `(GKRAddress.InnerLayer $(quote layer) $(quote offset))
  | .Cached layer offset => `(GKRAddress.Cached $(quote layer) $(quote offset))
  | .Setup index => `(GKRAddress.Setup $(quote index))
  | .ScratchSpace index => `(GKRAddress.ScratchSpace $(quote index))
  | .VirtualSetup kind => do
      let kind ← match kind with
        | .RangeCheck16Bits => `(VirtualSetupPoly.RangeCheck16Bits)
        | .RangeCheckTimestamp => `(VirtualSetupPoly.RangeCheckTimestamp)
        | .InitsAndTeardownsLow => `(VirtualSetupPoly.InitsAndTeardownsLow)
        | .InitsAndTeardownsHigh => `(VirtualSetupPoly.InitsAndTeardownsHigh)
      `(GKRAddress.VirtualSetup $kind)

private def groupsSyntax (groups : List (List GKRAddress)) : CommandElabM (TSyntax `term) := do
  let groups ← groups.toArray.mapM fun group => do
    let entries ← group.toArray.mapM addressSyntax
    `([$entries,*])
  `([$groups,*])

private def checksSyntax (proofs : Array (TSyntax `ident)) : CommandElabM (TSyntax `term) := do
  let mut result ← `(Compiler.BoolChecks.nil)
  for proof in proofs.reverse do result ← `(Compiler.BoolChecks.cons $proof $result)
  return result

syntax (name := importConsumerTyping) "import_compiler_typing " ident " from " str " wiring " ident : command

elab_rules : command
  | `(import_compiler_typing $name:ident from $path:str wiring $wiringName:ident) => do
    let pair ← match Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := Import.Pair)) with
      | .ok pair => pure pair
      | .error error => throwError "invalid compiler artifact for consumer typing: {error}"
    let graphName := mkIdent (wiringName.getId ++ `graph)
    let mut nodeNames : Array (TSyntax `term) := #[]
    let mut declarations : Array (TSyntax `term) := #[]
    let mut gateIndex := 0
    let mut cacheIndex := 0
    for layer in pair.circuit.layers do
      for gate in layer.gates ++ layer.gates_with_external_connections do
        let ports ← match WiringImport.relationPorts gate.output_layer gate.enforced_relation with
          | .ok ports => pure ports
          | .error error => throwError "{error}"
        let (inputKinds, outputKinds) ← match gateKinds gate.enforced_relation ports with
          | .ok roles => pure roles
          | .error error => throwError "{error}"
        unless inputKinds.length == ports.inputs.length && outputKinds.length == ports.outputs.length do
          throwError "consumer field-role arity differs from actual native ports"
        let raw := mkIdent (wiringName.getId ++ Name.mkSimple s!"gate{gateIndex}")
        let groups ← match consumerGroups gate.enforced_relation with
          | .ok groups => pure groups
          | .error error => throwError "{error}"
        let node := mkIdent (name.getId ++ Name.mkSimple s!"node{nodeNames.size}")
        elabCommand (← `(noncomputable def $node : ConsumerNode :=
          ⟨($raw).inputs, ($raw).outputs, ($raw).inputs.zip $(← kindsSyntax inputKinds),
            ($raw).outputs.zip $(← kindsSyntax outputKinds), $(← groupsSyntax groups)⟩))
        nodeNames := nodeNames.push (← `($node))
        declarations := declarations.push (← `(($node).outputs))
        gateIndex := gateIndex + 1
    for layer in pair.circuit.layers do
      for (_, relation) in layer.cached_relations do
        let raw := mkIdent (wiringName.getId ++ Name.mkSimple s!"cache{cacheIndex}")
        let outputKind := match relation with | .SingleColumnLookup _ _ => WireKind.base | _ => .extension
        let groups ← match relation with
          | .SingleColumnLookup row _ => pure [scalarAddresses row]
          | .MemoryTuple row =>
              match memoryAddresses row with
              | .ok addresses => pure [addresses]
              | .error error => throwError "{error}"
          | .VectorizedLookup row => pure [vectorAddresses row]
          | .VectorizedLookupSetup addresses => pure [addresses.toList]
        let node := mkIdent (name.getId ++ Name.mkSimple s!"node{nodeNames.size}")
        elabCommand (← `(noncomputable def $node : ConsumerNode :=
          ⟨($raw).inputs, [($raw).output], ($raw).inputs.map (fun address => (address, WireKind.base)),
            [(($raw).output, $(← kindSyntax outputKind))], $(← groupsSyntax groups)⟩))
        nodeNames := nodeNames.push (← `($node))
        declarations := declarations.push (← `(($node).outputs))
        cacheIndex := cacheIndex + 1
    let typingName := mkIdent (name.getId ++ `typing)
    elabCommand (← `(noncomputable def $typingName : ConsumerTyping :=
      ⟨$graphName, List.flatten [$declarations,*], [$nodeNames,*]⟩))
    let mut proofs := #[]
    for index in [:nodeNames.size] do
      let node := nodeNames[index]!
      let proof := mkIdent (name.getId ++ Name.mkSimple s!"nodeChecked{index}")
      elabCommand (← `(theorem $proof : ($typingName).nodeValid $node = true := by decide +kernel))
      proofs := proofs.push proof
    let ports := mkIdent (name.getId ++ `portsChecked)
    elabCommand (← `(theorem $ports : decide (($typingName).declarations.map Prod.fst = ($typingName).graph.produced) = true := by decide +kernel))
    let declared := mkIdent (name.getId ++ `declarationsChecked)
    elabCommand (← `(theorem $declared : decide (($typingName).nodes.flatMap ConsumerNode.outputs = ($typingName).declarations) = true := by decide +kernel))
    let sources := mkIdent (name.getId ++ `sourcesChecked)
    let consumers := mkIdent (name.getId ++ `consumersChecked)
    elabCommand (← `(theorem $consumers : ($typingName).consumersValid = true := by decide +kernel))
    elabCommand (← `(theorem $sources : ($typingName).sourceValid = true := by decide +kernel))
    let outputs := mkIdent (name.getId ++ `outputsChecked)
    elabCommand (← `(theorem $outputs : ($typingName).outputsValid = true := by decide +kernel))
    let nodes := mkIdent (name.getId ++ `nodesChecked)
    elabCommand (← `(theorem $nodes : ($typingName).nodes.all ($typingName).nodeValid = true :=
      Compiler.BoolChecks.all_true $(← checksSyntax proofs)))
    let checked := mkIdent (name.getId ++ `checked)
    elabCommand (← `(theorem $checked : ($typingName).check = true :=
      ConsumerTyping.assemble $ports $declared $consumers $nodes $sources $outputs))
    let wiringProof := mkIdent (wiringName.getId ++ `sound)
    let sound := mkIdent (name.getId ++ `sound)
    elabCommand (← `(theorem $sound : ($typingName).Valid := ConsumerTyping.sound $wiringProof $checked))

end Airbender.Compiler.TypingImport
