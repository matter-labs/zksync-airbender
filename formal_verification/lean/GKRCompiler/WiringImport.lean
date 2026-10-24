import GKRCompiler.Wiring
import GKRCompiler.Import

namespace Airbender.Compiler.WiringImport
open Lean Elab Command
set_option warningAsError true

private def memory (indices : List Nat) : List GKRAddress := indices.map .BaseLayerMemory

private def addressSpaceInputs : CompiledAddressSpaceRelationStrict → List Nat
  | .Constant _ => []
  | .IsRegister index | .IsRam index => [index]

private def addressInputs : CompiledAddressStrict → List Nat
  | .ConstantU16 _ | .Constant _ => []
  | .U16Space index => [index]
  | .U32Space indices => indices.values.toList
  | .U32SpaceSpecialIndirect low dynamic _ high =>
      [low, high] ++ (dynamic.toList.map (·.2))
  | .U32SpaceGeneric terms => terms.values.toList.flatMap fun column =>
      column.1.toList.map (·.2)

private def timestampInputs : CompiledMemoryTimestamp → List Nat
  | .Zero => []
  | .Normal indices => indices.values.toList

private def wordInputs : RamWordRepresentation → List Nat
  | .Zero => []
  | .U16Limbs indices => indices.values.toList
  | .U8Limbs indices => indices.values.toList

private def memoryInputs (relation : SpecialMemoryContributionRelation) : List GKRAddress :=
  memory (addressSpaceInputs relation.address_space ++ addressInputs relation.address ++
    timestampInputs relation.timestamp ++ wordInputs relation.value)

private def linearInputs (relation : LinearRelation) : List GKRAddress :=
  relation.linear_terms.toList.map (·.2)

private def vectorInputs (relation : VectorLookupRelation) : List GKRAddress :=
  relation.columns.toList.flatMap linearInputs

private def quadraticInputs (relation : CompiledMaxQuadraticGKRRelation) : List GKRAddress :=
  relation.quadratic_terms.toList.flatMap (fun (left, terms) => left :: terms.toList.map (·.2)) ++
    relation.linear_terms.toList.map (·.2)

private partial def expressionInputs : StructuredExpression → List GKRAddress
  | .Constant _ => []
  | .Place address => [address]
  | .Sum terms | .Product terms => terms.toList.flatMap expressionInputs

private def initializationInputs : InitsOrTeardownsTimestampAndValue → List GKRAddress
  | .Init => []
  | .Teardown lt lv rt rv => memory (lt.values.toList ++ lv.values.toList ++ rt.values.toList ++ rv.values.toList)

/-- Exhaustive native relation match. A new relation cannot silently contribute
no dependencies; the native unsupported batched constraint is rejected. -/
def relationPorts (layer : Nat) : GKRRelation → Except String GatePorts
  | .LinearBaseFieldRelation input output => pure ⟨layer, linearInputs input, [output]⟩
  | .MaxQuadratic input expression output =>
      pure ⟨layer, quadraticInputs input ++ expressionInputs expression, [output]⟩
  | .EnforceSingleMaxQuadraticConstraint input expression =>
      pure ⟨layer, quadraticInputs input ++ expressionInputs expression, []⟩
  | .EnforceConstraintsMaxQuadratic _ => throw "native batched constraints are unsupported by the consumer"
  | .CopyInBaseField input output | .CopyInExtensionField input output => pure ⟨layer, [input], [output]⟩
  | .InitialGrandProductFromCaches input output | .TrivialProduct input output =>
      pure ⟨layer, input.values.toList, [output]⟩
  | .InitialGrandProductWithoutCaches input output =>
      pure ⟨layer, input.values.toList.flatMap memoryInputs, [output]⟩
  | .UnbalancedGrandProductWithCache scalar input output => pure ⟨layer, [scalar, input], [output]⟩
  | .MaterializeGrandProductTermExpression input output => pure ⟨layer, memoryInputs input, [output]⟩
  | .MaskIntoIdentityProduct input mask output => pure ⟨layer, [input, mask], [output]⟩
  | .MaterializeSingleLookupInput input output _ => pure ⟨layer, linearInputs input.input, [output]⟩
  | .MaterializedVectorLookupInput input output => pure ⟨layer, vectorInputs input, [output]⟩
  | .LookupWithCachedDensAndSetup input setup output =>
      pure ⟨layer, input.values.toList ++ setup.values.toList, output.values.toList⟩
  | .LookupWithDensAndSetupExpressions input setup output =>
      pure ⟨layer, input.1 :: setup.1 :: (vectorInputs input.2 ++ setup.2.toList), output.values.toList⟩
  | .LookupPairFromBaseInputs input output _ =>
      pure ⟨layer, input.values.toList.flatMap (fun input => linearInputs input.input), output.values.toList⟩
  | .LookupPairFromMaterializedBaseInputs input output
  | .LookupPairFromMaterializedVectorInputs input output
  | .LookupPairFromCachedVectorInputs input output => pure ⟨layer, input.values.toList, output.values.toList⟩
  | .LookupFromBaseInputsWithSetup input setup output _ =>
      pure ⟨layer, linearInputs input.input ++ setup.values.toList, output.values.toList⟩
  | .LookupFromMaterializedBaseInputWithSetup input setup output
  | .LookupFromMaterializedVectorInputWithSetup input setup output =>
      pure ⟨layer, input :: setup.values.toList, output.values.toList⟩
  | .LookupUnbalancedPairWithMaterializedBaseInputs input remainder output
  | .LookupUnbalancedPairWithMaterializedVectorInputs input remainder output =>
      pure ⟨layer, remainder :: input.values.toList, output.values.toList⟩
  | .LookupPairFromVectorInputs input output =>
      pure ⟨layer, input.values.toList.flatMap vectorInputs, output.values.toList⟩
  | .LookupFromVectorInputWithSetup input setup output =>
      pure ⟨layer, setup.1 :: (vectorInputs input ++ setup.2.toList), output.values.toList⟩
  | .LookupUnbalancedPairWithVectorInputs input remainder output =>
      pure ⟨layer, input.values.toList ++ vectorInputs remainder, output.values.toList⟩
  | .AggregateLookupRationalPair input output =>
      pure ⟨layer, input.values.toList.flatMap (fun input => input.values.toList), output.values.toList⟩
  | .InitsOrTeardownsInitialPair state setup output _ =>
      pure ⟨layer, initializationInputs state ++ setup.values.toList, [output]⟩

private def cacheInputs : GKRCacheRelation → List GKRAddress
  | .SingleColumnLookup relation _ => linearInputs relation.input
  | .VectorizedLookup relation => vectorInputs relation
  | .MemoryTuple relation => memoryInputs relation
  | .VectorizedLookupSetup setup => setup.toList

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

private def addressesSyntax (addresses : List GKRAddress) : CommandElabM (TSyntax `term) := do
  let entries ← addresses.toArray.mapM addressSyntax
  `([$entries,*])

private def checksSyntax (proofs : Array (TSyntax `ident)) : CommandElabM (TSyntax `term) := do
  let mut result ← `(Compiler.BoolChecks.nil)
  for proof in proofs.reverse do
    result ← `(Compiler.BoolChecks.cons $proof $result)
  return result

syntax (name := importWiring) "import_compiler_wiring " ident " from " str " phase " str " start " num " count " num : command

elab_rules : command
  | `(import_compiler_wiring $name:ident from $path:str phase $mode:str start $offset:num count $length:num) => do
    let mode := mode.getString
    unless ["data", "geometry", "unique", "placement", "gates", "caches", "assemble"].contains mode do
      throwError "unsupported wiring-check phase"
    let first := offset.getNat
    let last := first + length.getNat
    let bytes ← IO.FS.readFile path.getString
    let pair ← match Json.parse bytes >>= (fromJson? (α := Import.Pair)) with
      | .ok pair => pure pair
      | .error error => throwError "invalid native compiler pair: {error}"
    let circuit := pair.circuit
    unless pair.format_version == 1 do throwError "unsupported native pair version"
    let mut widths : Array Nat := #[]
    let mut gateTerms : Array (TSyntax `term) := #[]
    let mut cacheTerms : Array (TSyntax `term) := #[]
    let mut producerPorts : List GKRAddress := []
    for h : index in [:circuit.layers.size] do
      let layer := circuit.layers[index]
      unless layer.layer == index do throwError "native layers are not consecutive"
      if index == 0 then
        unless layer.intermediate_layer_width.isNone do throwError "base layer has an intermediate width"
      else
        let some width := layer.intermediate_layer_width | throwError "missing intermediate width"
        widths := widths.push width
      unless (if index + 1 == circuit.layers.size then layer.gates.isEmpty else layer.gates_with_external_connections.isEmpty) do
        throwError "native external-connection layer is incorrect"
      for gate in layer.gates ++ layer.gates_with_external_connections do
        unless gate.output_layer == index + 1 do throwError "native gate has wrong output-layer tag"
        let ports ← match relationPorts gate.output_layer gate.enforced_relation with
          | .ok ports => pure ports
          | .error error => throwError "{error}"
        producerPorts := producerPorts ++ ports.outputs
        let gateName := mkIdent (name.getId ++ Name.mkSimple s!"gate{gateTerms.size}")
        if mode == "data" then
          elabCommand (← `(noncomputable def $gateName : GatePorts := GatePorts.mk $(quote ports.layer)
            $(← addressesSyntax ports.inputs) $(← addressesSyntax ports.outputs)))
        gateTerms := gateTerms.push (← `($gateName))
      for (address, relation) in layer.cached_relations do
        let cacheName := mkIdent (name.getId ++ Name.mkSimple s!"cache{cacheTerms.size}")
        if mode == "data" then
          elabCommand (← `(noncomputable def $cacheName : CachePorts := CachePorts.mk $(quote index)
            $(← addressesSyntax (cacheInputs relation)) $(← addressSyntax address)))
        cacheTerms := cacheTerms.push (← `($cacheName))
    let mut outputs : List GKRAddress := []
    for (_, ports) in circuit.global_output_map.entries do
      unless ports.size == 2 do throwError "global output must have exactly two ports"
      outputs := outputs ++ ports.toList
    widths := widths.push outputs.length
    let mut placements : Array (TSyntax `term) := #[]
    unless pair.source.layers.size == pair.source.num_variables do throwError "source layers omit variables"
    for index in [:pair.source.num_variables] do
      let [(_, address)] := (circuit.placement_data.entries.filter (·.1 == index)).toList
        | throwError "missing or ambiguous source placement"
      let [(_, layer)] := (pair.source.layers.filter (·.1 == index)).toList
        | throwError "missing or ambiguous source layer"
      placements := placements.push (← `(($(← addressSyntax address), $(quote layer))))
    let scratch ← circuit.scratch_space_mapping.mapM fun (address, index) => do
      `(($(← addressSyntax address), $(quote index)))
    let reverse ← circuit.scratch_space_mapping_rev.entries.mapM fun (index, address) => do
      `(($(quote index), $(← addressSyntax address)))
    let graphName := mkIdent (name.getId ++ `graph)
    for layer in circuit.layers do
      producerPorts := producerPorts ++ layer.cached_relations.toList.map (·.1)
    if mode == "data" then
      elabCommand (← `(noncomputable def $graphName : Wiring :=
        ⟨$(quote circuit.memory_layout.total_width), $(quote circuit.witness_layout.total_width),
         $(quote circuit.generic_lookup_tables_width), $(quote widths.toList),
         [$gateTerms,*], [$cacheTerms,*], $(← addressesSyntax producerPorts), [$placements,*], $(quote circuit.scratch_space_size),
         [$scratch,*], [$reverse,*], $(← addressesSyntax outputs), $(quote pair.cached)⟩))
      return
    let checkedName := mkIdent (name.getId ++ `checked)
    let nonemptyName := mkIdent (name.getId ++ `nonemptyChecked)
    let uniqueName := mkIdent (name.getId ++ `uniqueChecked)
    let tableName := mkIdent (name.getId ++ `producerTableChecked)
    let placementName := mkIdent (name.getId ++ `placementChecked)
    let scratchName := mkIdent (name.getId ++ `scratchChecked)
    let outputsName := mkIdent (name.getId ++ `outputsChecked)
    if mode == "geometry" then
      elabCommand (← `(theorem $nonemptyName : decide (($graphName).widths ≠ []) = true := by decide +kernel))
      elabCommand (← `(theorem $tableName : decide (($graphName).produced = ($graphName).computedProduced) = true := by decide +kernel))
      elabCommand (← `(theorem $scratchName : ($graphName).scratchValid = true := by decide +kernel))
      elabCommand (← `(theorem $outputsName : ($graphName).outputsValid = true := by decide +kernel))
      return
    if mode == "gates" && last > gateTerms.size || mode == "caches" && last > cacheTerms.size ||
        mode == "unique" && last > producerPorts.length || mode == "placement" && last > placements.size then
      throwError "wiring-check shard outside native relation count"
    let mut uniqueProofs := #[]
    for index in [:producerPorts.length] do
      let position ← `(⟨$(quote index), by decide⟩)
      let proof := mkIdent (name.getId ++ Name.mkSimple s!"producerUniqueChecked{index}")
      if mode == "unique" && first ≤ index && index < last then
        elabCommand (← `(theorem $proof : Compiler.distinctAt ($graphName).produced $position = true := by decide +kernel))
      uniqueProofs := uniqueProofs.push proof
    let mut placementProofs := #[]
    for index in [:placements.size] do
      let position ← `(⟨$(quote index), by decide⟩)
      let proof := mkIdent (name.getId ++ Name.mkSimple s!"placementCaseChecked{index}")
      if mode == "placement" && first ≤ index && index < last then
        elabCommand (← `(theorem $proof : ($graphName).placementCase $position = true := by decide +kernel))
      placementProofs := placementProofs.push proof
    let mut gateProofs := #[]
    for index in [:gateTerms.size] do
      let gate := gateTerms[index]!
      let proof := mkIdent (name.getId ++ Name.mkSimple s!"gateChecked{index}")
      if mode == "gates" && first ≤ index && index < last then
        elabCommand (← `(theorem $proof : ($graphName).gateValid $gate = true := by decide +kernel))
      gateProofs := gateProofs.push proof
    let mut cacheProofs := #[]
    for index in [:cacheTerms.size] do
      let cache := cacheTerms[index]!
      let proof := mkIdent (name.getId ++ Name.mkSimple s!"cacheChecked{index}")
      if mode == "caches" && first ≤ index && index < last then
        elabCommand (← `(theorem $proof : ($graphName).cacheValid $cache = true := by decide +kernel))
      cacheProofs := cacheProofs.push proof
    if mode != "assemble" then return
    elabCommand (← `(theorem $uniqueName : ($graphName).uniqueValid = true :=
      Compiler.BoolChecks.all_true $(← checksSyntax uniqueProofs)))
    elabCommand (← `(theorem $placementName : ($graphName).placementValid = true :=
      Compiler.BoolChecks.all_true $(← checksSyntax placementProofs)))
    let gatesName := mkIdent (name.getId ++ `gatesChecked)
    elabCommand (← `(theorem $gatesName : ($graphName).gates.all ($graphName).gateValid = true :=
      Compiler.BoolChecks.all_true $(← checksSyntax gateProofs)))
    let cachesName := mkIdent (name.getId ++ `cachesChecked)
    elabCommand (← `(theorem $cachesName : ($graphName).caches.all ($graphName).cacheValid = true :=
      Compiler.BoolChecks.all_true $(← checksSyntax cacheProofs)))
    elabCommand (← `(theorem $checkedName : ($graphName).check = true :=
      Wiring.assemble (graph := $graphName) $nonemptyName $tableName $uniqueName $gatesName $cachesName $placementName $scratchName $outputsName))
    let soundName := mkIdent (name.getId ++ `sound)
    elabCommand (← `(theorem $soundName : ($graphName).Valid := Wiring.sound (graph := $graphName) $checkedName))

end Airbender.Compiler.WiringImport
