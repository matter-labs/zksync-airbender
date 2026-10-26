import Airbender.Proofs.GKRProtocol.TableLayout
import Airbender.Import.GKRProtocol.LookupSourceData

namespace Airbender.Compiler.TableImport
open Lean Elab Command
set_option warningAsError true

private def sourceWidth (source : Source.SemanticInputs) : Nat × Bool := Id.run do
  let requests := Source.genericRequests source
  let decoderWidth := (source.executor_machine_state.map fun state =>
    (Source.decoderFields state source.circuit_family_bitmask.toList).length).getD 0
  let queryWidth := requests.foldl (fun result query => max result query.row.size) 0
  let sameTable := match requests with
    | [] => true
    | first :: rest => match first.table with
      | .Constant table => rest.all fun query => match query.table with
        | .Constant other => decide (table = other)
        | _ => false
      | _ => false
  let includeIDs := (!requests.isEmpty && source.executor_machine_state.isSome) || !sameTable
  return (max decoderWidth queryWidth + if includeIDs then 1 else 0, includeIDs)

private def addressSyntax : GKRAddress → CommandElabM (TSyntax `term)
  | .BaseLayerWitness index => `(GKRAddress.BaseLayerWitness $(quote index))
  | _ => throwError "lookup multiplicity is not in its declared witness column"

syntax (name := importSourceTableLayout) "import_source_table_layout " ident " from " str
  " source " str " source_lookups " ident " native_model " ident " roles " ident : command

elab_rules : command
  | `(import_source_table_layout $name:ident from $pairPath:str source $sourcePath:str
      source_lookups $sourcePrefix:ident native_model $nativePrefix:ident roles $rolesName:ident) => do
    let pairJson ← match Json.parse (← IO.FS.readFile pairPath.getString) with
      | .ok parsed => pure parsed | .error error => throwError "{error}"
    let sourceJson ← match Json.parse (← IO.FS.readFile sourcePath.getString) with
      | .ok parsed => pure parsed | .error error => throwError "{error}"
    let pair ← match fromJson? (α := Import.Pair) pairJson with
      | .ok parsed => pure parsed | .error error => throwError "{error}"
    let snapshot ← match fromJson? (α := Source.Snapshot) sourceJson with
      | .ok parsed => pure parsed | .error error => throwError "{error}"
    let .ok originalSource := pairJson.getObjVal? "source" | throwError "missing original compiler input"
    let .ok retainedSource := sourceJson.getObjVal? "source" | throwError "missing retained compiler input"
    unless pair.format_version == 1 && snapshot.format_version == 1 && pair.family == snapshot.family &&
        pair.cached == snapshot.cached && originalSource == retainedSource do
      throwError "source table capture is detached from its actual compilation"
    let (width, includeIDs) := sourceWidth snapshot.semantic_inputs
    let sizes : Array (TSyntax `term) := snapshot.semantic_inputs.table_sizes.map quote
    let decoderWords := if snapshot.semantic_inputs.executor_machine_state.isSome then
      snapshot.configuration.max_bytecode_size_in_words else 0
    let plan := mkIdent (name.getId ++ `sourcePlan)
    let layout := mkIdent (name.getId ++ `nativeLayout)
    let layoutChecked := mkIdent (name.getId ++ `tableLayoutPreserved)
    let totalChecked := mkIdent (name.getId ++ `sourceTableTotal)
    elabCommand (← `(def $plan : SourceTablePlan :=
      ⟨[$sizes,*], $(quote decoderWords), $(quote snapshot.configuration.trace_len_log2),
        $(quote width), $(quote includeIDs)⟩))
    let offsets : Array (TSyntax `term) := pair.circuit.table_offsets.map (fun offset => quote offset.val)
    elabCommand (← `(def $layout : LookupTableLayout :=
      ⟨[$offsets,*], $(quote pair.circuit.offset_for_decoder_table), $(quote pair.circuit.total_tables_size),
        $(quote pair.circuit.trace_len), $(quote pair.circuit.generic_lookup_tables_width),
        $(quote pair.circuit.tables_ids_in_generic_lookups)⟩))
    elabCommand (← `(theorem $layoutChecked : $layout = ($plan).layout := by decide +kernel))
    elabCommand (← `(theorem $totalChecked : ($plan).sizes.sum = $(quote snapshot.semantic_inputs.total_tables_len) := by decide +kernel))
    let countColumns : Array (TSyntax `term) := pair.circuit.global_output_map.entries.filterMap fun (kind, _) => match kind with
      | .GenericLookup => some (quote pair.circuit.witness_layout.multiplicities_columns_for_generic_lookup.start)
      | .Lookup16Bits => some (quote pair.circuit.witness_layout.multiplicities_columns_for_range_check_16.start)
      | .LookupTimestamps => some (quote pair.circuit.witness_layout.multiplicities_columns_for_timestamp_range_check.start)
      | _ => none
    let columnBank := mkIdent (name.getId ++ `multiplicityColumns)
    let disjoint := mkIdent (name.getId ++ `multiplicitiesDisjoint)
    elabCommand (← `(def $columnBank : List Nat := [$countColumns,*]))
    elabCommand (← `(theorem $disjoint : ($columnBank).eraseDups.length = ($columnBank).length := by decide +kernel))
    let registry := mkIdent (nativePrefix.getId ++ `registry)
    let definitionsName := mkIdent (sourcePrefix.getId ++ `definitions)
    let mut operands : Array LookupSourceData.Operand := #[]
    for layer in pair.circuit.layers do
      for gate in layer.gates ++ layer.gates_with_external_connections do
        match LookupSourceData.operands gate.enforced_relation with
        | .ok actual => operands := operands ++ actual
        | .error error => throwError "{error}"
    for (kind, _) in pair.circuit.global_output_map.entries do
      let some (stem, multiplicities) := (match kind with
        | .GenericLookup => some ("generic", pair.circuit.witness_layout.multiplicities_columns_for_generic_lookup)
        | .Lookup16Bits => some ("range16", pair.circuit.witness_layout.multiplicities_columns_for_range_check_16)
        | .LookupTimestamps => some ("timestamp", pair.circuit.witness_layout.multiplicities_columns_for_timestamp_range_check)
        | _ => none) | continue
      unless multiplicities.end == multiplicities.start + 1 do throwError "source table requires exactly one multiplicity column"
      let multiplicityAddress : GKRAddress := .BaseLayerWitness multiplicities.start
      let candidates := (operands.zipIdx).filter fun (operand, _) => match operand.weight with
        | .negativeMultiplicity address => address == multiplicityAddress
        | _ => false
      let [(actual, nativeIndex)] := candidates.toList | throwError "source table does not select a unique actual setup leaf"
      let leaf := mkIdent (sourcePrefix.getId ++ Name.mkSimple s!"leaf{nativeIndex}")
      let encoding := mkIdent (sourcePrefix.getId ++ Name.mkSimple s!"encoding{nativeIndex}")
      let expanded := mkIdent (sourcePrefix.getId ++ Name.mkSimple s!"expanded{nativeIndex}")
      let baseChecked := mkIdent (sourcePrefix.getId ++ Name.mkSimple s!"baseChecked{nativeIndex}")
      let found := mkIdent (sourcePrefix.getId ++ Name.mkSimple s!"leafFound{nativeIndex}")
      let actualDefinitions := LookupSourceData.definitions pair.circuit
      let mut input := actual.input
      let mut indices : Array (TSyntax `term) := #[]
      for _ in [:actualDefinitions.size] do
        let .address address := input | break
        let some index := actualDefinitions.findIdx? (fun definition => definition.output == address) | break
        let some definition := actualDefinitions[index]? | throwError "actual setup definition index changed"
        indices := indices.push (quote index)
        input ← match definition.input with
          | .ok resolved => pure resolved | .error error => throwError "{error}"
      let columnsName := mkIdent (name.getId ++ Name.mkSimple s!"{stem}SetupColumns")
      let mut columns : Array (TSyntax `term) := #[]
      match kind with
      | .GenericLookup => for column in [:width] do columns := columns.push (← `(SourceSetupColumn.generic $(quote column)))
      | .Lookup16Bits => columns := #[← `(SourceSetupColumn.range16)]
      | .LookupTimestamps => columns := #[← `(SourceSetupColumn.timestamp)]
      | _ => throwError "unexpected source setup kind"
      elabCommand (← `(def $columnsName : List SourceSetupColumn := [$columns,*]))
      let columnsChecked := mkIdent (name.getId ++ Name.mkSimple s!"{stem}SetupColumnsPreserved")
      elabCommand (← `(theorem $columnsChecked : ($encoding).columns =
        ($columnsName).map (fun column => AffineProgram.input column.address) := by rfl))
      let countRole := mkIdent (name.getId ++ Name.mkSimple s!"{stem}MultiplicityBase")
      elabCommand (← `(theorem $countRole : ($rolesName).compatible ($(← addressSyntax multiplicityAddress), .base) = true := by decide +kernel))
      let bankName := mkIdent (sourcePrefix.getId ++ `bank)
      let placementName := mkIdent (nativePrefix.getId ++ `sourcePlacement)
      let countFresh := mkIdent (name.getId ++ Name.mkSimple s!"{stem}MultiplicityFresh")
      elabCommand (← `(theorem $countFresh :
        (List.range $(quote pair.source.num_variables)).all (fun index =>
          !addressEqual (($bankName).address ($placementName index)) $(← addressSyntax multiplicityAddress)) = true := by decide +kernel))
      let interpreted := mkIdent (name.getId ++ Name.mkSimple s!"{stem}SetupInterpreted")
      elabCommand (← `(theorem $interpreted {R : Type} [CommRing R]
        (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
        (assignment : TypedAssignment R)
        (defined : ∀ definition ∈ $definitionsName, definition.Holds hom challenges (assignment.value $rolesName hom))
        (table : SourceSetupColumn → Source.BaseField) (multiplicity : Source.BaseField)
        (tableCells : ∀ column ∈ $columnsName, assignment.base column.address = table column)
        (countCell : assignment.base $(← addressSyntax multiplicityAddress) = multiplicity) :
        NativeLookupLeaf.registryValue $registry hom challenges gamma (assignment.value $rolesName hom) $(quote nativeIndex) =
          (SourceLookupSetupRow.mk (($columnsName).map table) multiplicity).value hom challenges.lookupAlpha gamma :=
        (NativeLookupLeaf.registryValue_at $found hom challenges gamma (assignment.value $rolesName hom)).trans
          (NativeLookupLeaf.source_setup $leaf $encoding $rolesName $baseChecked $definitionsName [$indices,*]
            $expanded assignment hom challenges gamma defined _
            (NativeLookupEncoding.source_setup_fields $encoding $columnsName $columnsChecked assignment.base table tableCells)
            (congrArg Neg.neg ((TypedAssignment.value_base assignment $rolesName hom $countRole).trans (congrArg hom countCell))))))
      if let .LookupTimestamps := kind then continue
      let sourceReduction := mkIdent (sourcePrefix.getId ++ Name.mkSimple s!"{stem}SourceReduction")
      let sourceQueries := mkIdent (sourcePrefix.getId ++ Name.mkSimple s!"{stem}Queries")
      let output := mkIdent (nativePrefix.getId ++ Name.mkSimple s!"{stem}Output")
      let nativeGates := mkIdent (nativePrefix.getId ++ `gates)
      let copies := mkIdent (nativePrefix.getId ++ `copyRelations)
      let sourcePlacement := mkIdent (nativePrefix.getId ++ `sourcePlacement)
      let bank := mkIdent (sourcePrefix.getId ++ `bank)
      let result := mkIdent (name.getId ++ Name.mkSimple s!"{stem}SourceTableReduction")
      elabCommand (← `(theorem $result {R : Type} [CommRing R]
        (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
        (assignment : TypedAssignment R)
        (defined : ∀ definition ∈ $definitionsName, definition.Holds hom challenges (assignment.value $rolesName hom))
        (baseCopies : Satisfies $copies (assignment.base ∘ ($bank).address))
        (holds : ∀ gate ∈ $nativeGates, gate.Holds hom challenges gamma (assignment.value $rolesName hom))
        (table : SourceSetupColumn → Source.BaseField) (multiplicity : Source.BaseField)
        (tableCells : ∀ column ∈ $columnsName, assignment.base column.address = table column)
        (countCell : assignment.base $(← addressSyntax multiplicityAddress) = multiplicity) :
        ($output).value (assignment.value $rolesName hom) =
          ((($sourceQueries).map (fun query => query.value hom challenges.lookupAlpha gamma
            ((assignment.base ∘ ($bank).address) ∘ $sourcePlacement))) ++
            [(SourceLookupSetupRow.mk (($columnsName).map table) multiplicity).value hom challenges.lookupAlpha gamma]).sum := by
        have translated := $sourceReduction hom challenges gamma assignment defined baseCopies holds
        change ($output).value (assignment.value $rolesName hom) =
          ((($sourceQueries).map (fun query => query.value hom challenges.lookupAlpha gamma
            ((assignment.base ∘ ($bank).address) ∘ $sourcePlacement))) ++
            [NativeLookupLeaf.registryValue $registry hom challenges gamma (assignment.value $rolesName hom) $(quote nativeIndex)]).sum at translated
        rw [$(← `(term| $interpreted hom challenges gamma assignment defined table multiplicity tableCells countCell)):term] at translated
        exact translated))

end Airbender.Compiler.TableImport
