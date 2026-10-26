import Airbender.Import.GKRProtocol.LookupSourceData
import Airbender.Import.GKRProtocol.LookupImport
import Airbender.Import.GKRProtocol.CacheImport
import Airbender.Proofs.GKRProtocol.LookupSourceSemantics

namespace Airbender.Compiler.LookupSourceImport
open Lean Elab Command
set_option warningAsError true

private instance : ObjectKey String where
  decode := Except.ok
  encode := id

structure OperandCertificate where
  native_leaf : Nat
  locator : Fixed 2 Nat
  expansion : Array Nat
  group : String
  kind : String
  source_row : Option Nat
  fields : Array Import.EncodedCombination
  deriving FromJson

structure GroupCertificate where
  native_leaves : Array Nat
  source_labels : Array Nat
  deriving FromJson

structure Certificate where
  format_version : Nat
  operands : Array OperandCertificate
  groups : ObjectMap String GroupCertificate
  deriving FromJson

private def addressSyntax : GKRAddress → CommandElabM (TSyntax `term)
  | .BaseLayerWitness index => `(GKRAddress.BaseLayerWitness $(quote index))
  | .BaseLayerMemory index => `(GKRAddress.BaseLayerMemory $(quote index))
  | .InnerLayer layer index => `(GKRAddress.InnerLayer $(quote layer) $(quote index))
  | .Cached layer index => `(GKRAddress.Cached $(quote layer) $(quote index))
  | .Setup index => `(GKRAddress.Setup $(quote index))
  | .ScratchSpace _ => throwError "actual source lookup operand contains ScratchSpace"
  | .VirtualSetup kind => do
      let kind ← match kind with
        | .RangeCheck16Bits => `(VirtualSetupPoly.RangeCheck16Bits)
        | .RangeCheckTimestamp => `(VirtualSetupPoly.RangeCheckTimestamp)
        | .InitsAndTeardownsLow => `(VirtualSetupPoly.InitsAndTeardownsLow)
        | .InitsAndTeardownsHigh => `(VirtualSetupPoly.InitsAndTeardownsHigh)
      `(GKRAddress.VirtualSetup $kind)

private def inputSyntax : LookupSourceData.Input → CommandElabM (TSyntax `term)
  | .address address => do `(AffineProgram.input (R := CacheCoefficient) $(← addressSyntax address))
  | .scalar row => CacheImport.program (.SingleColumnLookup row 0)
  | .vector row => CacheImport.program (.VectorizedLookup row)
  | .setup addresses => CacheImport.program (.VectorizedLookupSetup addresses)

private def weightSyntax : LookupWeight → CommandElabM (TSyntax `term)
  | .one => `(LookupWeight.one)
  | .column address => do `(LookupWeight.column $(← addressSyntax address))
  | .negativeMultiplicity address => do `(LookupWeight.negativeMultiplicity $(← addressSyntax address))

private def definitionSyntax (definition : LookupSourceData.Definition) : CommandElabM (TSyntax `term) := do
  let program ← match definition with
    | .cache _ relation => CacheImport.program relation
    | .copy _ address => inputSyntax (.address address)
    | .scalar _ row => inputSyntax (.scalar row)
    | .vector _ row => inputSyntax (.vector row)
  `(AffineDefinition.mk $(← addressSyntax definition.output) $program)

private def recipeSyntax : NativeBaseRecipe → CommandElabM (TSyntax `term)
  | .constant scalar => `(AffineProgram.constant (Address := GKRAddress) (R := Nat) $(quote scalar))
  | .input address => do `(AffineProgram.input (R := Nat) $(← addressSyntax address))
  | .add left right => do `(AffineProgram.add $(← recipeSyntax left) $(← recipeSyntax right))
  | .scale coefficient inner => do `(AffineProgram.scale $(quote coefficient) $(← recipeSyntax inner))

private def finSyntax (index bound : Nat) : CommandElabM (TSyntax `term) := do
  unless index < bound do throwError "source operand certificate index outside its actual bank"
  `(⟨$(quote index), by decide⟩)

private def combinationSyntax (arity length : Nat) (witness : Import.EncodedCombination) :
    CommandElabM (TSyntax `term) := do
  let entries ← witness.mapM fun (polynomial, relation) => do
    let terms ← polynomial.mapM fun (coefficient, monomial) => do
      unless coefficient < babyBearModulus do throwError "noncanonical source-column witness coefficient"
      let indices ← monomial.mapM fun index => finSyntax index arity
      `((($(quote coefficient) : Source.BaseField), [$indices,*]))
    `(([$terms,*], $(← finSyntax relation length)))
  `([$entries,*])

private def listEquality (proofs : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let mut result ← `(rfl)
  for proof in proofs.reverse do result ← `(congrArg₂ List.cons $proof $result)
  return result

private def predicateChecks (proofs : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let mut result ← `(PredicateChecks.nil)
  for proof in proofs.reverse do result ← `(PredicateChecks.cons $proof $result)
  return result

syntax (name := importSourceLookups) "import_source_lookups " ident " from " str
  " certificate " str " selectors " str " reference " ident " typing " ident
  " phase " num " start " num " stop " num : command

elab_rules : command
  | `(import_source_lookups $name:ident from $pairPath:str certificate $oldPath:str
      selectors $selectorText:str reference $referenceName:ident typing $typingName:ident
      phase $phaseNumber:num start $startNumber:num stop $stopNumber:num) => do
    let phaseIndex := phaseNumber.getNat
    unless phaseIndex ≤ 3 do throwError "unsupported source lookup import phase"
    let pair ← match Json.parse (← IO.FS.readFile pairPath.getString) >>= (fromJson? (α := Import.Pair)) with
      | .ok pair => pure pair
      | .error error => throwError "invalid actual source-lookup pair: {error}"
    let previous ← match Json.parse (← IO.FS.readFile oldPath.getString) >>= (fromJson? (α := LookupImport.LookupCertificate)) with
      | .ok previous => pure previous
      | .error error => throwError "invalid original source-column certificate: {error}"
    let cert ← match Json.parse selectorText.getString >>= (fromJson? (α := Certificate)) with
      | .ok parsed => pure parsed
      | .error error => throwError "invalid source-operand selectors: {error}"
    unless pair.format_version == 1 && previous.format_version == 1 && cert.format_version == 1 do
      throwError "unsupported source-operand certificate version"
    let expectedGroups := pair.circuit.global_output_map.entries.filterMap fun (kind, _) => match kind with
      | .GenericLookup => some "GenericLookup"
      | .Lookup16Bits => some "Lookup16Bits"
      | .LookupTimestamps => some "LookupTimestamps"
      | _ => none
    unless cert.groups.entries.size == expectedGroups.size && expectedGroups.all (fun group =>
        cert.groups.entries.any (fun entry => entry.1 == group)) do
      throwError "source lookup output group coverage changed"
    let arity := previous.addresses.size
    unless arity > 0 do throwError "source operand bank is empty"
    let gates := pair.circuit.layers.flatMap (fun layer => layer.gates ++ layer.gates_with_external_connections)
    let actualDefinitions := LookupSourceData.definitions pair.circuit
    let definitionsName := mkIdent (name.getId ++ `definitions)
    let definitions ← actualDefinitions.mapM definitionSyntax
    let addressesName := mkIdent (name.getId ++ `addresses)
    let addressTerms ← previous.addresses.mapM addressSyntax
    let placement := mkIdent (name.getId ++ `wirePlacement)
    let bank := mkIdent (name.getId ++ `bank)
    if phaseIndex == 0 || phaseIndex == 3 then
      elabCommand (← `(noncomputable def $definitionsName : List AffineDefinition := [$definitions,*]))
      elabCommand (← `(noncomputable def $addressesName : List GKRAddress := [$addressTerms,*]))
      elabCommand (← `(noncomputable def $placement (address : GKRAddress) : Fin $(quote arity) :=
        let index := ($addressesName).findIdx (fun candidate => addressEqual candidate address)
        if bound : index < $(quote arity) then ⟨index, bound⟩ else ⟨0, by decide⟩))
      elabCommand (← `(noncomputable def $bank : WireBank $(quote arity) :=
        ⟨fun index => (($addressesName)[index.val]?).getD (.BaseLayerWitness 0), $placement⟩))
    let copyRelations := mkIdent (referenceName.getId ++ `copyRelations)
    let sourcePlacement := mkIdent (referenceName.getId ++ `sourcePlacement)
    let registry := mkIdent (referenceName.getId ++ `registry)
    let relationCount := pair.circuit.layers.foldl (fun total layer => total +
      ((layer.gates ++ layer.gates_with_external_connections).filter (fun gate => match gate.enforced_relation with
        | .CopyInBaseField _ _ => true | _ => false)).size) 0
    let selectedOperands := if phaseIndex == 1 || phaseIndex == 3 then
      cert.operands.extract startNumber.getNat stopNumber.getNat else #[]
    for operand in selectedOperands do
      let [gateIndex, operandIndex] := operand.locator.values.toList | throwError "invalid operand locator width"
      let some gate := gates[gateIndex]? | throwError "actual operand gate selector outside list"
      let operands ← match LookupSourceData.operands gate.enforced_relation with
        | .ok values => pure values
        | .error error => throwError "{error}"
      let some actual := operands[operandIndex]? | throwError "actual operand selector outside gate"
      let final ← match LookupSourceData.head actualDefinitions operand.expansion.toList actual.input with
        | .ok input => pure input
        | .error error => throwError "{error}"
      let actualEncoding := LookupSourceData.encoding final
      let leafName := mkIdent (name.getId ++ Name.mkSimple s!"leaf{operand.native_leaf}")
      elabCommand (← `(noncomputable def $leafName : NativeLookupLeaf :=
        ⟨$(← weightSyntax actual.weight), $(← inputSyntax actual.input)⟩))
      let found := mkIdent (name.getId ++ Name.mkSimple s!"leafFound{operand.native_leaf}")
      elabCommand (← `(theorem $found : ($registry)[$(quote operand.native_leaf)]? = some $leafName := by rfl))
      let mut recipes : Array (TSyntax `term) := #[]
      for recipe in actualEncoding.columns do
        recipes := recipes.push (← recipeSyntax recipe)
      let encoding := mkIdent (name.getId ++ Name.mkSimple s!"encoding{operand.native_leaf}")
      match actualEncoding with
      | .scalar recipe => elabCommand (← `(noncomputable def $encoding : NativeLookupEncoding := .scalar $(← recipeSyntax recipe)))
      | .vector _ => elabCommand (← `(noncomputable def $encoding : NativeLookupEncoding := .vector [$recipes,*]))
      let expanded := mkIdent (name.getId ++ Name.mkSimple s!"expanded{operand.native_leaf}")
      let indices : Array (TSyntax `term) := operand.expansion.map quote
      elabCommand (← `(theorem $expanded : LookupPayload.expand $definitionsName [$indices,*] ($leafName).payload =
        some ($encoding).program := by rfl))
      let roles := mkIdent (name.getId ++ Name.mkSimple s!"baseChecked{operand.native_leaf}")
      elabCommand (← `(theorem $roles : ($encoding).baseCheck $typingName = true := by decide +kernel))
      if operand.kind == "query" || operand.kind == "decoder" then
        let some sourceRow := operand.source_row | throwError "source operand has no authored row selector"
        let some oldRow := previous.rows[sourceRow]? | throwError "authored row selector outside original bank"
        let maskOffset := if operand.kind == "decoder" then 1 else 0
        unless oldRow.fields.size == recipes.size + maskOffset && operand.fields.size == oldRow.fields.size do
          throwError "actual source operand field coverage changed"
        let mut targets := actualEncoding.columns.toArray
        if operand.kind == "decoder" then
          let .column mask := actual.weight | throwError "source decoder must use the actual mask operand"
          targets := #[AffineProgram.input mask] ++ targets
        let mut originalFields : Array (TSyntax `term) := #[]
        let mut soundFields : Array (TSyntax `term) := #[]
        for h : column in [:targets.size] do
          let recipe := mkIdent (name.getId ++ Name.mkSimple s!"recipe{operand.native_leaf}_{column}")
          elabCommand (← `(noncomputable def $recipe : NativeBaseRecipe := $(← recipeSyntax targets[column])))
          let original := mkIdent (referenceName.getId ++ Name.mkSimple s!"field{sourceRow}_{column}")
          originalFields := originalFields.push (← `(($original).source))
          let agreement := mkIdent (name.getId ++ Name.mkSimple s!"field{operand.native_leaf}_{column}")
          elabCommand (← `(noncomputable def $agreement : BaseRecipeAgreement $copyRelations $recipe :=
            ⟨($original).source, $(← combinationSyntax arity relationCount operand.fields[column]!)⟩))
          let checked := mkIdent (name.getId ++ Name.mkSimple s!"fieldChecked{operand.native_leaf}_{column}")
          let inBank := mkIdent (name.getId ++ Name.mkSimple s!"inBank{operand.native_leaf}_{column}")
          elabCommand (← `(theorem $checked : ($agreement).check $sourcePlacement ($bank).placement = true := by decide +kernel))
          elabCommand (← `(theorem $inBank : ($bank).check $recipe = true := by decide +kernel))
          let sound := mkIdent (name.getId ++ Name.mkSimple s!"sourceField{operand.native_leaf}_{column}")
          elabCommand (← `(theorem $sound (base : GKRAddress → Source.BaseField)
            (holds : Satisfies $copyRelations (base ∘ ($bank).address)) :
            ($agreement).source.value ((base ∘ ($bank).address) ∘ $sourcePlacement) = ($recipe).value base :=
            BaseRecipeAgreement.sound_bank $sourcePlacement $bank $checked $inBank base holds))
          soundFields := soundFields.push (← `($sound assignment.base holds))
        let query := mkIdent (name.getId ++ Name.mkSimple s!"query{operand.native_leaf}")
        let fields := originalFields.extract maskOffset originalFields.size
        let mask ← if operand.kind == "decoder" then `(some $(originalFields[0]!)) else `(none)
        elabCommand (← `(noncomputable def $query : SourceLookupQuery := ⟨[$fields,*], $mask⟩))
        let maskProof ← if operand.kind == "decoder" then do
            let .column maskAddress := actual.weight | throwError "invalid decoder mask"
            let maskRole := mkIdent (name.getId ++ Name.mkSimple s!"maskBase{operand.native_leaf}")
            elabCommand (← `(theorem $maskRole : ($typingName).compatible ($(← addressSyntax maskAddress), .base) = true := by decide +kernel))
            `((TypedAssignment.value_base assignment $typingName hom $maskRole).trans
              (congrArg hom $(soundFields[0]!)).symm)
          else `(by rfl)
        let fieldsProof ← listEquality (soundFields.extract maskOffset soundFields.size)
        let sourceQuery := mkIdent (name.getId ++ Name.mkSimple s!"sourceQuery{operand.native_leaf}")
        elabCommand (← `(theorem $sourceQuery {R : Type} [CommRing R]
          (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
          (assignment : TypedAssignment R)
          (defined : ∀ definition ∈ $definitionsName, definition.Holds hom challenges (assignment.value $typingName hom))
          (holds : Satisfies $copyRelations (assignment.base ∘ ($bank).address)) :
          NativeLookupLeaf.registryValue $registry hom challenges gamma (assignment.value $typingName hom) $(quote operand.native_leaf) =
            ($query).value hom challenges.lookupAlpha gamma ((assignment.base ∘ ($bank).address) ∘ $sourcePlacement) :=
          (NativeLookupLeaf.registryValue_at $found hom challenges gamma (assignment.value $typingName hom)).trans
            (NativeLookupLeaf.source_query $leafName $encoding $typingName $roles $definitionsName [$indices,*]
              $expanded assignment hom challenges gamma defined $query _ $fieldsProof $maskProof)))
    -- Expected query lists come from the independently imported original rows,
    -- rather than the operand selectors or the native reduction tree.
    if phaseIndex != 2 && phaseIndex != 3 then return
    for (group, description) in cert.groups.entries do
      if group == "LookupTimestamps" then continue
      let (stem, rowKind) ← match group with
        | "GenericLookup" => pure ("generic", "generic")
        | "Lookup16Bits" => pure ("range16", "range16")
        | _ => throwError "unexpected source lookup group"
      let mut queries : Array (TSyntax `term) := #[]
      for h : rowIndex in [:previous.rows.size] do
        let row := previous.rows[rowIndex]
        if row.kind == rowKind || (group == "GenericLookup" && row.kind == "decoder") then
          let mut fields : Array (TSyntax `term) := #[]
          for column in [:row.fields.size] do
            let original := mkIdent (referenceName.getId ++ Name.mkSimple s!"field{rowIndex}_{column}")
            fields := fields.push (← `(($original).source))
          let offset := if row.kind == "decoder" then 1 else 0
          let mask ← if row.kind == "decoder" then `(some $(fields[0]!)) else `(none)
          let values := fields.extract offset fields.size
          queries := queries.push (← `(SourceLookupQuery.mk [$values,*] $mask))
      let sourceQueries := mkIdent (name.getId ++ Name.mkSimple s!"{stem}Queries")
      elabCommand (← `(noncomputable def $sourceQueries : List SourceLookupQuery := [$queries,*]))
      let selected := cert.operands.filter (fun operand => operand.group == group)
      let setups := selected.filter (fun operand => operand.kind == "setup")
      unless setups.size == 1 do throwError "source group requires exactly one actual setup operand"
      let some setupOperand := setups[0]? | throwError "missing actual setup operand"
      let setupLeaf := setupOperand.native_leaf
      let actualSetup := mkIdent (name.getId ++ Name.mkSimple s!"leaf{setupLeaf}")
      let setupChecked := mkIdent (name.getId ++ Name.mkSimple s!"{stem}SetupChecked")
      elabCommand (← `(theorem $setupChecked : ($actualSetup).isSetup = true := by decide +kernel))
      let terms := mkIdent (name.getId ++ Name.mkSimple s!"{stem}SourceTerms")
      elabCommand (← `(noncomputable def $terms {R : Type} [CommRing R]
        (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
        (assignment : TypedAssignment R) : List (RationalPair R) :=
        (($sourceQueries).map (fun query => query.value hom challenges.lookupAlpha gamma
          ((assignment.base ∘ ($bank).address) ∘ $sourcePlacement))) ++
        [NativeLookupLeaf.registryValue $registry hom challenges gamma (assignment.value $typingName hom) $(quote setupLeaf)]))
      unless description.native_leaves.size == description.source_labels.size do throwError "unequal source label lists"
      let mut pairs : Array (TSyntax `term) := #[]
      for (nativeIndex, sourceIndex) in description.native_leaves.zip description.source_labels do
        pairs := pairs.push (← `(($(quote nativeIndex), $(quote sourceIndex))))
      let label := mkIdent (name.getId ++ Name.mkSimple s!"{stem}Label")
      elabCommand (← `(noncomputable def $label (index : Nat) : Nat :=
        ((List.find? (fun entry : Nat × Nat => entry.1 == index) [$pairs,*]).map Prod.snd).getD 0))
      let tree := mkIdent (referenceName.getId ++ Name.mkSimple s!"{stem}Tree")
      let output := mkIdent (referenceName.getId ++ Name.mkSimple s!"{stem}Output")
      let reduction := mkIdent (referenceName.getId ++ Name.mkSimple s!"{stem}Reduction")
      let leaves : Array (TSyntax `term) := description.native_leaves.map quote
      let leavesChecked := mkIdent (name.getId ++ Name.mkSimple s!"{stem}LeavesChecked")
      elabCommand (← `(theorem $leavesChecked : ($tree).leaves = [$leaves,*] := by decide +kernel))
      let coverage := mkIdent (name.getId ++ Name.mkSimple s!"{stem}SourceCoverage")
      elabCommand (← `(theorem $coverage : (($tree).leaves.map $label).Perm (List.range $(quote (queries.size + 1))) := by decide +kernel))
      let mut matchingProofs : Array (TSyntax `term) := #[]
      for nativeIndex in description.native_leaves do
        let matched := mkIdent (name.getId ++ Name.mkSimple s!"{stem}Match{nativeIndex}")
        let proof ← if nativeIndex == setupLeaf then `(by rfl) else do
          let sourceQuery := mkIdent (name.getId ++ Name.mkSimple s!"sourceQuery{nativeIndex}")
          `($sourceQuery hom challenges gamma assignment defined copies)
        elabCommand (← `(theorem $matched {R : Type} [CommRing R]
          (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
          (assignment : TypedAssignment R)
          (defined : ∀ definition ∈ $definitionsName, definition.Holds hom challenges (assignment.value $typingName hom))
          (copies : Satisfies $copyRelations (assignment.base ∘ ($bank).address)) :
          NativeLookupLeaf.registryValue $registry hom challenges gamma (assignment.value $typingName hom) $(quote nativeIndex) =
            (($terms hom challenges gamma assignment)[$label $(quote nativeIndex)]?).getD 0 := $proof))
        matchingProofs := matchingProofs.push (← `($matched hom challenges gamma assignment defined copies))
      let nativeGates := mkIdent (referenceName.getId ++ `gates)
      let translated := mkIdent (name.getId ++ Name.mkSimple s!"{stem}SourceReduction")
      elabCommand (← `(theorem $translated {R : Type} [CommRing R]
        (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
        (assignment : TypedAssignment R)
        (defined : ∀ definition ∈ $definitionsName, definition.Holds hom challenges (assignment.value $typingName hom))
        (copies : Satisfies $copyRelations (assignment.base ∘ ($bank).address))
        (holds : ∀ gate ∈ $nativeGates, gate.Holds hom challenges gamma (assignment.value $typingName hom)) :
        ($output).value (assignment.value $typingName hom) = ($terms hom challenges gamma assignment).sum := by
        apply LookupTree.translate_output $tree _ _ ($reduction hom challenges gamma _ holds) _ $label
        · rw [$leavesChecked:ident]
          exact PredicateChecks.all $(← predicateChecks matchingProofs)
        · exact $coverage))

end Airbender.Compiler.LookupSourceImport
