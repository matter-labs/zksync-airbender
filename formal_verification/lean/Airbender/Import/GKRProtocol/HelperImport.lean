import Airbender.Proofs.GKRProtocol.HelperCertificate
import Airbender.Import.GKRProtocol.MemoryImport

namespace Airbender.Compiler.HelperImport
open Lean Elab Command
set_option warningAsError true
set_option maxRecDepth 32768

private instance : ObjectKey String where
  decode := Except.ok
  encode := id

structure OperandSelector where
  native_leaf : Nat
  locator : Fixed 2 Nat
  expansion : Array Nat
  source_index : Nat
  witness : Import.EncodedCombination
  deriving FromJson

structure GroupSelector where
  native_leaves : Array Nat
  source_labels : Array Nat
  deriving FromJson

structure Selectors where
  format_version : Nat
  addresses : Array GKRAddress
  operands : Array OperandSelector
  setup_leaf : Nat
  group : GroupSelector
  deriving FromJson

private def addressSyntax : GKRAddress → CommandElabM (TSyntax `term)
  | .BaseLayerWitness index => `(GKRAddress.BaseLayerWitness $(quote index))
  | .BaseLayerMemory index => `(GKRAddress.BaseLayerMemory $(quote index))
  | .InnerLayer layer index => `(GKRAddress.InnerLayer $(quote layer) $(quote index))
  | .Cached layer index => `(GKRAddress.Cached $(quote layer) $(quote index))
  | .Setup index => `(GKRAddress.Setup $(quote index))
  | .ScratchSpace _ => throwError "memory bank contains an unallocated ScratchSpace address"
  | .VirtualSetup kind => do
      let kind ← match kind with
        | .RangeCheck16Bits => `(VirtualSetupPoly.RangeCheck16Bits)
        | .RangeCheckTimestamp => `(VirtualSetupPoly.RangeCheckTimestamp)
        | .InitsAndTeardownsLow => `(VirtualSetupPoly.InitsAndTeardownsLow)
        | .InitsAndTeardownsHigh => `(VirtualSetupPoly.InitsAndTeardownsHigh)
      `(GKRAddress.VirtualSetup $kind)

private def finSyntax (index bound : Nat) : CommandElabM (TSyntax `term) := do
  unless index < bound do throwError "memory certificate index outside actual finite bank"
  `(⟨$(quote index), by decide⟩)

private def combinationSyntax (arity length : Nat) (witness : Import.EncodedCombination) : CommandElabM (TSyntax `term) := do
  let entries ← witness.mapM fun (polynomial, relation) => do
    let terms ← polynomial.mapM fun (coefficient, monomial) => do
      unless coefficient < babyBearModulus do throwError "noncanonical memory certificate coefficient"
      let indices ← monomial.mapM fun index => finSyntax index arity
      `((($(quote coefficient) : Source.BaseField), [$indices,*]))
    `(([$terms,*], $(← finSyntax relation length)))
  `([$entries,*])

private def sourceInputSyntax (bound : Nat) : Source.LookupInput → CommandElabM (TSyntax `term)
  | .Variable index => do
      unless index < bound do throwError "memory field changes original source-variable scope"
      `(Source.LookupInput.Variable $(quote index))
  | .Expression terms constant => do
      let terms ← terms.mapM fun (coefficient, index) => do
        unless index < bound do throwError "memory expression changes original source-variable scope"
        `((Coefficient.mk ⟨$(quote coefficient.raw.val), by decide⟩, $(quote index)))
      `(Source.LookupInput.Expression #[$terms,*] (Coefficient.mk ⟨$(quote constant.raw.val), by decide⟩))

private def fieldSyntax (bound : Nat) : Source.MemoryField → CommandElabM (TSyntax `term)
  | .input expression => do `(Source.MemoryField.input $(← sourceInputSyntax bound expression))
  | .readTimestamp query limb => do `(Source.MemoryField.readTimestamp $(quote query) $(← finSyntax limb.val 2))
  | .initializationAddress limb => do `(Source.MemoryField.initializationAddress $(← finSyntax limb.val 2))
  | .teardownTimestamp query limb => do `(Source.MemoryField.teardownTimestamp $(quote query) $(← finSyntax limb.val 2))
  | .teardownValue query limb => do `(Source.MemoryField.teardownValue $(quote query) $(← finSyntax limb.val 2))
  | .constant scalar => `(Source.MemoryField.constant $(quote scalar))
  | .add left right => do `(Source.MemoryField.add $(← fieldSyntax bound left) $(← fieldSyntax bound right))
  | .scale scalar inner => do `(Source.MemoryField.scale $(quote scalar) $(← fieldSyntax bound inner))
  | .neg inner => do `(Source.MemoryField.neg $(← fieldSyntax bound inner))

private def definitionSyntax (definition : LookupSourceData.Definition) : CommandElabM (TSyntax `term) := do
  let program ← match definition with
    | .cache _ relation => CacheImport.program relation
    | .copy _ address => do `(AffineProgram.input (R := CacheCoefficient) $(← addressSyntax address))
    | .scalar _ row => CacheImport.program (.SingleColumnLookup row 0)
    | .vector _ row => CacheImport.program (.VectorizedLookup row)
  `(AffineDefinition.mk $(← addressSyntax definition.output) $program)

private def inputSyntax : LookupSourceData.Input → CommandElabM (TSyntax `term)
  | .address address => do `(AffineProgram.input (R := CacheCoefficient) $(← addressSyntax address))
  | .scalar row => CacheImport.program (.SingleColumnLookup row 0)
  | .vector row => CacheImport.program (.VectorizedLookup row)
  | .setup addresses => CacheImport.program (.VectorizedLookupSetup addresses)

private def weightSyntax : LookupWeight → CommandElabM (TSyntax `term)
  | .one => `(LookupWeight.one)
  | .column address => do `(LookupWeight.column $(← addressSyntax address))
  | .negativeMultiplicity address => do `(LookupWeight.negativeMultiplicity $(← addressSyntax address))

private def recipeSyntax : NativeBaseRecipe → CommandElabM (TSyntax `term)
  | .constant scalar => `(AffineProgram.constant (Address := GKRAddress) (R := Nat) $(quote scalar))
  | .input address => do `(AffineProgram.input (R := Nat) $(← addressSyntax address))
  | .add left right => do `(AffineProgram.add $(← recipeSyntax left) $(← recipeSyntax right))
  | .scale coefficient inner => do `(AffineProgram.scale $(quote coefficient) $(← recipeSyntax inner))

private def listEquality (proofs : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let mut result ← `(rfl)
  for proof in proofs.reverse do result ← `(congrArg₂ List.cons $proof $result)
  return result

private def predicateChecks (proofs : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let mut result ← `(PredicateChecks.nil)
  for proof in proofs.reverse do result ← `(PredicateChecks.cons $proof $result)
  return result

private def helperSyntax (bound : Nat) : Source.HelperField → CommandElabM (TSyntax `term)
  | .memory field => do `(Source.HelperField.memory $(← fieldSyntax bound field))
  | .borrow index => `(Source.HelperField.borrow $(quote index))
  | .add left right => do `(Source.HelperField.add $(← helperSyntax bound left) $(← helperSyntax bound right))
  | .scale scalar field => do `(Source.HelperField.scale $(quote scalar) $(← helperSyntax bound field))
  | .neg field => do `(Source.HelperField.neg $(← helperSyntax bound field))

syntax (name := importSourceHelpers) "import_source_helpers " ident " from " str " source " str
  " selectors " str " memory_model " ident " lookup_model " ident " typing " ident : command

elab_rules : command
  | `(import_source_helpers $name:ident from $pairPath:str source $sourcePath:str selectors $selectorText:str
      memory_model $memoryPrefix:ident lookup_model $lookupPrefix:ident typing $typingName:ident) => do
    let pairJson ← match Json.parse (← IO.FS.readFile pairPath.getString) with
      | .ok value => pure value | .error error => throwError "{error}"
    let sourceJson ← match Json.parse (← IO.FS.readFile sourcePath.getString) with
      | .ok value => pure value | .error error => throwError "{error}"
    let pair ← match fromJson? (α := Import.Pair) pairJson with
      | .ok value => pure value | .error error => throwError "{error}"
    let snapshot ← match fromJson? (α := Source.Snapshot) sourceJson with
      | .ok value => pure value | .error error => throwError "{error}"
    let cert ← match Json.parse selectorText.getString >>= (fromJson? (α := Selectors)) with
      | .ok value => pure value | .error error => throwError "{error}"
    let .ok originalSource := pairJson.getObjVal? "source" | throwError "missing original compiler input"
    let .ok retainedSource := sourceJson.getObjVal? "source" | throwError "missing retained compiler input"
    unless pair.format_version == 1 && snapshot.format_version == 1 && cert.format_version == 1 &&
        pair.family == snapshot.family && pair.cached == snapshot.cached && originalSource == retainedSource do
      throwError "helper source is detached from actual compilation"
    let requests ← match Source.helperRequests snapshot.semantic_inputs with
      | .ok value => pure value | .error error => throwError "{error}"
    let sourceCount := pair.source.num_variables
    let arity := cert.addresses.size
    unless 0 < sourceCount && sourceCount ≤ arity && cert.addresses.toList.eraseDups.length == arity do
      throwError "helper source address bank is empty or aliased"
    let mut originals : Array (TSyntax `term) := #[]
    for index in [:sourceCount] do
      let [(_, actual)] := (pair.circuit.placement_data.entries.filter (·.1 == index)).toList
        | throwError "missing original helper variable placement"
      unless cert.addresses[index]? == some actual do throwError "helper bank changes original source placement"
      originals := originals.push (← addressSyntax actual)
    let bank := mkIdent (memoryPrefix.getId ++ `bank)
    let memoryPlacement := mkIdent (memoryPrefix.getId ++ `sourcePlacement)
    let actualBank := mkIdent (memoryPrefix.getId ++ `addresses)
    let bankChecked := mkIdent (name.getId ++ `bankChecked)
    let addressTerms ← cert.addresses.mapM addressSyntax
    elabCommand (← `(theorem $bankChecked : $actualBank = [$addressTerms,*] := by decide +kernel))
    let originalProjection := mkIdent (name.getId ++ `originalProjection)
    elabCommand (← `(theorem $originalProjection :
      ((List.range $(quote sourceCount)).map (fun index => ($bank).address (($memoryPlacement).original index))) =
        [$originals,*] := by decide +kernel))
    let mut history : Array (TSyntax `term) := #[]
    for query in pair.circuit.memory_layout.ram_access_sets do
      let timestamps := match query with | .Readonly row => row.read_timestamp | .Write row => row.read_timestamp
      let [low, high] := timestamps.values.toList | throwError "native history timestamp width changed"
      history := history.push (← `(($(← addressSyntax (.BaseLayerMemory low)), $(← addressSyntax (.BaseLayerMemory high)))))
    let historyProjection := mkIdent (name.getId ++ `historyProjection)
    elabCommand (← `(theorem $historyProjection :
      ((List.range $(quote history.size)).map (fun index =>
        (($bank).address (($memoryPlacement).readTimestamp index ⟨0, by decide⟩),
         ($bank).address (($memoryPlacement).readTimestamp index ⟨1, by decide⟩)))) = [$history,*] := by decide +kernel))
    let borrows := pair.circuit.aux_layout_data.shuffle_ram_timestamp_comparison_aux_vars
    unless borrows.size == requests.comparisons.size do throwError "source/native timestamp comparison counts differ"
    let borrowTerms ← borrows.mapM (fun row => addressSyntax row.intermediate_borrow)
    let borrowAddresses := mkIdent (name.getId ++ `borrowAddresses)
    let placement := mkIdent (name.getId ++ `placement)
    let sourceValues := mkIdent (name.getId ++ `sourceValues)
    elabCommand (← `(def $borrowAddresses : List GKRAddress := [$borrowTerms,*]))
    elabCommand (← `(def $placement : Source.HelperPlacement $(quote arity) :=
      ⟨$memoryPlacement, fun index => ($bank).placement ((($borrowAddresses)[index]?).getD (.BaseLayerWitness 0))⟩))
    elabCommand (← `(def $sourceValues (base : GKRAddress → Source.BaseField) : Source.HelperValues :=
      ($placement).project (base ∘ ($bank).address)))
    let inBank := mkIdent (name.getId ++ `borrowsInBank)
    let roles := mkIdent (name.getId ++ `borrowRoles)
    let fresh := mkIdent (name.getId ++ `borrowFresh)
    let unique := mkIdent (name.getId ++ `borrowUnique)
    let projections := mkIdent (memoryPrefix.getId ++ `projectionInputs)
    elabCommand (← `(theorem $inBank : ($bank).inputCheck $borrowAddresses = true := by decide +kernel))
    elabCommand (← `(theorem $roles : ($borrowAddresses).all
      (fun address => ($typingName).compatible (address, .base)) = true := by decide +kernel))
    elabCommand (← `(theorem $unique : ($borrowAddresses).Nodup := by decide +kernel))
    elabCommand (← `(theorem $fresh : ($borrowAddresses).all (fun address =>
      !(($actualBank).take $(quote sourceCount) ++ $projections).any (addressEqual address)) = true := by decide +kernel))
    let fields := mkIdent (name.getId ++ `fields)
    let sourceFields ← requests.timestamps.mapM (helperSyntax sourceCount)
    elabCommand (← `(noncomputable def $fields : List Source.HelperField := [$sourceFields,*]))
    let scope := mkIdent (name.getId ++ `sourceReferencesValid)
    elabCommand (← `(theorem $scope : ($fields).all
      (Source.HelperField.referencesValid $(quote sourceCount) $(quote history.size)
        $(quote pair.circuit.memory_layout.teardown_sets.size) $(quote borrows.size)
        $(quote (snapshot.configuration.inline_init_teardown_pairs != 0))) = true := by decide +kernel))
    let gates := pair.circuit.layers.flatMap (fun layer => layer.gates ++ layer.gates_with_external_connections)
    let mut copies : Array (TSyntax `term) := #[]
    for gate in gates do
      if let .CopyInBaseField input output := gate.enforced_relation then
        let some outIndex := cert.addresses.findIdx? (· == output) | throwError "base-copy output omitted from helper bank"
        let some inIndex := cert.addresses.findIdx? (· == input) | throwError "base-copy input omitted from helper bank"
        copies := copies.push (← `(Compiler.add (Compiler.atom $(← finSyntax outIndex arity))
          (Compiler.negate (Compiler.atom $(← finSyntax inIndex arity)))))
    let copyRelations := mkIdent (name.getId ++ `copyRelations)
    elabCommand (← `(noncomputable def $copyRelations : List (Polynomial $(quote arity) Source.BaseField) := [$copies,*]))
    let definitionsName := mkIdent (name.getId ++ `definitions)
    let actualDefinitions := LookupSourceData.definitions pair.circuit
    let definitions ← actualDefinitions.mapM definitionSyntax
    elabCommand (← `(noncomputable def $definitionsName : List AffineDefinition := [$definitions,*]))
    let registry := mkIdent (lookupPrefix.getId ++ `registry)
    let mut actualOperands : Array (Array LookupSourceData.Operand) := #[]
    let mut offsets : Array Nat := #[]
    let mut primitiveCount := 0
    for gate in gates do
      let rows ← match LookupSourceData.operands gate.enforced_relation with
        | .ok rows => pure rows | .error error => throwError "{error}"
      offsets := offsets.push primitiveCount
      primitiveCount := primitiveCount + rows.size
      actualOperands := actualOperands.push rows
    for operand in cert.operands do
      let [gateIndex, operandIndex] := operand.locator.values.toList | throwError "invalid helper operand locator"
      let some operands := actualOperands[gateIndex]? | throwError "helper gate index outside actual graph"
      let some actual := operands[operandIndex]? | throwError "helper operand index outside actual gate"
      unless offsets[gateIndex]? == some (operand.native_leaf - operandIndex) &&
          operand.native_leaf ≥ operandIndex do throwError "helper registry index disagrees with actual locator"
      let .one := actual.weight | throwError "timestamp query has a nontrivial weight"
      let head ← match LookupSourceData.head actualDefinitions operand.expansion.toList actual.input with
        | .ok head => pure head | .error error => throwError "{error}"
      let .scalar recipe := LookupSourceData.encoding head | throwError "timestamp query is not a scalar"
      let some expected := requests.timestamps[operand.source_index]? | throwError "helper selector outside independent source queries"
      let leaf := mkIdent (name.getId ++ Name.mkSimple s!"leaf{operand.native_leaf}")
      let found := mkIdent (name.getId ++ Name.mkSimple s!"found{operand.native_leaf}")
      let recipeName := mkIdent (name.getId ++ Name.mkSimple s!"recipe{operand.native_leaf}")
      let candidate := mkIdent (name.getId ++ Name.mkSimple s!"candidate{operand.native_leaf}")
      let checked := mkIdent (name.getId ++ Name.mkSimple s!"checked{operand.native_leaf}")
      let recipeInBank := mkIdent (name.getId ++ Name.mkSimple s!"inBank{operand.native_leaf}")
      let recipeRoles := mkIdent (name.getId ++ Name.mkSimple s!"roles{operand.native_leaf}")
      let expanded := mkIdent (name.getId ++ Name.mkSimple s!"expanded{operand.native_leaf}")
      let indices : Array (TSyntax `term) := operand.expansion.map quote
      elabCommand (← `(noncomputable def $leaf : NativeLookupLeaf :=
        ⟨$(← weightSyntax actual.weight), $(← inputSyntax actual.input)⟩))
      elabCommand (← `(theorem $found : ($registry)[$(quote operand.native_leaf)]? = some $leaf := by rfl))
      elabCommand (← `(noncomputable def $recipeName : NativeBaseRecipe := $(← recipeSyntax recipe)))
      elabCommand (← `(noncomputable def $candidate : HelperAgreement $copyRelations $recipeName :=
        ⟨$(← helperSyntax sourceCount expected), $(← combinationSyntax arity copies.size operand.witness)⟩))
      elabCommand (← `(theorem $checked : ($candidate).check $placement $bank = true := by decide +kernel))
      elabCommand (← `(theorem $recipeInBank : ($bank).check $recipeName = true := by decide +kernel))
      elabCommand (← `(theorem $recipeRoles : (NativeLookupEncoding.scalar $recipeName).baseCheck $typingName = true := by decide +kernel))
      elabCommand (← `(theorem $expanded : LookupPayload.expand $definitionsName [$indices,*] ($leaf).payload =
        some ($recipeName).toPayload := by rfl))
      let matched := mkIdent (name.getId ++ Name.mkSimple s!"sourceQuery{operand.native_leaf}")
      elabCommand (← `(theorem $matched {R : Type} [CommRing R]
        (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R) (assignment : TypedAssignment R)
        (defined : ∀ definition ∈ $definitionsName, definition.Holds hom challenges (assignment.value $typingName hom))
        (copies : Satisfies $copyRelations (assignment.base ∘ ($bank).address)) :
        NativeLookupLeaf.registryValue $registry hom challenges gamma (assignment.value $typingName hom) $(quote operand.native_leaf) =
          RationalPair.leaf 1 (hom (($candidate).source.value ($sourceValues assignment.base)) + gamma) :=
        (NativeLookupLeaf.registryValue_at $found hom challenges gamma (assignment.value $typingName hom)).trans
          (NativeLookupLeaf.source_helper $leaf $recipeName $typingName $recipeRoles $definitionsName [$indices,*]
            $expanded (by rfl) assignment hom challenges gamma defined ($candidate).source ($sourceValues assignment.base)
            (($candidate).sound $placement $bank $checked $recipeInBank assignment.base copies))))
    let setupIndex := cert.setup_leaf
    let terms := mkIdent (name.getId ++ `timestampTerms)
    elabCommand (← `(noncomputable def $terms {R : Type} [CommRing R]
      (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R) (assignment : TypedAssignment R) :
      List (RationalPair R) := ($fields).map (fun field => RationalPair.leaf 1
        (hom (field.value ($sourceValues assignment.base)) + gamma)) ++
      [NativeLookupLeaf.registryValue $registry hom challenges gamma (assignment.value $typingName hom) $(quote setupIndex)]))
    let tree := mkIdent (lookupPrefix.getId ++ `timestampTree)
    let leavesChecked := mkIdent (name.getId ++ `leavesChecked)
    let sourceCoverage := mkIdent (name.getId ++ `sourceCoverage)
    let nativeLeaves : Array (TSyntax `term) := cert.group.native_leaves.map quote
    let labels : Array (TSyntax `term) := cert.group.source_labels.map quote
    elabCommand (← `(theorem $leavesChecked : ($tree).leaves = [$nativeLeaves,*] := by decide +kernel))
    elabCommand (← `(theorem $sourceCoverage : ([$labels,*] : List Nat).Perm (List.range (($fields).length + 1)) := by decide +kernel))
    unless cert.group.native_leaves.size == cert.group.source_labels.size do throwError "incomplete timestamp occurrence correspondence"
    let setup := mkIdent (name.getId ++ `setupChecked)
    elabCommand (← `(theorem $setup : (($registry)[$(quote setupIndex)]?).any NativeLookupLeaf.isSetup = true := by decide +kernel))
    let mut matchingProofs : Array (TSyntax `term) := #[]
    for (nativeIndex, sourceIndex) in cert.group.native_leaves.zip cert.group.source_labels do
      let proof ← if nativeIndex == setupIndex then do
          unless sourceIndex == requests.timestamps.size do throwError "timestamp setup label changes source order"
          `(by rfl)
        else do
          let [operand] := (cert.operands.filter (fun row => row.native_leaf == nativeIndex)).toList
            | throwError "missing or duplicate consumed timestamp selector"
          unless sourceIndex == operand.source_index do throwError "timestamp occurrence changes independent source selector"
          let matched := mkIdent (name.getId ++ Name.mkSimple s!"sourceQuery{nativeIndex}")
          `($matched hom challenges gamma assignment defined copies)
      matchingProofs := matchingProofs.push proof
    let mut correspondence ← `(List.Forall₂.nil)
    for proof in matchingProofs.reverse do correspondence ← `(List.Forall₂.cons $proof $correspondence)
    let output := mkIdent (lookupPrefix.getId ++ `timestampOutput)
    let reduction := mkIdent (lookupPrefix.getId ++ `timestampReduction)
    let nativeGates := mkIdent (lookupPrefix.getId ++ `gates)
    let translated := mkIdent (name.getId ++ `timestampSourceReduction)
    elabCommand (← `(theorem $translated {R : Type} [CommRing R]
      (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R) (assignment : TypedAssignment R)
      (defined : ∀ definition ∈ $definitionsName, definition.Holds hom challenges (assignment.value $typingName hom))
      (copies : Satisfies $copyRelations (assignment.base ∘ ($bank).address))
      (holds : ∀ gate ∈ $nativeGates, gate.Holds hom challenges gamma (assignment.value $typingName hom)) :
      ($output).value (assignment.value $typingName hom) = ($terms hom challenges gamma assignment).sum := by
      apply ($reduction hom challenges gamma (assignment.value $typingName hom) holds).trans
      apply helper_sum_translation _ ($terms hom challenges gamma assignment) (native := ($tree).leaves)
        (labels := ([$labels,*] : List Nat))
      · rw [$leavesChecked:ident]
        exact $correspondence
      · simpa only [$terms:ident, List.length_append, List.length_map, List.length_cons, List.length_nil] using $sourceCoverage))

end Airbender.Compiler.HelperImport
