module
public meta import Proven.Import.GKRProtocol.Export
public import Proven.GKRCompiler.Bidirectional
public import Proven.GKRProtocol.HelperAssertions
public import Proven.GKRProtocol.BaseAssignment
public import Proven.Import.GKRProtocol.LookupSourceData
public meta import Proven.GKRCompiler.Bidirectional
public meta import Proven.GKRProtocol.HelperAssertions
public meta import Proven.GKRProtocol.BaseAssignment
public meta import Proven.Import.GKRProtocol.LookupSourceData

public meta section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticImport
open Lean Elab Command
set_option maxRecDepth 32768

structure Selectors where
  format_version : Nat
  inputs : Array GKRAddress
  addresses : Array GKRAddress
  extension : Array Import.EncodedPolynomial
  forward : Array Import.EncodedCombination
  backward : Array Import.EncodedCombination
  deriving FromJson

private def addressTermSyntax : GKRAddress → CommandElabM (TSyntax `term)
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
  unless index < bound do throwError "compiler certificate index {index} is outside bound {bound}"
  `(⟨$(quote index), by decide⟩)

private def coefficientSyntax (raw : Coefficient) : CommandElabM (TSyntax `term) :=
  `((($(quote raw.raw.val) : ZMod babyBearModulus) * $(quote montgomeryInverse)))

private def constantSyntax (raw : Coefficient) : CommandElabM (TSyntax `term) := do
  `(Compiler.Expression.constant $(← coefficientSyntax raw))

private def zeroSyntax : CommandElabM (TSyntax `term) := `(Compiler.Expression.constant 0)
private def oneSyntax : CommandElabM (TSyntax `term) := `(Compiler.Expression.constant 1)

private def atomSyntax (index bound : Nat) : CommandElabM (TSyntax `term) := do
  `(Compiler.Expression.atom $(← finSyntax index bound))

initialize sharedExpressions : IO.Ref Nat ← IO.mkRef 0

private partial def syntaxWeight : Syntax → Nat
  | .node _ _ children => 1 + children.foldl (fun sum child => sum + syntaxWeight child) 0
  | _ => 1

/-- Share closed expression trees before elaboration. Every node keeps its original type and value. -/
private def shareExpression (bound : Nat) (term : TSyntax `term) : CommandElabM (TSyntax `term) := do
  if syntaxWeight term ≤ 400 then return term
  let index ← sharedExpressions.get
  sharedExpressions.set (index + 1)
  let name := mkIdent (Name.mkSimple s!"sharedExpression{index}")
  Export.emit (← `(def $name : Compiler.Expression $(quote bound) Source.BaseField := $term))
  `($name)

private def addSyntax (bound : Nat) (left right : TSyntax `term) : CommandElabM (TSyntax `term) := do
  shareExpression bound (← `(Compiler.Expression.add $left $right))

private def mulSyntax (bound : Nat) (left right : TSyntax `term) : CommandElabM (TSyntax `term) := do
  shareExpression bound (← `(Compiler.Expression.mul $left $right))

private partial def sourceSyntax (originalBound bound : Nat) : Expr → CommandElabM (TSyntax `term)
  | .Constant raw => constantSyntax raw
  | .Var index => do
      unless index < originalBound do throwError "full arithmetic source escapes original variable scope"
      atomSyntax index bound
  | .Sum terms => do terms.foldlM (fun result term => do addSyntax bound result (← sourceSyntax originalBound bound term)) (← zeroSyntax)
  | .Product terms => do terms.foldlM (fun result term => do mulSyntax bound result (← sourceSyntax originalBound bound term)) (← oneSyntax)

private def statementSyntax (originalBound bound : Nat) : StructuredStatement → CommandElabM (TSyntax `term)
  | .AssertZero expression _ _ => sourceSyntax originalBound bound expression
  | .Define dst _ expression _ => do
      unless dst < originalBound do throwError "source definition escapes original variable scope"
      let negative ← `(Compiler.Expression.constant (-1))
      addSyntax bound (← atomSyntax dst bound) (← mulSyntax bound negative (← sourceSyntax originalBound bound expression))

private def addressIndex (addresses : Array GKRAddress) (address : GKRAddress) : CommandElabM Nat := do
  match addresses.findIdx? (· == address) with
  | some index => return index
  | none => throwError "native GKR dependency is absent from the certificate address bank: {repr address}"

private def addressSyntax (addresses : Array GKRAddress) (address : GKRAddress) : CommandElabM (TSyntax `term) := do
  atomSyntax (← addressIndex addresses address) addresses.size

private partial def structuredSyntax (addresses : Array GKRAddress) : StructuredExpression → CommandElabM (TSyntax `term)
  | .Constant raw => constantSyntax raw
  | .Place address => addressSyntax addresses address
  | .Sum terms => do terms.foldlM (fun result term => do addSyntax addresses.size result (← structuredSyntax addresses term)) (← zeroSyntax)
  | .Product terms => do terms.foldlM (fun result term => do mulSyntax addresses.size result (← structuredSyntax addresses term)) (← oneSyntax)

private def linearSyntax (addresses : Array GKRAddress) (relation : LinearRelation) : CommandElabM (TSyntax `term) := do
  relation.linear_terms.foldlM (fun result (coefficient, address) => do
    addSyntax addresses.size result (← mulSyntax addresses.size (← constantSyntax coefficient) (← addressSyntax addresses address)))
    (← constantSyntax relation.constant)

private def quadraticSyntax (addresses : Array GKRAddress) (relation : CompiledMaxQuadraticGKRRelation) :
    CommandElabM (TSyntax `term) := do
  let linear : LinearRelation := ⟨relation.linear_terms, relation.constant⟩
  relation.quadratic_terms.foldlM (fun result (left, terms) => do
    terms.foldlM (fun result (coefficient, right) => do
      let term ← mulSyntax addresses.size (← mulSyntax addresses.size (← constantSyntax coefficient) (← addressSyntax addresses left))
        (← addressSyntax addresses right)
      addSyntax addresses.size result term) result) (← linearSyntax addresses linear)

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
  | .MaterializeSingleLookupInput row output _ => do
      let expression ← linearSyntax addresses row.input
      return some (← `(Compiler.ArithmeticGate.define
        $(← finSyntax (← addressIndex addresses output) addresses.size) $expression $expression))
  | .EnforceConstraintsMaxQuadratic _ => throwError "batched arithmetic requires a separate checked adapter"
  | .LookupPairFromCachedVectorInputs _ _ => throwError "retired cached-vector lookup consumer"
  | .UnbalancedGrandProductWithCache _ _ _ => throwError "retired unbalanced product consumer"
  | .CopyInExtensionField _ _ | .InitialGrandProductFromCaches _ _ | .InitialGrandProductWithoutCaches _ _ |
    .MaterializeGrandProductTermExpression _ _ | .TrivialProduct _ _ | .MaskIntoIdentityProduct _ _ _ |
    .MaterializedVectorLookupInput _ _ | .InitsOrTeardownsInitialPair _ _ _ _ |
    .LookupPairFromBaseInputs _ _ _ | .LookupPairFromVectorInputs _ _ |
    .LookupPairFromMaterializedBaseInputs _ _ | .LookupPairFromMaterializedVectorInputs _ _ |
    .LookupFromBaseInputsWithSetup _ _ _ _ | .LookupFromVectorInputWithSetup _ _ _ |
    .LookupFromMaterializedBaseInputWithSetup _ _ _ | .LookupFromMaterializedVectorInputWithSetup _ _ _ |
    .LookupWithCachedDensAndSetup _ _ _ | .LookupWithDensAndSetupExpressions _ _ _ |
    .LookupUnbalancedPairWithMaterializedBaseInputs _ _ _ | .LookupUnbalancedPairWithMaterializedVectorInputs _ _ _ |
    .LookupUnbalancedPairWithVectorInputs _ _ _ | .AggregateLookupRationalPair _ _ => return none

private def polynomialSyntax (arity : Nat) (encoded : Import.EncodedPolynomial) : CommandElabM (TSyntax `term) := do
  let terms ← encoded.mapM fun (coefficient, monomial) => do
    unless coefficient < babyBearModulus do throwError "noncanonical certificate coefficient"
    let wires ← monomial.mapM fun wire => finSyntax wire arity
    `((($(quote coefficient) : ZMod babyBearModulus), [$[$wires],*]))
  `([$[$terms],*])

private def combinationSyntax (arity count : Nat) (encoded : Import.EncodedCombination) : CommandElabM (TSyntax `term) := do
  let terms ← encoded.mapM fun (polynomial, index) => do
    `(($(← polynomialSyntax arity polynomial), $(← finSyntax index count)))
  `([$[$terms],*])

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

private def helperSyntax (bound : Nat) : Source.HelperField → CommandElabM (TSyntax `term)
  | .memory field => do `(Source.HelperField.memory $(← fieldSyntax bound field))
  | .borrow index => `(Source.HelperField.borrow $(quote index))
  | .add left right => do `(Source.HelperField.add $(← helperSyntax bound left) $(← helperSyntax bound right))
  | .scale scalar field => do `(Source.HelperField.scale $(quote scalar) $(← helperSyntax bound field))
  | .neg field => do `(Source.HelperField.neg $(← helperSyntax bound field))

private def assertionSyntax (bound : Nat) : Source.HelperAssertion → CommandElabM (TSyntax `term)
  | .zero field => do `(Source.HelperAssertion.zero $(← helperSyntax bound field))
  | .boolean field => do `(Source.HelperAssertion.boolean $(← helperSyntax bound field))

syntax (name := importFullArithmetic) "import_full_compiler_arithmetic " ident " from " str " source " str
  " selectors " str : command

elab_rules : command
  | `(import_full_compiler_arithmetic $name:ident from $pairPath:str source $sourcePath:str selectors $selectorText:str) => do
    let pairJson ← match Lean.Json.parse (← IO.FS.readFile pairPath.getString) with
      | .ok value => pure value | .error error => throwError "{error}"
    let sourceJson ← match Lean.Json.parse (← IO.FS.readFile sourcePath.getString) with
      | .ok value => pure value | .error error => throwError "{error}"
    let pair ← match fromJson? (α := Import.Pair) pairJson with
      | .ok value => pure value | .error error => throwError "{error}"
    let snapshot ← match fromJson? (α := Source.Snapshot) sourceJson with
      | .ok value => pure value | .error error => throwError "{error}"
    let cert ← match Lean.Json.parse selectorText.getString >>= (fromJson? (α := Selectors)) with
      | .ok value => pure value | .error error => throwError "{error}"
    let .ok originalSource := pairJson.getObjVal? "source" | throwError "missing original source"
    let .ok retainedSource := sourceJson.getObjVal? "source" | throwError "missing retained source"
    unless pair.format_version == 1 && snapshot.format_version == 1 && cert.format_version == 1 &&
        pair.family == snapshot.family && pair.cached == snapshot.cached && originalSource == retainedSource do
      throwError "full arithmetic source is detached from actual compilation"
    let helperRequests ← match Source.helperRequests snapshot.semantic_inputs with
      | .ok value => pure value | .error error => throwError "{error}"
    let helpers ← match Source.helperAssertions snapshot.semantic_inputs with
      | .ok value => pure value | .error error => throwError "{error}"
    let originalCount := pair.source.num_variables
    let mut baseOutputs : Array GKRAddress := #[]
    for layer in pair.circuit.layers do
      for (output, relation) in layer.cached_relations do
        if let .SingleColumnLookup _ _ := relation then baseOutputs := baseOutputs.push output
      for gate in layer.gates ++ layer.gates_with_external_connections do
        match gate.enforced_relation with
        | .LinearBaseFieldRelation _ output | .MaxQuadratic _ _ output |
          .CopyInBaseField _ output | .MaterializeSingleLookupInput _ output _ =>
            baseOutputs := baseOutputs.push output
        | _ => pure ()
    let mut inputs : Array GKRAddress := #[]
    unless originalCount > 0 do throwError "empty original arithmetic source"
    for index in [:originalCount] do
      let [(_, actual)] := (pair.circuit.placement_data.entries.filter (·.1 == index)).toList
        | throwError "missing or ambiguous original arithmetic placement"
      match actual with
      | .BaseLayerWitness index => unless index < pair.circuit.witness_layout.total_width do
          throwError "original witness placement outside actual native layout"
      | .BaseLayerMemory index => unless index < pair.circuit.memory_layout.total_width do
          throwError "original memory placement outside actual native layout"
      | .InnerLayer _ _ | .Cached _ _ =>
          unless baseOutputs.contains actual do throwError "original variable has no actual base-field producer"
      | _ => throwError "unsupported original variable placement in full arithmetic profile"
      unless !inputs.contains actual do throwError "aliased original arithmetic inputs"
      inputs := inputs.push actual
    for index in [:pair.circuit.witness_layout.total_width] do
      let address := GKRAddress.BaseLayerWitness index
      unless inputs.contains address do inputs := inputs.push address
    for index in [:pair.circuit.memory_layout.total_width] do
      let address := GKRAddress.BaseLayerMemory index
      unless inputs.contains address do inputs := inputs.push address
    for address in cert.addresses do
      match address with
      | .VirtualSetup _ => unless inputs.contains address do inputs := inputs.push address
      | .Setup index =>
          unless index < pair.circuit.generic_lookup_tables_width do throwError "setup input outside actual native layout"
          unless inputs.contains address do inputs := inputs.push address
      | .ScratchSpace _ => throwError "full arithmetic address bank contains unallocated scratch storage"
      | _ => pure ()
    unless cert.inputs == inputs && cert.addresses.toList.eraseDups.length == cert.addresses.size do
      throwError "full arithmetic input domain is incomplete, reordered or aliased"
    let n := inputs.size
    let m := cert.addresses.size
    unless cert.extension.size == m do throwError "incomplete full arithmetic witness extension"
    unless cert.addresses.toList.take n == inputs.toList do
      throwError "native bank must begin with all logical/oracle input coordinates"
    let addressesName := mkIdent (name.getId ++ `addresses)
    let inputsName := mkIdent (name.getId ++ `inputs)
    let bank := mkIdent (name.getId ++ `bank)
    let inputBank := mkIdent (name.getId ++ `inputBank)
    let addressTerms ← cert.addresses.mapM addressTermSyntax
    let inputTerms ← inputs.mapM addressTermSyntax
    Export.emit (← `(def $addressesName : List GKRAddress := [$addressTerms,*]))
    Export.emit (← `(def $inputsName : List GKRAddress := [$inputTerms,*]))
    Export.emit (← `(def $bank : WireBank $(quote m) := WireBank.ofList $addressesName (by decide)))
    Export.emit (← `(def $inputBank : WireBank $(quote n) := WireBank.ofList $inputsName (by decide)))
    let initialSegment := mkIdent (name.getId ++ `inputPrefix)
    Export.emit (← `(theorem $initialSegment : ($addressesName).take $(quote n) = $inputsName := by rfl))
    let projection ← `(fun index : Fin $(quote n) => index.castLE (by decide : $(quote n) ≤ $(quote m)))
    let mut gates : Array (TSyntax `term) := #[]
    -- Every actual scalar cache is a base-field definition. Other cache variants
    -- have extension outputs and are handled by the whole-graph construction.
    for layer in pair.circuit.layers do
      for (output, relation) in layer.cached_relations do
        if let .SingleColumnLookup row _ := relation then
          let expression ← linearSyntax cert.addresses row.input
          gates := gates.push (← `(ArithmeticGate.define
            $(← finSyntax (← addressIndex cert.addresses output) m) $expression $expression))
    for layer in pair.circuit.layers do
      for gate in layer.gates ++ layer.gates_with_external_connections do
        if let some description ← gateSyntax cert.addresses gate.enforced_relation then gates := gates.push description
    unless cert.forward.size == gates.size do throwError "full arithmetic certificate omits actual native relations"
    let locateInput := fun address => do finSyntax (← addressIndex inputs address) n
    let history := pair.circuit.memory_layout.ram_access_sets
    let mut readTimes : Array (TSyntax `term) := #[]
    for query in history do
      let times := match query with | .Readonly row => row.read_timestamp | .Write row => row.read_timestamp
      let [low, high] := times.values.toList | throwError "native history timestamp width changed"
      readTimes := readTimes.push (← `(($(← locateInput (.BaseLayerMemory low)), $(← locateInput (.BaseLayerMemory high)))))
    let borrows := pair.circuit.aux_layout_data.shuffle_ram_timestamp_comparison_aux_vars
    unless borrows.size == helperRequests.comparisons.size do throwError "source/native arithmetic borrow counts differ"
    let borrowIndices ← borrows.mapM fun row => do
      let some row := row |
        throwError "full arithmetic capture needs a placement for its derived timestamp borrow"
      locateInput row.intermediate_borrow
    let originalProjection := mkIdent (name.getId ++ `originalProjection)
    let readProjection := mkIdent (name.getId ++ `readProjection)
    let borrowProjection := mkIdent (name.getId ++ `borrowProjection)
    let helperPlacement := mkIdent (name.getId ++ `helperPlacement)
    Export.emit (← `(def $originalProjection (index : Nat) : Fin $(quote n) :=
      if bound : index < $(quote originalCount) then ⟨index, Nat.lt_of_lt_of_le bound (by decide)⟩ else ⟨0, by decide⟩))
    Export.emit (← `(def $readProjection : List (Fin $(quote n) × Fin $(quote n)) := [$readTimes,*]))
    Export.emit (← `(def $borrowProjection : List (Fin $(quote n)) := [$borrowIndices,*]))
    Export.emit (← `(def $helperPlacement : Source.HelperPlacement $(quote n) :=
      ⟨⟨$originalProjection, fun query limb =>
          let places := (($readProjection)[query]?).getD (⟨0, by decide⟩, ⟨0, by decide⟩)
          if limb.val = 0 then places.1 else places.2,
        fun _ => ⟨0, by decide⟩, fun _ _ => ⟨0, by decide⟩, fun _ _ => ⟨0, by decide⟩⟩,
        fun index => (($borrowProjection)[index]?).getD ⟨0, by decide⟩⟩))
    let helperAssertions := mkIdent (name.getId ++ `helperAssertions)
    let helperTerms ← helpers.mapM (assertionSyntax originalCount)
    Export.emit (← `(noncomputable def $helperAssertions : List Source.HelperAssertion := [$helperTerms,*]))
    let helperScope := mkIdent (name.getId ++ `helperReferencesValid)
    Export.emit (← `(theorem $helperScope : ($helperAssertions).all (fun assertion =>
      match assertion with
      | .zero field | .boolean field =>
          field.referencesValid $(quote originalCount) $(quote history.size) 0 $(quote borrows.size) false) = true := by decide +kernel))
    let mut originalTerms ← pair.source.statements.mapM (statementSyntax originalCount n)
    for wire in pair.source.booleans do
      unless wire < originalCount do throwError "original Boolean escapes source scope"
      let atom ← atomSyntax wire n
      originalTerms := originalTerms.push (← mulSyntax n atom (← addSyntax n atom (← `(Expression.constant (-1)))))
    let mut sources : Array (TSyntax `term) := #[]
    for index in [:originalTerms.size] do
      let expression := mkIdent (name.getId ++ Name.mkSimple s!"originalExpression{index}")
      Export.emit (← `(def $expression : Expression $(quote n) Source.BaseField := $(originalTerms[index]!)))
      sources := sources.push (← `(($expression).polynomial))
    let sourceName := mkIdent (name.getId ++ `source)
    Export.emit (← `(noncomputable def $sourceName : List (Polynomial $(quote n) Source.BaseField) :=
      [$sources,*] ++ ($helperAssertions).map (Source.HelperAssertion.polynomial $helperPlacement)))
    let mut gateReferences : Array (TSyntax `ident) := #[]
    for index in [:gates.size] do
      let gate := mkIdent (name.getId ++ Name.mkSimple s!"gate{index}")
      Export.emit (← `(def $gate : ArithmeticGate $(quote m) Source.BaseField := $(gates[index]!)))
      gateReferences := gateReferences.push gate
    let extensionData := mkIdent (name.getId ++ `extensionData)
    let extension := mkIdent (name.getId ++ `extension)
    let extensions ← (cert.extension.extract n m).mapM (polynomialSyntax n)
    Export.emit (← `(def $extensionData : Vector (Polynomial $(quote n) Source.BaseField) $(quote (m - n)) := #v[$extensions,*]))
    Export.emit (← `(def $extension (index : Fin $(quote m)) : Polynomial $(quote n) Source.BaseField :=
      initialExtension (by decide : $(quote n) ≤ $(quote m)) (fun coordinate => ($extensionData)[coordinate]) index))
    let artifact := mkIdent (name.getId ++ `artifact)
    Export.emit (← `(noncomputable def $artifact : ArithmeticExtension $(quote n) $(quote m) Source.BaseField :=
      ⟨$sourceName, [$gateReferences,*], ($projection), $extension⟩))
    let coordinates := mkIdent (name.getId ++ `inputCoordinates)
    Export.emit (← `(theorem $coordinates (wire : Fin $(quote n)) :
      ($bank).address (($artifact).projection wire) = ($inputBank).address wire :=
      WireBank.ofList_prefix $addressesName $inputsName (by decide) (by decide) (by decide) $initialSegment wire))
    let forwardData := mkIdent (name.getId ++ `forwardData)
    let sourceSize := originalTerms.size + helpers.size
    let forwardTerms ← cert.forward.mapM (combinationSyntax n sourceSize)
    Export.emit (← `(noncomputable def $forwardData : Vector (Combination ($artifact).source) $(quote gates.size) := #v[$forwardTerms,*]))
    unless cert.backward.size == sourceSize do throwError "full arithmetic certificate omits source obligations"
    let backwardData := mkIdent (name.getId ++ `backwardData)
    let backwardTerms ← cert.backward.mapM (combinationSyntax m gates.size)
    Export.emit (← `(noncomputable def $backwardData : Vector (Combination ($artifact).translation.lowered) $(quote sourceSize) := #v[$backwardTerms,*]))
    let certificateName := mkIdent (name.getId ++ `certificate)
    Export.emit (← `(noncomputable def $certificateName : Certificate ($artifact).translation :=
      ⟨fun index => ($backwardData)[index], fun index => ($forwardData)[index]⟩))

end Airbender.Compiler.FullArithmeticImport
