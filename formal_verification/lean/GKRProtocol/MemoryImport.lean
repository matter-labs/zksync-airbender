import GKRProtocol.MemoryCertificate
import GKRProtocol.MemoryRequests
import GKRProtocol.NativeProductImport
import GKRProtocol.LookupSourceData

namespace Airbender.Compiler.MemoryImport
open Lean Elab Command
set_option warningAsError true
set_option maxRecDepth 32768

private instance : ObjectKey String where
  decode := Except.ok
  encode := id

structure LeafSelector where
  native_leaf : Nat
  locator : Fixed 2 Nat
  expansion : Array Nat
  deriving FromJson

structure MaskSelector where
  address : GKRAddress
  witness : Import.EncodedCombination
  deriving FromJson

structure GroupSelector where
  native_leaves : Array Nat
  source_labels : Array Nat
  witnesses : Array Import.EncodedCombination
  mask : Option MaskSelector
  deriving FromJson

structure Selectors where
  format_version : Nat
  addresses : Array GKRAddress
  leaves : Array LeafSelector
  groups : ObjectMap String GroupSelector
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

private def wordSyntax (bound : Nat) (word : Source.MemoryWord) : CommandElabM (TSyntax `term) := do
  `(Source.MemoryWord.mk $(← fieldSyntax bound word.low) $(← fieldSyntax bound word.high))

private def rowSyntax (bound : Nat) (row : Source.MemoryRow) : CommandElabM (TSyntax `term) := do
  `(Source.MemoryRow.mk $(← fieldSyntax bound row.addressSpace) $(← wordSyntax bound row.address)
    $(← wordSyntax bound row.timestamp) $(← wordSyntax bound row.data))

private def definitionSyntax (definition : LookupSourceData.Definition) : CommandElabM (TSyntax `term) := do
  let program ← match definition with
    | .cache _ relation => CacheImport.program relation
    | .copy _ address => do `(AffineProgram.input (R := CacheCoefficient) $(← addressSyntax address))
    | .scalar _ row => CacheImport.program (.SingleColumnLookup row 0)
    | .vector _ row => CacheImport.program (.VectorizedLookup row)
  `(AffineDefinition.mk $(← addressSyntax definition.output) $program)

private def pairSyntax (addresses : Fixed 2 GKRAddress) : CommandElabM (TSyntax `term) := do
  let [low, high] := addresses.values.toList | throwError "memory location word width changed"
  `(($(← addressSyntax low), $(← addressSyntax high)))

private def correspondenceSyntax (proofs : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let mut result ← `(List.Forall₂.nil)
  for proof in proofs.reverse do result ← `(List.Forall₂.cons $proof $result)
  return result

syntax (name := importSourceMemory) "import_source_memory " ident " from " str " source " str
  " selectors " str " word_bits " num " native_model " ident " typing " ident : command

elab_rules : command
  | `(import_source_memory $name:ident from $pairPath:str source $sourcePath:str selectors $selectorText:str
      word_bits $wordBitsNumber:num native_model $nativePrefix:ident typing $typingName:ident) => do
    let pairJson ← match Json.parse (← IO.FS.readFile pairPath.getString) with
      | .ok parsed => pure parsed | .error error => throwError "{error}"
    let sourceJson ← match Json.parse (← IO.FS.readFile sourcePath.getString) with
      | .ok parsed => pure parsed | .error error => throwError "{error}"
    let pair ← match fromJson? (α := Import.Pair) pairJson with
      | .ok parsed => pure parsed | .error error => throwError "{error}"
    let snapshot ← match fromJson? (α := Source.Snapshot) sourceJson with
      | .ok parsed => pure parsed | .error error => throwError "{error}"
    let cert ← match Json.parse selectorText.getString >>= (fromJson? (α := Selectors)) with
      | .ok parsed => pure parsed | .error error => throwError "{error}"
    let .ok originalSource := pairJson.getObjVal? "source" | throwError "missing compiler input"
    let .ok retainedSource := sourceJson.getObjVal? "source" | throwError "missing retained input"
    unless pair.format_version == 1 && snapshot.format_version == 1 && cert.format_version == 1 &&
        pair.family == snapshot.family && pair.cached == snapshot.cached && originalSource == retainedSource do
      throwError "memory source is detached from its actual compilation"
    let sourceCount := pair.source.num_variables
    let arity := cert.addresses.size
    unless 0 < sourceCount && sourceCount ≤ arity && cert.addresses.toList.eraseDups.length == arity do
      throwError "memory address bank is empty or aliased"
    for index in [:sourceCount] do
      let [(_, actual)] := (pair.circuit.placement_data.entries.filter (·.1 == index)).toList
        | throwError "missing or ambiguous original memory variable placement"
      unless cert.addresses[index]? == some actual do throwError "memory bank changes original source placement"
    let requests ← match Source.memoryRequests snapshot.semantic_inputs with
      | .ok requests => pure requests | .error error => throwError "{error}"
    let wordBits := wordBitsNumber.getNat
    unless wordBits == 2 || wordBits == 3 do throwError "unsupported source initialization word width"
    if snapshot.configuration.inline_init_teardown_pairs > 0 then
      unless (pair.circuit.memory_layout.inits_and_teardowns_word_bits.map (·.val)) == some wordBits do
        throwError "native initialization word width differs from source compile parameter"
    let initial := Source.initializationRequests snapshot.configuration.inline_init_teardown_pairs wordBits
      snapshot.configuration.trace_len_log2
    let sourceGroups := #[("memoryRead", requests.reads.toList), ("memoryWrite", requests.writes.toList),
      ("initializationRead", initial.map (·.1)), ("initializationWrite", initial.map (·.2))]
    unless 2 ^ snapshot.configuration.trace_len_log2 == pair.circuit.trace_len do
      throwError "source memory trace domain differs from native compilation"
    let expectedGroups := if initial.isEmpty then #["memoryRead", "memoryWrite"] else
      #["memoryRead", "memoryWrite", "initializationRead", "initializationWrite"]
    let mut nativeGroups : Array (String × GKRAddress) := #[]
    for (kind, outputs) in pair.circuit.global_output_map.entries do
      let some stem := (match kind with
        | .PermutationProduct => some "memory" | .InitsAndTeardownsProduct => some "initialization" | _ => none) | continue
      let [read, write] := outputs.toList | throwError "actual native memory output width changed"
      nativeGroups := nativeGroups ++ #[(stem ++ "Read", read), (stem ++ "Write", write)]
    unless nativeGroups.size == expectedGroups.size && cert.groups.entries.size == expectedGroups.size &&
        expectedGroups.all (fun stem => nativeGroups.any (fun entry => entry.1 == stem) &&
          cert.groups.entries.any (fun entry => entry.1 == stem)) do
      throwError "source/native memory output group coverage changed"
    for (stem, rows) in sourceGroups do
      let sourceRows := mkIdent (name.getId ++ Name.mkSimple s!"{stem}Rows")
      let terms ← rows.toArray.mapM (rowSyntax sourceCount)
      elabCommand (← `(noncomputable def $sourceRows : List Source.MemoryRow := [$terms,*]))
    let sourceScope := mkIdent (name.getId ++ `sourceReferencesValid)
    let readRows := mkIdent (name.getId ++ `memoryReadRows)
    let writeRows := mkIdent (name.getId ++ `memoryWriteRows)
    let initialReads := mkIdent (name.getId ++ `initializationReadRows)
    let initialWrites := mkIdent (name.getId ++ `initializationWriteRows)
    elabCommand (← `(theorem $sourceScope :
      ($readRows ++ $writeRows ++ $initialReads ++ $initialWrites).all (fun row => row.fields.all
        (Source.MemoryField.referencesValid $(quote sourceCount) $(quote pair.circuit.memory_layout.ram_access_sets.size)
          $(quote pair.circuit.memory_layout.teardown_sets.size) $(quote (!initial.isEmpty)))) = true := by decide +kernel))
    let addresses := mkIdent (name.getId ++ `addresses)
    let addressTerms ← cert.addresses.mapM addressSyntax
    elabCommand (← `(def $addresses : List GKRAddress := [$addressTerms,*]))
    let wirePlacement := mkIdent (name.getId ++ `wirePlacement)
    let bank := mkIdent (name.getId ++ `bank)
    elabCommand (← `(def $wirePlacement (address : GKRAddress) : Fin $(quote arity) :=
      let index := ($addresses).findIdx (fun candidate => addressEqual candidate address)
      if bound : index < $(quote arity) then ⟨index, bound⟩ else ⟨0, by decide⟩))
    elabCommand (← `(def $bank : WireBank $(quote arity) :=
      ⟨fun index => (($addresses)[index.val]?).getD (.BaseLayerWitness 0), $wirePlacement⟩))
    let placement := mkIdent (name.getId ++ `sourcePlacement)
    let readTimesName := mkIdent (name.getId ++ `readTimestamps)
    let mut readTimes : Array (TSyntax `term) := #[]
    for query in pair.circuit.memory_layout.ram_access_sets do
      let timestamps := match query with | .Readonly read => read.read_timestamp | .Write write => write.read_timestamp
      let [low, high] := timestamps.values.toList | throwError "native history timestamp width changed"
      readTimes := readTimes.push (← `(($(← addressSyntax (.BaseLayerMemory low)), $(← addressSyntax (.BaseLayerMemory high)))))
    elabCommand (← `(def $readTimesName : List (GKRAddress × GKRAddress) := [$readTimes,*]))
    let teardownTimes := mkIdent (name.getId ++ `teardownTimestamps)
    let teardownValues := mkIdent (name.getId ++ `teardownValues)
    let times ← pair.circuit.memory_layout.teardown_sets.mapM (fun entry => pairSyntax entry.1)
    let values ← pair.circuit.memory_layout.teardown_sets.mapM (fun entry => pairSyntax entry.2)
    elabCommand (← `(def $teardownTimes : List (GKRAddress × GKRAddress) := [$times,*]))
    elabCommand (← `(def $teardownValues : List (GKRAddress × GKRAddress) := [$values,*]))
    let projectionInputs := mkIdent (name.getId ++ `projectionInputs)
    let projectionInBank := mkIdent (name.getId ++ `projectionInBank)
    let projectionRoles := mkIdent (name.getId ++ `projectionRoles)
    let extra ← if initial.isEmpty then `([]) else `([GKRAddress.VirtualSetup .InitsAndTeardownsLow,
      GKRAddress.VirtualSetup .InitsAndTeardownsHigh])
    elabCommand (← `(def $projectionInputs : List GKRAddress :=
      ($readTimesName ++ $teardownTimes ++ $teardownValues).flatMap (fun locations => [locations.1, locations.2]) ++ $extra))
    elabCommand (← `(theorem $projectionInBank : ($bank).inputCheck $projectionInputs = true := by decide +kernel))
    elabCommand (← `(theorem $projectionRoles : ($projectionInputs).all
      (fun address => ($typingName).compatible (address, .base)) = true := by decide +kernel))
    let locateWord := mkIdent (name.getId ++ `wordPlacement)
    elabCommand (← `(def $locateWord (words : List (GKRAddress × GKRAddress)) (query : Nat) (limb : Fin 2) : Fin $(quote arity) :=
      let locations := (words[query]?).getD (.BaseLayerMemory 0, .BaseLayerMemory 0)
      $wirePlacement (if limb.val = 0 then locations.1 else locations.2)))
    elabCommand (← `(def $placement : Source.MemoryPlacement $(quote arity) :=
      ⟨fun index => if bound : index < $(quote sourceCount) then
          ⟨index, Nat.lt_of_lt_of_le bound (by decide)⟩ else ⟨0, by decide⟩,
        $locateWord $readTimesName,
        fun limb => $wirePlacement (.VirtualSetup (if limb.val = 0 then .InitsAndTeardownsLow else .InitsAndTeardownsHigh)),
        $locateWord $teardownTimes, $locateWord $teardownValues⟩))
    let sourceValues := mkIdent (name.getId ++ `sourceValues)
    let sourceExecute := mkIdent (name.getId ++ `sourceExecute)
    elabCommand (← `(def $sourceValues (base : GKRAddress → Source.BaseField) : Source.MemoryValues :=
      ($placement).project (base ∘ ($bank).address)))
    elabCommand (← `(def $sourceExecute : Source.MemoryField := $(← fieldSyntax sourceCount (.input (.Variable requests.execute)))))
    let gates := pair.circuit.layers.flatMap (fun layer => layer.gates ++ layer.gates_with_external_connections)
    let mut copies : Array (TSyntax `term) := #[]
    for gate in gates do
      if let .CopyInBaseField input output := gate.enforced_relation then
        let some outIndex := cert.addresses.findIdx? (· == output) | throwError "actual base-copy output omitted from memory bank"
        let some inIndex := cert.addresses.findIdx? (· == input) | throwError "actual base-copy input omitted from memory bank"
        copies := copies.push (← `(Compiler.add (Compiler.atom $(← finSyntax outIndex arity))
          (Compiler.negate (Compiler.atom $(← finSyntax inIndex arity)))))
    let copyRelations := mkIdent (name.getId ++ `copyRelations)
    elabCommand (← `(noncomputable def $copyRelations : List (Polynomial $(quote arity) Source.BaseField) := [$copies,*]))
    let definitionsName := mkIdent (name.getId ++ `definitions)
    let definitions ← (LookupSourceData.definitions pair.circuit).mapM definitionSyntax
    elabCommand (← `(noncomputable def $definitionsName : List AffineDefinition := [$definitions,*]))
    let memoryCaches := pair.circuit.layers.flatMap fun layer => layer.cached_relations.filterMap fun (address, relation) =>
      match relation with | .MemoryTuple _ => some address | _ => none
    let mut actualLeaves : Array (Array (TSyntax `term)) := #[]
    let mut primitiveCount := 0
    for gate in gates do
      if let some pieces ← NativeProductImport.pieces pair.circuit memoryCaches primitiveCount gate.enforced_relation then
        actualLeaves := actualLeaves.push pieces.leaves
        primitiveCount := primitiveCount + pieces.leaves.size
      else actualLeaves := actualLeaves.push #[]
    unless cert.leaves.size == primitiveCount do throwError "actual memory registry coverage changed"
    let registry := mkIdent (nativePrefix.getId ++ `registry)
    for h : position in [:cert.leaves.size] do
      let selected := cert.leaves[position]
      unless selected.native_leaf == position do throwError "memory registry selector order changed"
      let [gateIndex, operand] := selected.locator.values.toList | throwError "invalid memory operand locator"
      let some gateLeaves := actualLeaves[gateIndex]? | throwError "memory operand gate selector outside native graph"
      let some actual := gateLeaves[operand]? | throwError "memory operand selector outside actual native gate"
      let leaf := mkIdent (name.getId ++ Name.mkSimple s!"leaf{position}")
      let found := mkIdent (name.getId ++ Name.mkSimple s!"leafFound{position}")
      let raw := mkIdent (name.getId ++ Name.mkSimple s!"raw{position}")
      let present := mkIdent (name.getId ++ Name.mkSimple s!"expansionPresent{position}")
      let expanded := mkIdent (name.getId ++ Name.mkSimple s!"expanded{position}")
      let indices : Array (TSyntax `term) := selected.expansion.map quote
      elabCommand (← `(noncomputable def $leaf : LookupPayload := $actual))
      elabCommand (← `(theorem $found : ($registry)[$(quote position)]? = some $leaf := by rfl))
      elabCommand (← `(noncomputable def $raw : LookupPayload :=
        (LookupPayload.expand $definitionsName [$indices,*] $leaf).getD (.constant (.natural 0))))
      elabCommand (← `(theorem $present : (LookupPayload.expand $definitionsName [$indices,*] $leaf).isSome = true := by decide +kernel))
      elabCommand (← `(theorem $expanded : LookupPayload.expand $definitionsName [$indices,*] $leaf = some $raw :=
        option_eq_some_getD $present (.constant (.natural 0))))
      let roles := mkIdent (name.getId ++ Name.mkSimple s!"roles{position}")
      let inBank := mkIdent (name.getId ++ Name.mkSimple s!"inBank{position}")
      elabCommand (← `(theorem $roles : ($raw).inputs.all (fun address => ($typingName).compatible (address, .base)) = true := by decide +kernel))
      elabCommand (← `(theorem $inBank : ($bank).inputCheck ($raw).inputs = true := by decide +kernel))
    for (stem, selection) in cert.groups.entries do
      let some (_, rows) := sourceGroups.find? (fun entry => entry.1 == stem) | throwError "unknown source memory group"
      unless selection.native_leaves.size == selection.source_labels.size &&
          selection.witnesses.size == selection.source_labels.size do throwError "incomplete source memory occurrence correspondence"
      let sourceRows := mkIdent (name.getId ++ Name.mkSimple s!"{stem}Rows")
      let terms := mkIdent (name.getId ++ Name.mkSimple s!"{stem}Terms")
      elabCommand (← `(noncomputable def $terms {R : Type} [CommRing R]
        (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (assignment : TypedAssignment R) : List R :=
        ($sourceRows).map (fun row => row.fingerprint ($sourceValues assignment.base) hom challenges)))
      let mut matchingProofs : Array (TSyntax `term) := #[]
      for occurrence in [:selection.native_leaves.size] do
        let some nativeIndex := selection.native_leaves[occurrence]? | throwError "missing native memory occurrence"
        let some sourceIndex := selection.source_labels[occurrence]? | throwError "missing source memory occurrence"
        let some _ := rows[sourceIndex]? | throwError "source memory row selector outside independent request bank"
        let raw := mkIdent (name.getId ++ Name.mkSimple s!"raw{nativeIndex}")
        let candidate := mkIdent (name.getId ++ Name.mkSimple s!"{stem}Certificate{occurrence}")
        let checked := mkIdent (name.getId ++ Name.mkSimple s!"{stem}Checked{occurrence}")
        let row ← `( (($sourceRows)[$(quote sourceIndex)]?).getD
          (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
        elabCommand (← `(noncomputable def $candidate : MemoryFingerprintCertificate $copyRelations :=
          ⟨$(← combinationSyntax (arity + 7) copies.size selection.witnesses[occurrence]!)⟩))
        elabCommand (← `(theorem $checked : ($candidate).check $row $placement $bank $raw = true := by decide +kernel))
        let found := mkIdent (name.getId ++ Name.mkSimple s!"leafFound{nativeIndex}")
        let expanded := mkIdent (name.getId ++ Name.mkSimple s!"expanded{nativeIndex}")
        let roles := mkIdent (name.getId ++ Name.mkSimple s!"roles{nativeIndex}")
        let inBank := mkIdent (name.getId ++ Name.mkSimple s!"inBank{nativeIndex}")
        let matched := mkIdent (name.getId ++ Name.mkSimple s!"{stem}Match{occurrence}")
        let some selector := cert.leaves[nativeIndex]? | throwError "memory occurrence registry index outside actual bank"
        let expansion : Array (TSyntax `term) := selector.expansion.map quote
        elabCommand (← `(theorem $matched {R : Type} [CommRing R]
          (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (assignment : TypedAssignment R)
          (defined : ∀ definition ∈ $definitionsName, definition.Holds hom challenges (assignment.value $typingName hom))
          (copies : Satisfies $copyRelations (assignment.base ∘ ($bank).address)) :
          productRegistryValue $registry hom challenges (assignment.value $typingName hom) $(quote nativeIndex) =
            (($terms hom challenges assignment)[$(quote sourceIndex)]?).getD 1 :=
          productRegistry_source_memory $found $definitionsName [$expansion,*] $expanded $candidate $row $placement
            $bank $checked $inBank $typingName $roles assignment hom challenges defined copies))
        matchingProofs := matchingProofs.push (← `($matched hom challenges assignment defined copies))
      let tree := mkIdent (nativePrefix.getId ++ Name.mkSimple s!"{stem}Product")
      let nativeReduction := mkIdent (nativePrefix.getId ++ Name.mkSimple s!"{stem}ProductReduction")
      let nativeGates := mkIdent (nativePrefix.getId ++ `gates)
      let leavesChecked := mkIdent (name.getId ++ Name.mkSimple s!"{stem}LeavesChecked")
      let coverage := mkIdent (name.getId ++ Name.mkSimple s!"{stem}SourceCoverage")
      let nativeLeaves : Array (TSyntax `term) := selection.native_leaves.map quote
      let labels : Array (TSyntax `term) := selection.source_labels.map quote
      elabCommand (← `(theorem $leavesChecked : ($tree).leaves = [$nativeLeaves,*] := by decide +kernel))
      elabCommand (← `(theorem $coverage : ([$labels,*] : List Nat).Perm (List.range ($sourceRows).length) := by decide +kernel))
      let some (_, actualOutput) := nativeGroups.find? (fun entry => entry.1 == stem) | throwError "missing actual memory output"
      let output := mkIdent (name.getId ++ Name.mkSimple s!"{stem}Output")
      elabCommand (← `(def $output : GKRAddress := $(← addressSyntax actualOutput)))
      let productEquality ← `(memory_product_translation
        (productRegistryValue $registry hom challenges (assignment.value $typingName hom)) ($terms hom challenges assignment)
        (native := ($tree).leaves) (labels := ([$labels,*] : List Nat))
        (by rw [$leavesChecked:ident]; exact $(← correspondenceSyntax matchingProofs)) $coverage)
      let result := mkIdent (name.getId ++ Name.mkSimple s!"{stem}SourceReduction")
      if stem == "memoryRead" || stem == "memoryWrite" then
        let some mask := selection.mask | throwError "source RAM output has no execution mask correspondence"
        let formula := mkIdent (nativePrefix.getId ++ Name.mkSimple s!"{stem}Formula")
        let shape := mkIdent (name.getId ++ Name.mkSimple s!"{stem}MaskShape")
        let maskField := mkIdent (name.getId ++ Name.mkSimple s!"{stem}MaskField")
        let maskChecked := mkIdent (name.getId ++ Name.mkSimple s!"{stem}MaskChecked")
        let maskInBank := mkIdent (name.getId ++ Name.mkSimple s!"{stem}MaskInBank")
        let maskRole := mkIdent (name.getId ++ Name.mkSimple s!"{stem}MaskRole")
        let maskAddress ← addressSyntax mask.address
        elabCommand (← `(theorem $shape : $formula = ProductFormula.mask $maskAddress (ProductFormula.ofTree $tree) := by rfl))
        elabCommand (← `(noncomputable def $maskField : MemoryFieldAgreement $copyRelations :=
          ⟨$sourceExecute, Expression.atom ($wirePlacement $maskAddress),
            $(← combinationSyntax arity copies.size mask.witness)⟩))
        elabCommand (← `(theorem $maskChecked : ($maskField).check $placement = true := by decide +kernel))
        elabCommand (← `(theorem $maskInBank : ($bank).inputCheck [$maskAddress] = true := by decide +kernel))
        elabCommand (← `(theorem $maskRole : ($typingName).compatible ($maskAddress, .base) = true := by decide +kernel))
        let maskValue ← `(MemoryFieldAgreement.mask_value $placement $bank $maskAddress (by rfl) $maskChecked
          $maskInBank $typingName $maskRole assignment hom copies)
        elabCommand (← `(theorem $result {R : Type} [CommRing R]
          (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (assignment : TypedAssignment R)
          (defined : ∀ definition ∈ $definitionsName, definition.Holds hom challenges (assignment.value $typingName hom))
          (copies : Satisfies $copyRelations (assignment.base ∘ ($bank).address))
          (holds : ∀ gate ∈ $nativeGates, gate.Holds hom challenges (assignment.value $typingName hom)) :
          assignment.value $typingName hom $output =
            maskProduct (hom (($sourceExecute).value ($sourceValues assignment.base))) ($terms hom challenges assignment).prod := by
          have reduced := $nativeReduction hom challenges (assignment.value $typingName hom) holds
          have products := $productEquality
          change assignment.value $typingName hom $output =
            maskProduct (assignment.value $typingName hom $maskAddress)
              ((($tree).leaves.map (productRegistryValue $registry hom challenges (assignment.value $typingName hom))).prod) at reduced
          rw [products, $maskValue:term] at reduced
          exact reduced))
      else
        unless selection.mask.isNone do throwError "initialization source product has an unexpected mask"
        elabCommand (← `(theorem $result {R : Type} [CommRing R]
          (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (assignment : TypedAssignment R)
          (defined : ∀ definition ∈ $definitionsName, definition.Holds hom challenges (assignment.value $typingName hom))
          (copies : Satisfies $copyRelations (assignment.base ∘ ($bank).address))
          (holds : ∀ gate ∈ $nativeGates, gate.Holds hom challenges (assignment.value $typingName hom)) :
          assignment.value $typingName hom $output = ($terms hom challenges assignment).prod :=
          ($nativeReduction hom challenges (assignment.value $typingName hom) holds).trans $productEquality))

end Airbender.Compiler.MemoryImport
