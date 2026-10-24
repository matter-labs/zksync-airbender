import GKRProtocol.LookupFields
import Lean

namespace Airbender.Compiler.LookupImport
open Lean Elab Command
set_option warningAsError true

structure RowCertificate where
  kind : String
  source_index : Nat
  native_index : Nat
  fields : Array Import.EncodedCombination
  deriving FromJson

structure LookupCertificate where
  format_version : Nat
  addresses : Array GKRAddress
  decoder_gate : Option (Fixed 3 Nat)
  rows : Array RowCertificate
  deriving FromJson

private def finSyntax (index bound : Nat) : CommandElabM (TSyntax `term) := do
  unless index < bound do throwError "lookup certificate index {index} outside bound {bound}"
  `(⟨$(quote index), by decide⟩)

private def coefficientSyntax (coefficient : Coefficient) : CommandElabM (TSyntax `term) :=
  `(Coefficient.mk ⟨$(quote coefficient.raw.val), by decide⟩)

private def fieldSyntax (coefficient : Coefficient) : CommandElabM (TSyntax `term) :=
  `((($(quote coefficient.raw.val) : Source.BaseField) * $(quote montgomeryInverse)))

private def sourceIndex (bound index : Nat) : CommandElabM Unit :=
  unless index < bound do throwError "lookup input is outside original source variables"

private def inputSyntax (bound : Nat) : Source.LookupInput → CommandElabM (TSyntax `term)
  | .Variable index => do
      sourceIndex bound index
      `(Source.LookupInput.Variable $(quote index))
  | .Expression terms constant => do
      let terms ← terms.mapM fun (coefficient, index) => do
        sourceIndex bound index
        `(($(← coefficientSyntax coefficient), $(quote index)))
      `(Source.LookupInput.Expression #[$terms,*] $(← coefficientSyntax constant))

private def tableSyntax (bound : Nat) : Source.LookupTable → CommandElabM (TSyntax `term)
  | .Variable index => do
      sourceIndex bound index
      `(Source.LookupTable.Variable $(quote index))
  | .Constant table => do
      let .ok name := (toJson table).getStr? | throwError "native source table is not an enum name"
      let constructor := mkIdent (`Airbender.Compiler.Source.Table ++ Name.mkSimple name)
      `(Source.LookupTable.Constant $constructor)
  | .Expression expression => do
      `(Source.LookupTable.Expression $(← inputSyntax bound expression))

private def sourceFieldSyntax (bound : Nat) : Source.EncodedField → CommandElabM (TSyntax `term)
  | .input expression => do
      `(Source.EncodedField.input $(← inputSyntax bound expression))
  | .table selection => do
      `(Source.EncodedField.table $(← tableSyntax bound selection))
  | .familyMask bits => do
      for index in bits do sourceIndex bound index
      `(Source.EncodedField.familyMask $(quote bits))
  | .zero => `(Source.EncodedField.zero)

private def canonicalAddress (circuit : Circuit) (address : GKRAddress) : CommandElabM GKRAddress := do
  match address with
  | .ScratchSpace index =>
      let [(_, target)] := (circuit.scratch_space_mapping_rev.entries.filter (·.1 == index)).toList
        | throwError "missing or ambiguous scratch reverse mapping"
      let [(forward, _)] := (circuit.scratch_space_mapping.filter (·.2 == index)).toList
        | throwError "missing or ambiguous scratch forward mapping"
      unless forward == target do throwError "scratch storage mapping is not an inverse"
      unless index < circuit.scratch_space_size do throwError "scratch storage alias outside allocation"
      match target with
      | .InnerLayer _ _ => return target
      | _ => throwError "scratch storage alias is not an intermediate GKR wire"
  | _ => return address

private def addressSyntax (circuit : Circuit) (addresses : Array GKRAddress)
    (address : GKRAddress) : CommandElabM (TSyntax `term) := do
  let address ← canonicalAddress circuit address
  let found := addresses.toList.zipIdx.filter (fun (candidate, _) => candidate == address)
  let [(_, index)] := found | throwError "missing or ambiguous native lookup address"
  `(Compiler.Expression.atom $(← finSyntax index addresses.size))

private def linearSyntax (circuit : Circuit) (addresses : Array GKRAddress)
    (relation : LinearRelation) : CommandElabM (TSyntax `term) := do
  let mut result ← `(Compiler.Expression.constant $(← fieldSyntax relation.constant))
  for (coefficient, address) in relation.linear_terms do
    result ← `(Compiler.Expression.add $result
      (Compiler.Expression.mul (Compiler.Expression.constant $(← fieldSyntax coefficient))
        $(← addressSyntax circuit addresses address)))
  return result

private def polynomialSyntax (arity : Nat) (encoded : Import.EncodedPolynomial) : CommandElabM (TSyntax `term) := do
  let terms ← encoded.mapM fun (coefficient, monomial) => do
    unless coefficient < babyBearModulus do throwError "noncanonical lookup certificate coefficient"
    let wires ← monomial.mapM fun index => finSyntax index arity
    `((($(quote coefficient) : Source.BaseField), [$wires,*]))
  `([$terms,*])

private def combinationSyntax (arity count : Nat) (encoded : Import.EncodedCombination) : CommandElabM (TSyntax `term) := do
  let terms ← encoded.mapM fun (polynomial, index) => do
    `(($(← polynomialSyntax arity polynomial), $(← finSyntax index count)))
  `([$terms,*])

private def checksSyntax (proofs : Array (TSyntax `ident)) : CommandElabM (TSyntax `term) := do
  let mut result ← `(Compiler.BoolChecks.nil)
  for proof in proofs.reverse do result ← `(Compiler.BoolChecks.cons $proof $result)
  return result

private def originalPlacement (pair : Import.Pair) (index : Nat) : CommandElabM GKRAddress := do
  let [(_, address)] := (pair.circuit.placement_data.entries.filter (·.1 == index)).toList
    | throwError "missing or ambiguous original source placement"
  return address

private def decoderInput (pair : Import.Pair) (cert : LookupCertificate) :
    CommandElabM (Option (GKRAddress × VectorLookupRelation)) := do
  let mut found : Array (Array Nat × GKRRelation) := #[]
  for h : layer in [:pair.circuit.layers.size] do
    let description := pair.circuit.layers[layer]
    for (container, gates) in [(0, description.gates), (1, description.gates_with_external_connections)] do
      for h : index in [:gates.size] do
        let relation := gates[index].enforced_relation
        match relation with
        | .LookupWithDensAndSetupExpressions _ _ _ | .LookupWithCachedDensAndSetup _ _ _ =>
            found := found.push (#[layer, container, index], relation)
        | _ => pure ()
  match cert.decoder_gate, found.toList with
  | none, [] => return none
  | some selection, [(location, relation)] =>
      unless selection.values == location do throwError "decoder leaf selector does not match actual graph"
      match relation with
      | .LookupWithDensAndSetupExpressions input _ _ =>
          unless input.2.lookup_set_index == 18446744073709551615 do
            throwError "decoder witness selector is not the native formal set index"
          return some input
      | .LookupWithCachedDensAndSetup input _ _ =>
          let [mask, cached] := input.values.toList | throwError "invalid cached decoder input arity"
          let caches : Array (GKRAddress × GKRCacheRelation) := pair.circuit.layers.flatMap (·.cached_relations)
          let [(_, cachedRelation)] := (caches.filter (·.1 == cached)).toList
            | throwError "decoder cache is missing or ambiguous"
          let GKRCacheRelation.VectorizedLookup relation := cachedRelation
            | throwError "decoder cache has wrong relation type"
          unless relation.lookup_set_index == 18446744073709551615 do
            throwError "cached decoder witness selector is not the native formal set index"
          return some (mask, relation)
      | _ => throwError "unsupported masked decoder relation"
  | _, _ => throwError "source decoder must have exactly one actual graph leaf"

syntax (name := importLookupFields) "import_compiler_lookup_fields " ident " from " str
  " source " str " certificate " str : command

elab_rules : command
  | `(import_compiler_lookup_fields $name:ident from $pairPath:str source $sourcePath:str certificate $certificatePath:str) => do
    let .ok pairJson := Json.parse (← IO.FS.readFile pairPath.getString) | throwError "invalid native pair JSON"
    let .ok sourceJson := Json.parse (← IO.FS.readFile sourcePath.getString) | throwError "invalid native source JSON"
    let pair ← match fromJson? (α := Import.Pair) pairJson with
      | .ok pair => pure pair
      | .error error => throwError "invalid native pair: {error}"
    let snapshot ← match fromJson? (α := Source.Snapshot) sourceJson with
      | .ok captured => pure captured
      | .error error => throwError "invalid native source capture: {error}"
    let cert ← match Json.parse (← IO.FS.readFile certificatePath.getString) >>= (fromJson? (α := LookupCertificate)) with
      | .ok cert => pure cert
      | .error error => throwError "invalid lookup certificate: {error}"
    unless pair.format_version == 1 && snapshot.format_version == 1 && cert.format_version == 1 do
      throwError "unsupported lookup translation version"
    let .ok originalSource := pairJson.getObjVal? "source" | throwError "missing original source"
    let .ok capturedSource := sourceJson.getObjVal? "source" | throwError "missing captured source"
    unless snapshot.family == pair.family && snapshot.cached == pair.cached &&
        originalSource == capturedSource do
      throwError "source sidecar is detached from compilation"
    let circuit := pair.circuit
    let n := pair.source.num_variables
    let m := cert.addresses.size
    unless 0 < n && n ≤ m do throwError "invalid source or lower address count"
    unless cert.addresses.toList.eraseDups.length == m do throwError "aliased lookup certificate address bank"
    for index in [:n] do
      let some actual := cert.addresses[index]? | throwError "source placement outside address bank"
      unless actual == (← originalPlacement pair index) do
        throwError "lookup certificate changes original source placement"
    unless snapshot.semantic_inputs.range_checks.all (fun query => query.width == 8 || query.width == 16) do
      throwError "unsupported authored range-check width"
    let requests := Source.genericRequests snapshot.semantic_inputs
    let scalar := Source.range16Requests snapshot.semantic_inputs
    let executor := snapshot.semantic_inputs.executor_machine_state
    let bits := snapshot.semantic_inputs.circuit_family_bitmask.toList
    let includeId := circuit.tables_ids_in_generic_lookups
    if !includeId then
      match requests with
      | [] => pure ()
      | first :: rest =>
          unless executor.isNone do throwError "mixed decoder lookup omitted table selectors"
          let .Constant fixed := first.table | throwError "omitted dynamic table selector"
          unless rest.all (fun request => match request.table with
            | .Constant table => decide (table = fixed)
            | _ => false) do throwError "omitted selector for distinct source tables"
    let decoderWidth := (executor.map (fun state => (Source.decoderFields state bits).length)).getD 0
    let sourceWidth := requests.foldl (fun width request => max width request.row.size) 0
    let width := max decoderWidth sourceWidth + if includeId then 1 else 0
    unless width == circuit.generic_lookup_tables_width do throwError "lookup encoding width changed"
    unless requests.length == circuit.generic_lookups.size && scalar.length == circuit.range_check_16_lookup_expressions.size &&
        requests.length + (if executor.isSome then 1 else 0) == circuit.num_generic_lookups &&
        executor.isSome == circuit.has_decoder_lookup do throwError "source lookup coverage changed"
    unless cert.rows.size == requests.length + scalar.length + (if executor.isSome then 1 else 0) do
      throwError "lookup field certificate omits source requests"
    let sourcePlacementName := mkIdent (name.getId ++ `sourcePlacement)
    elabCommand (← `(def $sourcePlacementName (index : Nat) : Fin $(quote m) :=
      if h : index < $(quote n) then ⟨index, Nat.lt_of_lt_of_le h (by decide)⟩ else ⟨0, by decide⟩))
    let mut copies : Array (TSyntax `term) := #[]
    for layer in circuit.layers do
      for gate in layer.gates ++ layer.gates_with_external_connections do
        match gate.enforced_relation with
        | .CopyInBaseField input output =>
            let copyName := mkIdent (name.getId ++ Name.mkSimple s!"copy{copies.size}")
            let lhs ← addressSyntax circuit cert.addresses output
            let rhs ← addressSyntax circuit cert.addresses input
            elabCommand (← `(noncomputable def $copyName : Compiler.Polynomial $(quote m) Source.BaseField :=
              Compiler.add ($lhs).polynomial (Compiler.negate ($rhs).polynomial)))
            copies := copies.push (← `($copyName))
        | _ => pure ()
    let copiesName := mkIdent (name.getId ++ `copyRelations)
    elabCommand (← `(noncomputable def $copiesName : List (Compiler.Polynomial $(quote m) Source.BaseField) := [$copies,*]))
    let mut rows : Array (List Source.EncodedField × Array (TSyntax `term)) := #[]
    for sourceIndex in [:requests.length] do
      let some row := cert.rows[sourceIndex]? | throwError "missing generic row certificate"
      let some request := requests[sourceIndex]? | throwError "missing original generic request"
      unless row.kind == "generic" && row.source_index == sourceIndex do throwError "generic row order changed"
      let some native := circuit.generic_lookups[row.native_index]? | throwError "generic native selector outside bank"
      unless native.lookup_set_index == sourceIndex do throwError "generic lookup set index changed"
      let fields := Source.queryFields width includeId request
      rows := rows.push (fields, ← native.columns.mapM (linearSyntax circuit cert.addresses))
    for sourceIndex in [:scalar.length] do
      let some row := cert.rows[requests.length + sourceIndex]? | throwError "missing scalar row certificate"
      let some request := scalar[sourceIndex]? | throwError "missing original scalar request"
      unless row.kind == "range16" && row.source_index == sourceIndex do throwError "scalar row order changed"
      let some native := circuit.range_check_16_lookup_expressions[row.native_index]? | throwError "scalar native selector outside bank"
      unless native.lookup_set_index == sourceIndex do throwError "scalar lookup set index changed"
      rows := rows.push ([.input request], #[← linearSyntax circuit cert.addresses native.input])
    let decoder ← decoderInput pair cert
    match executor, decoder with
    | none, none => pure ()
    | some state, some (mask, native) =>
        let some row := cert.rows[requests.length + scalar.length]? | throwError "missing decoder row certificate"
        unless row.kind == "decoder" && row.source_index == 0 && row.native_index == 0 do
          throwError "decoder row identity changed"
        let columns ← native.columns.mapM (linearSyntax circuit cert.addresses)
        rows := rows.push (Source.decoderEncodedFields width includeId state bits,
          #[← addressSyntax circuit cert.addresses mask] ++ columns)
    | _, _ => throwError "source and graph decoder presence differ"
    let mut fields : Array (TSyntax `term) := #[]
    let mut proofs := #[]
    for h : rowIndex in [:rows.size] do
      let (sourceFields, lowerFields) := rows[rowIndex]
      let some rowCertificate := cert.rows[rowIndex]? | throwError "missing field row certificate"
      let witnesses := rowCertificate.fields
      unless sourceFields.length == lowerFields.size && witnesses.size == lowerFields.size do
        throwError "lookup field width or identity coverage changed"
      for column in [:lowerFields.size] do
        let some sourceField := sourceFields[column]? | throwError "missing source field"
        let fieldName := mkIdent (name.getId ++ Name.mkSimple s!"field{rowIndex}_{column}")
        let proof := mkIdent (name.getId ++ Name.mkSimple s!"fieldChecked{rowIndex}_{column}")
        elabCommand (← `(noncomputable def $fieldName : Compiler.LookupFieldAgreement $copiesName :=
          ⟨$(← sourceFieldSyntax n sourceField), $(lowerFields[column]!),
            $(← combinationSyntax m copies.size witnesses[column]!)⟩))
        elabCommand (← `(theorem $proof : ($fieldName).check $sourcePlacementName = true := by decide +kernel))
        fields := fields.push (← `($fieldName))
        proofs := proofs.push proof
    let fieldsName := mkIdent (name.getId ++ `fields)
    elabCommand (← `(noncomputable def $fieldsName : List (Compiler.LookupFieldAgreement $copiesName) := [$fields,*]))
    let checkedName := mkIdent (name.getId ++ `checked)
    elabCommand (← `(theorem $checkedName : ($fieldsName).all (fun field => field.check $sourcePlacementName) = true :=
      Compiler.BoolChecks.all_true $(← checksSyntax proofs)))

end Airbender.Compiler.LookupImport
