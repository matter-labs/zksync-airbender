import GKRProtocol.FunctionalImport

namespace Airbender.Compiler.FunctionalLinksImport
open Lean Elab Command
set_option warningAsError true

private def field (owner : Ident) (stem : String) : Ident := mkIdent (owner.getId ++ Name.mkSimple stem)
private def indexed (owner : Ident) (stem : String) (index : Nat) : Ident := field owner s!"{stem}{index}"

private def address : GKRAddress → CommandElabM (TSyntax `term)
  | .BaseLayerWitness index => `(GKRAddress.BaseLayerWitness $(quote index))
  | .BaseLayerMemory index => `(GKRAddress.BaseLayerMemory $(quote index))
  | .InnerLayer layer index => `(GKRAddress.InnerLayer $(quote layer) $(quote index))
  | .Cached layer index => `(GKRAddress.Cached $(quote layer) $(quote index))
  | _ => throwError "native base copy uses a non-column address"

private def predicates (proofs : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let mut result ← `(PredicateChecks.nil)
  for proof in proofs.reverse do result ← `(PredicateChecks.cons $proof $result)
  return result

syntax (name := importFunctionalLinks) "import_functional_links " ident " from " str
  " graph " ident " base_model " ident " typing " ident " lookup_fields " ident
  " lookup_source " ident " memory_model " ident " helper_model " ident : command

elab_rules : command
  | `(import_functional_links $name:ident from $path:str graph $graphName:ident
      base_model $baseName:ident typing $typingName:ident lookup_fields $lookupName:ident
      lookup_source $sourceName:ident memory_model $memoryName:ident helper_model $helperName:ident) => do
    let pair ← match Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := Import.Pair)) with
      | .ok pair => pure pair | .error error => throwError "{error}"
    unless pair.format_version == 1 do throwError "unsupported native functional link version"
    let mut outputs : Array (GKRAddress × Nat) := #[]
    let mut ordinal := 0
    for layer in pair.circuit.layers do
      for (output, relation) in layer.cached_relations do
        if let .SingleColumnLookup _ _ := relation then
          outputs := outputs.push (output, ordinal)
          ordinal := ordinal + 1
    let mut copies : Array (GKRAddress × GKRAddress × Nat) := #[]
    for layer in pair.circuit.layers do
      for gate in layer.gates ++ layer.gates_with_external_connections do
        match gate.enforced_relation with
        | .CopyInBaseField input output =>
            outputs := outputs.push (output, ordinal)
            copies := copies.push (output, input, ordinal)
            ordinal := ordinal + 1
        | .LinearBaseFieldRelation _ output | .MaxQuadratic _ _ output |
          .MaterializeSingleLookupInput _ output _ =>
            outputs := outputs.push (output, ordinal)
            ordinal := ordinal + 1
        | .EnforceSingleMaxQuadraticConstraint _ _ => ordinal := ordinal + 1
        | _ => pure ()
    let mut bindings : Array GKRAddress := #[]
    for definition in LookupSourceData.definitions pair.circuit do
      if outputs.any (fun entry => entry.1 == definition.output) then bindings := bindings.push definition.output
    let artifact := field baseName "artifact"
    let baseBank := field baseName "bank"
    let isBase := field graphName "isBase"
    let canonical := field graphName "canonical"
    let canonicalBase := field graphName "canonical_base"
    let canonicalAffines := field graphName "canonical_affines"
    let definitions := field graphName "definitions"
    let assignment := field name "assignment"
    let assignmentValue := field name "assignment_value"
    elabCommand (← `(noncomputable def $assignment {R : Type} [CommRing R]
      (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
      (baseValue : GKRAddress → Source.BaseField) : TypedAssignment R :=
      ⟨baseValue, $canonical hom challenges gamma baseValue⟩))
    elabCommand (← `(theorem $assignmentValue {R : Type} [CommRing R]
      (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
      (baseValue : GKRAddress → Source.BaseField) :
      ($assignment hom challenges gamma baseValue).value $typingName hom = $canonical hom challenges gamma baseValue :=
      TypedAssignment.value_from_function $typingName hom baseValue _ ($canonicalBase hom challenges gamma baseValue)))
    for (copy, index) in copies.toList.zipIdx do
      let (output, input, gateOrdinal) := copy
      let some binding := bindings.findIdx? (· == output) | throwError "base-copy recipe is absent"
      let recipe := indexed graphName "baseRecipe" binding
      let ports := indexed graphName "basePortsChecked" binding
      let identity := indexed graphName "baseRelationChecked" binding
      let gate := indexed baseName "gate" gateOrdinal
      let gateCheck := indexed baseName "gateChecked" gateOrdinal
      let result := indexed name "baseCopy" index
      elabCommand (← `(theorem $result (baseValue : GKRAddress → Source.BaseField)
        (arithmetic : ∀ gate ∈ ($artifact).gates, gate.expressionResidual (baseValue ∘ ($baseBank).address) = 0) :
        baseValue $(← address output) = baseValue $(← address input) :=
        NativeBaseRecipe.definition_of_gate $recipe $baseBank $isBase $(← address output) $gate $ports $identity
          $gateCheck (RingHom.id Source.BaseField) ⟨0, 0, fun _ => 0⟩ baseValue baseValue (fun _ _ => rfl)
          (arithmetic $gate (List.get_mem ($artifact).gates ⟨$(quote gateOrdinal), by decide⟩))))
    for (label, model, bankOwner, copiesOwner) in
        [("lookup", sourceName, sourceName, lookupName), ("memory", memoryName, memoryName, memoryName),
         ("helper", helperName, memoryName, helperName)] do
      let oldBank := field bankOwner "bank"
      let oldCopies := field copiesOwner "copyRelations"
      let oldDefinitions := field model "definitions"
      let definitionsAgree := field name (label ++ "DefinitionsAgree")
      elabCommand (← `(theorem $definitionsAgree : $definitions = $oldDefinitions := by rfl))
      let mut proofs := #[]
      for (copy, index) in copies.toList.zipIdx do
        let (output, input, _) := copy
        let baseCopy := indexed name "baseCopy" index
        let result := indexed name (label ++ "Copy") index
        let bound := indexed name (label ++ "CopyBound") index
        let shape := indexed name (label ++ "CopyShape") index
        elabCommand (← `(theorem $bound : $(quote index) < ($oldCopies).length := by decide +kernel))
        elabCommand (← `(theorem $shape : ($oldCopies).get ⟨$(quote index), $bound⟩ =
          add (atom (($oldBank).placement $(← address output)))
            (negate (atom (($oldBank).placement $(← address input)))) := by rfl))
        elabCommand (← `(theorem $result (baseValue : GKRAddress → Source.BaseField)
          (arithmetic : ∀ gate ∈ ($artifact).gates, gate.expressionResidual (baseValue ∘ ($baseBank).address) = 0) :
          evaluate (baseValue ∘ ($oldBank).address) (($oldCopies).get ⟨$(quote index), $bound⟩) = 0 := by
          rw [$shape:ident]
          simp only [evaluate_add, evaluate_atom, evaluate_negate]
          change baseValue $(← address output) + -baseValue $(← address input) = 0
          exact add_neg_eq_zero.mpr ($baseCopy baseValue arithmetic)))
        proofs := proofs.push (← `($result baseValue arithmetic))
      let allCopies := field name (label ++ "Copies")
      elabCommand (← `(theorem $allCopies (baseValue : GKRAddress → Source.BaseField)
        (arithmetic : ∀ gate ∈ ($artifact).gates, gate.expressionResidual (baseValue ∘ ($baseBank).address) = 0) :
        Satisfies $oldCopies (baseValue ∘ ($oldBank).address) := PredicateChecks.all $(← predicates proofs)))
      let defined := field name (label ++ "Defined")
      elabCommand (← `(theorem $defined {R : Type} [CommRing R]
        (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
        (baseValue : GKRAddress → Source.BaseField)
        (arithmetic : ∀ gate ∈ ($artifact).gates, gate.expressionResidual (baseValue ∘ ($baseBank).address) = 0) :
        ∀ definition ∈ $oldDefinitions,
          definition.Holds hom challenges (($assignment hom challenges gamma baseValue).value $typingName hom) := by
        have result := $canonicalAffines hom challenges gamma baseValue arithmetic
        have sameDefinitions := $definitionsAgree
        have sameValues := $assignmentValue hom challenges gamma baseValue
        rw [sameDefinitions, ← sameValues] at result
        exact result))

end Airbender.Compiler.FunctionalLinksImport
