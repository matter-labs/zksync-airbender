import GKRProtocol.HistoryErasure
import GKRProtocol.SourceContractImport

namespace Airbender.Compiler.HistoryErasureImport
open Lean Elab Command
set_option warningAsError true

private def fieldName (owner : Ident) (stem : String) : Ident := mkIdent (owner.getId ++ Name.mkSimple stem)

private def coordinate (placement : Ident) : Source.MemoryField → CommandElabM (TSyntax `term)
  | .input (.Variable index) => `(($placement).memory.original $(quote index))
  | .readTimestamp query limb =>
      `(($placement).memory.readTimestamp $(quote query) ⟨$(quote limb.val), by decide⟩)
  | _ => throwError "source history erasure requires direct original/history timestamp cells"

syntax (name := importHistoryErasure) "import_history_erasure " ident " from " str
  " base_model " ident " source_model " ident " inputs " num : command

elab_rules : command
  | `(import_history_erasure $name:ident from $path:str base_model $baseName:ident
      source_model $sourceName:ident inputs $arityNumber:num) => do
    let snapshot ← match Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := Source.Snapshot)) with
      | .ok snapshot => pure snapshot | .error error => throwError "{error}"
    let requests ← match Source.helperRequests snapshot.semantic_inputs with
      | .ok requests => pure requests | .error error => throwError "{error}"
    let placement := fieldName baseName "helperPlacement"
    let protectedPolys := fieldName sourceName "protectedPolynomials"
    let comparisons := fieldName sourceName "comparisons"
    let clock := fieldName sourceName "clock"
    let slots := fieldName name "historyCells"
    let mut coordinates := #[]
    for (previous, _) in requests.comparisons do
      coordinates := coordinates.push (← coordinate placement previous.low)
      coordinates := coordinates.push (← coordinate placement previous.high)
    elabCommand (← `(def $slots : List (Fin $(quote arityNumber.getNat)) := [$coordinates,*]))
    let unique := fieldName name "historyUnique"
    let checked := fieldName name "arithmeticChecked"
    elabCommand (← `(theorem $unique : ($slots).Nodup := by decide +kernel))
    elabCommand (← `(theorem $checked : erasureCheck $slots $protectedPolys = true := by decide +kernel))
    let historyFields := fieldName name "historyFields"
    let meaning := fieldName name "historyMeaning"
    elabCommand (← `(noncomputable def $historyFields : List Source.MemoryField :=
      ($comparisons).flatMap (fun pair => [pair.1.low, pair.1.high])))
    elabCommand (← `(theorem $meaning : ($historyFields).map (Source.MemoryField.polynomial ($placement).memory) =
      ($slots).map (Compiler.atom (F := Source.BaseField)) := by rfl))
    let memory ← match Source.memoryRequests snapshot.semantic_inputs with
      | .ok memory => pure memory | .error error => throwError "{error}"
    let mut protectedVariables := #[memory.execute]
    if let some delegation := snapshot.semantic_inputs.delegation_circuit_state then
      protectedVariables := protectedVariables ++ delegation.invocation_timestamp.values
    for access in snapshot.semantic_inputs.register_and_indirect_accesses do
      if access.indirects_alignment_log2.val != 0 then
        let read := match access.register_access with | .Read value | .Write value _ => value
        protectedVariables := protectedVariables.push read.values[0]!
    let extraFields ← protectedVariables.mapM fun index => `(Source.MemoryField.input (.Variable $(quote index)))
    let currentFields := fieldName name "protectedFields"
    elabCommand (← `(noncomputable def $currentFields : List Source.MemoryField :=
      ($comparisons).flatMap (fun pair => [pair.2.low, pair.2.high]) ++
        (match ($clock) with | none => [] | some (initial, final) => [initial.low, initial.high, final.low, final.high]) ++
        [$extraFields,*]))
    let fieldsChecked := fieldName name "fieldsChecked"
    elabCommand (← `(theorem $fieldsChecked : ($currentFields).all (fun field =>
      equal (substitute (erasurePolynomials $slots) (field.polynomial ($placement).memory))
        (field.polynomial ($placement).memory)) = true := by decide +kernel))
    let preserved := fieldName name "arithmetic_preserved"
    elabCommand (← `(theorem $preserved (values : Fin $(quote arityNumber.getNat) → Source.BaseField)
      (holds : Satisfies $protectedPolys values) :
      Satisfies $protectedPolys (eraseCoordinates $slots values) := erasure_satisfies $slots $protectedPolys $checked values holds))
    let fieldsPreserved := fieldName name "fields_preserved"
    elabCommand (← `(theorem $fieldsPreserved (values : Fin $(quote arityNumber.getNat) → Source.BaseField) :
      ∀ field ∈ $currentFields,
        field.value (($placement).memory.project (eraseCoordinates $slots values)) =
          field.value (($placement).memory.project values) := by
      intro field member
      exact memoryField_erasure field ($placement).memory $slots (List.all_eq_true.mp $fieldsChecked field member) values))
    let fieldsZero := fieldName name "history_fields_zero"
    elabCommand (← `(theorem $fieldsZero (values : Fin $(quote arityNumber.getNat) → Source.BaseField) :
      ∀ field ∈ $historyFields, field.value (($placement).memory.project (eraseCoordinates $slots values)) = 0 := by
      intro field member
      have polynomialMember : field.polynomial ($placement).memory ∈
          ($historyFields).map (Source.MemoryField.polynomial ($placement).memory) :=
        List.mem_map.mpr ⟨field, member, rfl⟩
      rw [$meaning:ident] at polynomialMember
      obtain ⟨index, included, same⟩ := List.mem_map.mp polynomialMember
      rw [← Source.MemoryField.polynomial_value, ← same, evaluate_atom]
      exact eraseCoordinates_at $slots values index included))

end Airbender.Compiler.HistoryErasureImport
