import GKRProtocol.CounterFrame
import GKRProtocol.TableImport
import GKRProtocol.FullArithmeticImport

namespace Airbender.Compiler.CounterFrameImport
open Lean Elab Command
set_option warningAsError true

private def fieldName (owner : Ident) (stem : String) : Ident := mkIdent (owner.getId ++ Name.mkSimple stem)

private def emitChecked (command : Syntax) : CommandElabM Unit := do
  elabCommand command
  if (← get).messages.hasErrors then throwAbortCommand

syntax (name := importCounterFrame) "import_counter_frame " ident " from " str
  " base_model " ident " table_model " ident " helper_model " ident " inputs " num : command

elab_rules : command
  | `(import_counter_frame $name:ident from $path:str base_model $baseName:ident
      table_model $tableName:ident helper_model $helperName:ident inputs $arityNumber:num) => do
    let pair ← match Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := Import.Pair)) with
      | .ok pair => pure pair | .error error => throwError "{error}"
    unless pair.format_version == 1 do throwError "unsupported compiler counter frame version"
    let columns := fieldName tableName "multiplicityColumns"
    let artifact := fieldName baseName "artifact"
    let bank := fieldName baseName "inputBank"
    let placement := fieldName baseName "helperPlacement"
    let fields := fieldName helperName "fields"
    let actualColumns : Array (TSyntax `term) := pair.circuit.global_output_map.entries.filterMap fun (kind, _) =>
      match kind with
      | .GenericLookup => some (quote pair.circuit.witness_layout.multiplicities_columns_for_generic_lookup.start)
      | .Lookup16Bits => some (quote pair.circuit.witness_layout.multiplicities_columns_for_range_check_16.start)
      | .LookupTimestamps => some (quote pair.circuit.witness_layout.multiplicities_columns_for_timestamp_range_check.start)
      | _ => none
    let columnsChecked := fieldName name "columnsChecked"
    emitChecked (← `(theorem $columnsChecked : $columns = [$actualColumns,*] := by decide +kernel))
    let slots := fieldName name "slots"
    emitChecked (← `(def $slots (index : Fin ($columns).length) : Fin $(quote arityNumber.getNat) :=
      ($bank).placement (.BaseLayerWitness (($columns).get index))))
    let unique := fieldName name "slotsUnique"
    let roundTrip := fieldName name "slotsRoundTrip"
    let fresh := fieldName name "slotsFresh"
    emitChecked (← `(theorem $unique : Function.Injective $slots := by decide +kernel))
    emitChecked (← `(theorem $roundTrip : ∀ index, ($bank).address ($slots index) =
      GKRAddress.BaseLayerWitness (($columns).get index) := by decide +kernel))
    emitChecked (← `(theorem $fresh : ∀ index, $(quote pair.source.num_variables) ≤ ($slots index).val := by decide +kernel))
    let sourceChecked := fieldName name "sourceChecked"
    let helpersChecked := fieldName name "helpersChecked"
    emitChecked (← `(theorem $sourceChecked : ($artifact).source.all
      (erasureUntouched (List.ofFn $slots)) = true := by decide +kernel))
    emitChecked (← `(theorem $helpersChecked : ($fields).all (fun field =>
      erasureUntouched (List.ofFn $slots) (field.polynomial $placement)) = true := by decide +kernel))
    let assigned := fieldName name "assigned"
    emitChecked (← `(noncomputable def $assigned (values : Fin $(quote arityNumber.getNat) → Source.BaseField)
      (counts : Fin ($columns).length → Source.BaseField) := Source.assignCounters $slots values counts))
    let sourcePreserved := fieldName name "source_preserved"
    emitChecked (← `(theorem $sourcePreserved (values : Fin $(quote arityNumber.getNat) → Source.BaseField)
      (counts : Fin ($columns).length → Source.BaseField) (holds : Satisfies ($artifact).source values) :
      Satisfies ($artifact).source ($assigned values counts) :=
      Source.assignCounters_satisfies $slots ($artifact).source $sourceChecked values counts holds))
    let helpersPreserved := fieldName name "helpers_preserved"
    emitChecked (← `(theorem $helpersPreserved (values : Fin $(quote arityNumber.getNat) → Source.BaseField)
      (counts : Fin ($columns).length → Source.BaseField) : ∀ field ∈ $fields,
      field.value (($placement).project ($assigned values counts)) = field.value (($placement).project values) := by
      intro field member
      exact Source.HelperField.assignCounters_value field $placement $slots
        (List.all_eq_true.mp $helpersChecked field member) values counts))
    let assignedAt := fieldName name "counts_at"
    emitChecked (← `(theorem $assignedAt (values : Fin $(quote arityNumber.getNat) → Source.BaseField)
      (counts : Fin ($columns).length → Source.BaseField) (index : Fin ($columns).length) :
      $assigned values counts ($slots index) = counts index := Source.assignCounters_at $slots $unique values counts index))
    let frame := fieldName name "assigned_frame"
    emitChecked (← `(theorem $frame (values : Fin $(quote arityNumber.getNat) → Source.BaseField)
      (counts : Fin ($columns).length → Source.BaseField) (index : Fin $(quote arityNumber.getNat))
      (outside : ∀ counter, $slots counter ≠ index) : $assigned values counts index = values index :=
      Source.assignCounters_frame $slots values counts index outside))

end Airbender.Compiler.CounterFrameImport
