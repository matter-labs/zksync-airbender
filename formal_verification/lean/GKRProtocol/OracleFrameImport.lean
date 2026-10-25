import GKRProtocol.OracleFrame
import GKRProtocol.FullArithmeticImport
import GKRProtocol.Typing

namespace Airbender.Compiler.OracleFrameImport
open Lean Elab Command
set_option warningAsError true

private def fieldName (owner : Ident) (stem : String) : Ident := mkIdent (owner.getId ++ Name.mkSimple stem)

private def emitChecked (command : Syntax) : CommandElabM Unit := do
  elabCommand command
  if (← get).messages.hasErrors then throwAbortCommand

syntax (name := importOracleFrame) "import_lookup_oracle_frame " ident " from " str
  " base_model " ident " typing " ident : command

elab_rules : command
  | `(import_lookup_oracle_frame $name:ident from $path:str base_model $baseName:ident
      typing $typingName:ident) => do
    let pair ← match Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := Import.Pair)) with
      | .ok pair => pure pair | .error error => throwError "{error}"
    unless pair.format_version == 1 do throwError "unsupported lookup oracle frame version"
    let mut terms : Array (TSyntax `term) := #[]
    for (kind, _) in pair.circuit.global_output_map.entries do
      match kind with
      | .GenericLookup =>
          for index in [:pair.circuit.generic_lookup_tables_width] do
            terms := terms.push (← `(SourceSetupColumn.generic $(quote index)))
      | .Lookup16Bits => terms := terms.push (← `(SourceSetupColumn.range16))
      | .LookupTimestamps => terms := terms.push (← `(SourceSetupColumn.timestamp))
      | _ => pure ()
    let bank := fieldName baseName "bank"
    let columns := fieldName name "columns"
    let external := fieldName name "externalChecked"
    let roles := fieldName name "baseRoles"
    emitChecked (← `(def $columns : List SourceSetupColumn := [$terms,*]))
    emitChecked (← `(theorem $external : ($columns).all (fun column =>
      decide (addressEqual (($bank).address (($bank).placement column.address)) column.address = false)) = true := by decide +kernel))
    emitChecked (← `(theorem $roles : ($columns).all (fun column =>
      ($typingName).compatible (column.address, .base)) = true := by decide +kernel))
    let cells := fieldName name "materialized_cells"
    emitChecked (← `(theorem $cells {width : Nat} (model : MaterializedLookupSetup width)
      (row : Fin model.imported.data.length) (fallback : GKRAddress → Source.BaseField)
      (extended : Fin _ → Source.BaseField) :
      ∀ column ∈ $columns,
        ($bank).materialize extended (model.baseOracle row fallback) column.address = model.value row column := by
      intro column member
      have external := List.all_eq_true.mp $external column member
      have checked : addressEqual (($bank).address (($bank).placement column.address)) column.address = false := by
        exact of_decide_eq_true external
      rw [WireBank.materialize_external $bank extended (model.baseOracle row fallback) column.address checked]
      exact model.baseOracle_at row fallback column))

end Airbender.Compiler.OracleFrameImport
