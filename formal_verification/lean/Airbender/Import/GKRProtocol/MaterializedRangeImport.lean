import Airbender.Proofs.GKRProtocol.MaterializedRanges

namespace Airbender.Compiler.MaterializedRangeImport
open Lean Elab Command
set_option warningAsError true

private def fieldName (owner : Ident) (stem : String) : Ident := mkIdent (owner.getId ++ Name.mkSimple stem)
private def emitChecked (command : Syntax) : CommandElabM Unit := do
  elabCommand command
  if (← get).messages.hasErrors then throwAbortCommand

syntax (name := importMaterializedRanges) "import_materialized_ranges " ident " model " ident : command
elab_rules : command
  | `(import_materialized_ranges $name:ident model $modelName:ident) => do
    for (stem, limit) in [("range16", 65536), ("timestamp", 524288)] do
      let data ← if stem == "range16" then `(($modelName).imported.range16)
        else `(($modelName).imported.timestampRange)
      let tail := fieldName name s!"{stem}Tail"
      let initialBlocks := fieldName name s!"{stem}Prefix"
      let offset := fieldName name s!"{stem}Offset"
      let domain := fieldName name s!"{stem}Domain"
      let contains := fieldName name s!"{stem}_contains"
      let result ← if stem == "range16" then `(MaterializedLookupSetup.range_contains)
        else `(MaterializedLookupSetup.timestamp_contains)
      let columns ← if stem == "range16" then `([SourceSetupColumn.range16]) else `([SourceSetupColumn.timestamp])
      emitChecked (← `(def $tail : List Setup.Block := (($data).columns[0]).blocks.toList.tail))
      emitChecked (← `(theorem $initialBlocks : (($data).columns[0]).blocks.toList =
        Setup.Block.affine $(quote limit) 0 1 :: $tail := by decide +kernel))
      emitChecked (← `(theorem $offset : ($data).offset = 0 := by rfl))
      emitChecked (← `(theorem $domain : $(quote limit) ≤ ($modelName).imported.data.length := by decide +kernel))
      emitChecked (← `(theorem $contains (value : Source.BaseField) (bounded : value.val < $(quote limit)) :
        ($modelName).Contains $columns [value] := $result $modelName $offset $tail $initialBlocks $domain value bounded))

end Airbender.Compiler.MaterializedRangeImport
