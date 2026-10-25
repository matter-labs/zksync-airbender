import GKRProtocol.ScalarSetupRefinement

namespace Airbender.Compiler.CleanScalarImport
open Lean Elab Command
set_option warningAsError true

private def fieldName (owner : Ident) (stem : String) : Ident := mkIdent (owner.getId ++ Name.mkSimple stem)
private def emitChecked (command : Syntax) : CommandElabM Unit := do
  elabCommand command
  if (← get).messages.hasErrors then throwAbortCommand

syntax (name := importCleanScalar) "import_clean_scalar_setup " ident " model " ident : command
elab_rules : command
  | `(import_clean_scalar_setup $name:ident model $modelName:ident) => do
    for (stem, limit) in [("range16", 65536), ("timestamp", 524288)] do
      let data ← if stem == "range16" then `(($modelName).imported.range16) else `(($modelName).imported.timestampRange)
      let targetData ← if stem == "range16" then `(Verification.importedRange16) else `(Verification.importedTimestamp19)
      let tableName ← if stem == "range16" then `(Verification.range16Table (p := babyBearModulus))
        else `(Trace.timestampTable (p := babyBearModulus))
      let column ← if stem == "range16" then `(SourceSetupColumn.range16) else `(SourceSetupColumn.timestamp)
      let domainEquality ← if stem == "range16" then `(($modelName).rangeDomain) else `(($modelName).timestampDomain)
      let label := if stem == "range16" then "Airbender.Range16" else "Airbender.Timestamp19"
      let shape := fieldName name s!"{stem}Shape"
      let targetShape := fieldName name s!"{stem}TargetShape"
      let domain := fieldName name s!"{stem}TargetDomain"
      let refined := fieldName name s!"{stem}_clean_refinement"
      emitChecked (← `(theorem $shape : ($data).columns[0].blocks.toList =
        [Setup.Block.affine $(quote limit) 0 1, Setup.Block.affine (($data).length - $(quote limit)) 0 0] := by decide +kernel))
      emitChecked (← `(theorem $targetShape : ($targetData).columns[0].blocks.toList =
        [Setup.Block.affine $(quote limit) 0 1, Setup.Block.affine (($targetData).length - $(quote limit)) 0 0] := by decide +kernel))
      emitChecked (← `(theorem $domain : ($data).length ≤ ($targetData).length := by decide +kernel))
      emitChecked (← `(theorem $refined (value : Source.BaseField)
        (member : ($modelName).Contains [$column] [value]) (provided : Array Source.BaseField) :
        ($tableName).Contains provided value := by
        have scalarMember : ∃ index : Fin ($data).length, value = ((($data).row index)[0] : Source.BaseField) := by
          obtain ⟨row, same⟩ := member
          let index : Fin ($data).length := ⟨row.val, by have sameDomain := $domainEquality; rw [sameDomain]; exact row.isLt⟩
          refine ⟨index, ?_⟩
          change [value] = [((($data).row index)[0] : Source.BaseField)] at same
          exact (List.cons.inj same).1
        exact scalar_table_refinement $data $targetData $(quote limit)
          (($data).length - $(quote limit)) (($targetData).length - $(quote limit))
          rfl rfl $shape $targetShape $domain value scalarMember $(quote label) provided))

end Airbender.Compiler.CleanScalarImport
