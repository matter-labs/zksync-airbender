import Airbender.Proofs.GKRProtocol.MaterializedCounters
import Airbender.Import.GKRProtocol.TableImport

namespace Airbender.Compiler

def SourceTablePlan.fixedRegions (plan : SourceTablePlan) : List (Nat × Nat × Nat) :=
  plan.sizes.zipIdx.filterMap (fun (size, index) => if size = 0 then none else
    some (index, (plan.layout.offsets[index]?).getD 0, size))

namespace MaterializedImport
open Lean Elab Command
set_option warningAsError true

private def fieldName (owner : Ident) (stem : String) : Ident := mkIdent (owner.getId ++ Name.mkSimple stem)

private def emitChecked (command : Syntax) : CommandElabM Unit := do
  elabCommand command
  if (← get).messages.hasErrors then throwAbortCommand

syntax (name := importMaterializedSetup) "import_materialized_setup " ident " from " str
  " uncached " str " setup_model " ident " table_model " ident " width " num : command

elab_rules : command
  | `(import_materialized_setup $name:ident from $path:str uncached $uncachedPath:str
      setup_model $dataOwner:ident table_model $tableName:ident width $widthNumber:num) => do
    let json ← match Json.parse (← IO.FS.readFile path.getString) with
      | .ok json => pure json | .error error => throwError "{error}"
    let uncachedJson ← match Json.parse (← IO.FS.readFile uncachedPath.getString) with
      | .ok json => pure json | .error error => throwError "{error}"
    let pair ← match fromJson? (α := Import.Pair) json with
      | .ok pair => pure pair | .error error => throwError "{error}"
    let uncachedPair ← match fromJson? (α := Import.Pair) uncachedJson with
      | .ok pair => pure pair | .error error => throwError "{error}"
    let .ok original := json.getObjVal? "source" | throwError "missing original compiler input"
    let .ok uncachedOriginal := uncachedJson.getObjVal? "source" | throwError "missing original compiler input"
    unless pair.format_version == 1 && uncachedPair.format_version == 1 && !uncachedPair.cached &&
        pair.family == uncachedPair.family && original == uncachedOriginal do
      throwError "materialized setup is detached from the shared original compiler input"
    let .ok uncachedCircuit := uncachedJson.getObjVal? "circuit" | throwError "missing uncached native circuit"
    let dataName := fieldName dataOwner "setup"
    let rangeDomain := fieldName dataOwner "range16_length"
    let timestampDomain := fieldName dataOwner "timestamp_length"
    let circuitBytes := fieldName dataOwner "setupCircuitSource"
    let nativeLayout := fieldName tableName "nativeLayout"
    let sourcePlan := fieldName tableName "sourcePlan"
    let model := fieldName name "model"
    emitChecked (← `(def $model : MaterializedLookupSetup $(quote widthNumber.getNat) :=
      ⟨$dataName, $rangeDomain, $timestampDomain⟩))
    let circuitChecked := fieldName name "circuitChecked"
    emitChecked (← `(theorem $circuitChecked : $circuitBytes = $(quote uncachedCircuit.compress) := by rfl))
    let traceChecked := fieldName name "traceChecked"
    let widthChecked := fieldName name "widthChecked"
    let regionsChecked := fieldName name "regionsChecked"
    let positive := fieldName name "positive"
    emitChecked (← `(theorem $traceChecked : ($nativeLayout).traceLength = ($model).imported.data.length := by rfl))
    emitChecked (← `(theorem $widthChecked : ($nativeLayout).width = $(quote widthNumber.getNat) := by rfl))
    emitChecked (← `(theorem $regionsChecked : ($model).imported.regions.toList.map
      (fun region => (region.id, region.offset, region.length)) = ($sourcePlan).fixedRegions := by decide +kernel))
    emitChecked (← `(theorem $positive : 0 < ($model).imported.data.length := by decide +kernel))
    for (kind, _) in pair.circuit.global_output_map.entries do
      let some stem := (match kind with
        | .GenericLookup => some "generic" | .Lookup16Bits => some "range16"
        | .LookupTimestamps => some "timestamp" | _ => none) | continue
      let columns := fieldName tableName s!"{stem}SetupColumns"
      let complete := fieldName name s!"{stem}_count_witness"
      emitChecked (← `(theorem $complete {R Q : Type} [CommRing R]
        (entries : List Q) (queryFields : Q → List Source.BaseField) (weight : Q → Source.BaseField)
        (valid : ∀ entry ∈ entries, weight entry ≠ 0 → ($model).Contains $columns (queryFields entry))
        (hom : Source.BaseField →+* R) (alpha gamma : R) :
        ∃ counts : Fin ($model).imported.data.length → Source.BaseField,
          ((entries.map (fun entry => RationalPair.leaf (hom (weight entry))
            (NativeLookupEncoding.linearize hom alpha (queryFields entry) 0 0 + gamma))) ++
            ((List.finRange ($model).imported.data.length).map
              (fun row => (($model).row $columns row (counts row)).value hom alpha gamma))).sum.numerator = 0 :=
        MaterializedLookupSetup.counter_witness $model $columns $positive entries queryFields weight valid hom alpha gamma))

end MaterializedImport
end Airbender.Compiler
