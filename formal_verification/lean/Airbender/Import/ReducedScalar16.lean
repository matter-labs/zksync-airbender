import Airbender.Import.ReducedInitializationRange
import Airbender.Review.Circuits.ReducedMachine.Scalar16Columns

namespace Airbender.Import.ReducedScalar16
open Lean Elab Command
private def group (json : Json) (start count : Nat) : Except String Unit := do
  let fields := (← json.getObj?).toArray
  unless fields.size == 2 && fields.all (fun (key,_) => key == "start" || key == "num_elements") do
    throw "unexpected scalar16 group fields"
  let actualStart : Nat ← fromJson? (← json.getObjVal? "start")
  let actualCount : Nat ← fromJson? (← json.getObjVal? "num_elements")
  unless actualStart == start && actualCount == count do throw "unsupported scalar16 group geometry"

/-- Complete unchanged body/all-stage2/init-pair validation on the SAME read.
    Bind every original scalar query to its actual consecutive physical column;
    unmapped witness7 is not body7. Parsing alone gives no range certificate. -/
def parse (source : String) : Except String Airbender.ReducedMachine.Native.Scalar16Layout := do
  let initialization ← ReducedInitializationRange.parse source
  let body ← Airbender.parseCircuit source
  let json ← Json.parse source
  let witness ← json.getObjVal? "witness_layout"
  group (← witness.getObjVal? "multiplicities_columns_for_range_check_16") 7 1
  group (← witness.getObjVal? "range_check_16_columns") 11 8
  unless body.variable_mapping.entries.all (fun entry => entry.2 != .WitnessSubtree 7) do
    throw "scalar16 multiplicity unexpectedly mapped to body variable"
  let mut columns : Array Nat := #[]
  unless body.witness_layout.range_check_16_lookup_expressions.size == 8 do
    throw "unsupported scalar16 query count"
  for (query,i) in body.witness_layout.range_check_16_lookup_expressions.zipIdx do
    unless (match query with
      | .Variable (.WitnessSubtree n) => n == 11+i
      | _ => false) do
      throw "unsupported scalar16 physical query order"
    columns := columns.push (← body.logicalVariable (.WitnessSubtree (11+i)))
  let setup ← json.getObjVal? "setup_layout"
  group (← setup.getObjVal? "range_check_16_setup_column") 0 1
  let stage ← json.getObjVal? "stage_2_layout"
  group (← stage.getObjVal? "intermediate_poly_for_range_check_16_multiplicity") 76 1
  if size : columns.size = 8 then
    return ⟨initialization.traceLength,body.witness_layout.total_width,body.setup_layout.total_width,
      initialization.extensionOffset,initialization.width,⟨columns,size⟩,⟨0⟩,⟨12⟩,
      initialization.product,initialization.accumulator,⟨7⟩,⟨0⟩,⟨76⟩⟩
  else throw "unsupported scalar16 decoded query count"

elab "import_native_reduced_scalar16 " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let layout ← match parse source with
    | .ok layout => pure layout | .error e => throwError "Reduced scalar16 import failed: {e}"
  let columns : Array (TSyntax `term) := layout.bodyColumns.toArray.map (fun c => quote c)
  let array ← `( #[$columns,*] )
  let bytes := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $name : Airbender.ReducedMachine.Native.Scalar16Layout :=
    ⟨$(quote layout.traceLength),$(quote layout.witnessWidth),$(quote layout.setupWidth),
      $(quote layout.extensionOffset),$(quote layout.width),⟨$array,by decide⟩,
      ⟨$(quote layout.bodyProductStart.index)⟩,⟨$(quote layout.bodyAccumulatorStart.start)⟩,
      ⟨$(quote layout.initializationProduct.index)⟩,⟨$(quote layout.initializationAccumulator.start)⟩,
      ⟨$(quote layout.multiplicity.index)⟩,⟨$(quote layout.setup.index)⟩,⟨$(quote layout.tableAccumulator.start)⟩⟩))
  elabCommand (← `(def $bytes : String := $(quote source)))
end Airbender.Import.ReducedScalar16
