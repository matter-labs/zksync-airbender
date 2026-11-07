import Airbender.Import.ReducedDecoderAuxiliary
import Airbender.Review.Circuits.ReducedMachine.DecoderTableColumns

namespace Airbender.Import.ReducedDecoderTable
open Lean Elab Command
private def group (json : Json) (start count : Nat) : Except String Unit := do
  let entries := (← json.getObj?).toArray
  unless entries.size == 2 && entries.all (fun (key,_) => key == "start" || key == "num_elements") do
    throw "unexpected decoder-table group fields"
  let actualStart : Nat ← fromJson? (← json.getObjVal? "start")
  let actualCount : Nat ← fromJson? (← json.getObjVal? "num_elements")
  unless actualStart == start && actualCount == count do throw "unsupported decoder-table group geometry"

/-- Complete unchanged body/stage2/access validation on the SAME source. The
    multiplicity is an unmapped physical witness column, not body variable9. -/
def parse (source : String) : Except String Airbender.ReducedMachine.Native.DecoderTableLayout := do
  let access ← ReducedDecoderAuxiliary.parse source
  let body ← Airbender.parseCircuit source
  let json ← Json.parse source
  let witness ← json.getObjVal? "witness_layout"
  group (← witness.getObjVal? "multiplicities_columns_for_decoder_in_executor_families") 9 1
  unless body.variable_mapping.entries.all (fun entry => entry.2 != .WitnessSubtree 9) do
    throw "decoder multiplicity unexpectedly mapped to a body variable"
  let setup ← json.getObjVal? "setup_layout"
  group (← setup.getObjVal? "preprocessed_decoder_setup_columns") 6 1
  let stage ← json.getObjVal? "stage_2_layout"
  group (← stage.getObjVal? "intermediate_polys_for_decoder_multiplicities") 88 1
  return ⟨access.traceLength,body.witness_layout.total_width,body.setup_layout.total_width,
    body.executor_family_decoder_table_size,access.extensionOffset,access.width,⟨9⟩,6,access.access,⟨88⟩⟩

elab "import_native_reduced_decoder_table " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let layout ← match parse source with
    | .ok layout => pure layout | .error e => throwError "Reduced decoder table import failed: {e}"
  let bytes := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $name : Airbender.ReducedMachine.Native.DecoderTableLayout :=
    ⟨$(quote layout.traceLength),$(quote layout.witnessWidth),$(quote layout.setupWidth),
      $(quote layout.decoderCapacity),$(quote layout.extensionOffset),$(quote layout.width),
      ⟨$(quote layout.multiplicity.index)⟩,$(quote layout.setupStart),⟨$(quote layout.access.start)⟩,
      ⟨$(quote layout.tableMultiplicity.start)⟩⟩))
  elabCommand (← `(def $bytes : String := $(quote source)))
end Airbender.Import.ReducedDecoderTable
