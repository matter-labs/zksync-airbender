import Airbender.Import.Parse
import Airbender.Review.Circuits.ReducedMachine.AuxiliaryColumns

namespace Airbender.Import.ReducedAuxiliary
open Lean Elab Command

private def exactKeys (json : Json) (keys : Array String) : Except String Unit := do
  let entries := (← json.getObj?).toArray
  unless entries.size == keys.size && entries.all (fun (key, _) => keys.contains key) do
    throw "unexpected or missing reduced auxiliary fields"

private def readNat (json : Json) (key : String) : Except String Nat := do
  fromJson? (← json.getObjVal? key)

private def expectGroup (json : Json) (key : String) (start count : Nat) : Except String Unit := do
  let value ← json.getObjVal? key
  exactKeys value #["start","num_elements"]
  unless (← readNat value "start") == start && (← readNat value "num_elements") == count do
    throw "unsupported reduced auxiliary group geometry"

/-- Fresh selected main artifact only, after unchanged complete body validation.
    All stage2 fields are checked; no quartic slot becomes a body variable. -/
def parse (source : String) : Except String Airbender.ReducedMachine.Native.CallerAuxiliaryLayout := do
  let body ← Airbender.parseCircuit source
  unless body.hasReducedLookups && body.trace_len == 8388608 && body.total_tables_size == 5771521 &&
    body.executor_family_decoder_table_size == 1048576 && body.witness_layout.total_width == 107 &&
    body.memory_layout.total_width == 39 && body.setup_layout.total_width == 16 &&
    body.degree_2_constraints.size == 112 && body.degree_1_constraints.size == 5 &&
    body.variable_mapping.entries.size == 142 do throw "unsupported fresh native reduced body geometry"
  let stage := body.stage_2_layout.raw
  exactKeys stage #["intermediate_polys_for_range_check_16","remainder_for_range_check_16",
    "lazy_init_address_range_check_16","intermediate_polys_for_timestamp_range_checks",
    "intermediate_polys_for_generic_lookup","intermediate_poly_for_decoder_accesses",
    "intermediate_poly_for_range_check_16_multiplicity","intermediate_poly_for_timestamp_range_check_multiplicity",
    "intermediate_polys_for_generic_multiplicities","intermediate_polys_for_decoder_multiplicities",
    "delegation_processing_aux_poly","intermediate_polys_for_memory_init_teardown",
    "intermediate_polys_for_memory_argument","intermediate_polys_for_state_permutation",
    "intermediate_polys_for_permutation_masking","intermediate_poly_for_grand_product",
    "ext4_polys_offset","total_width"]
  unless (← stage.getObjVal? "remainder_for_range_check_16") == .null do
    throw "unsupported reduced auxiliary remainder"
  for (key,pairs,base,extension) in #[
      ("intermediate_polys_for_range_check_16",4,0,12),
      ("lazy_init_address_range_check_16",1,4,28),
      ("intermediate_polys_for_timestamp_range_checks",4,5,32)] do
    let part ← stage.getObjVal? key
    exactKeys part #["num_pairs","base_field_oracles","ext_4_field_oracles"]
    unless (← readNat part "num_pairs") == pairs do throw "unsupported reduced auxiliary pair count"
    expectGroup part "base_field_oracles" base pairs
    expectGroup part "ext_4_field_oracles" extension pairs
  for (key,start,count) in #[
      ("intermediate_polys_for_generic_lookup",48,6),
      ("intermediate_poly_for_decoder_accesses",72,1),
      ("intermediate_poly_for_range_check_16_multiplicity",76,1),
      ("intermediate_poly_for_timestamp_range_check_multiplicity",80,1),
      ("intermediate_polys_for_generic_multiplicities",84,1),
      ("intermediate_polys_for_decoder_multiplicities",88,1),
      ("delegation_processing_aux_poly",92,1),
      ("intermediate_polys_for_memory_init_teardown",116,1),
      ("intermediate_polys_for_memory_argument",96,3),
      ("intermediate_polys_for_state_permutation",108,1),
      ("intermediate_polys_for_permutation_masking",112,1),
      ("intermediate_poly_for_grand_product",120,1)] do
    expectGroup stage key start count
  let offset ← readNat stage "ext4_polys_offset"
  let width ← readNat stage "total_width"
  unless offset == 12 && width == 124 do throw "unsupported reduced auxiliary row width"
  return ⟨body.trace_len,offset,width,⟨92⟩,(Array.range 3).map (fun i => ⟨96+4*i⟩),⟨108⟩,⟨112⟩,⟨116⟩,⟨120⟩⟩

elab "import_native_reduced_auxiliary " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let layout ← match parse source with
    | .ok layout => pure layout | .error e => throwError "Reduced auxiliary import failed: {e}"
  let memories ← layout.memory.mapM fun c => `(Airbender.Blake2Worker.QuarticColumn.mk $(quote c.start))
  let memory ← `( #[$memories,*] )
  let bytes := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $name : Airbender.ReducedMachine.Native.CallerAuxiliaryLayout :=
    ⟨$(quote layout.traceLength),$(quote layout.extensionOffset),$(quote layout.width),⟨$(quote layout.request.start)⟩,
      $memory,⟨$(quote layout.state.start)⟩,⟨$(quote layout.masking.start)⟩,
      ⟨$(quote layout.initialization.start)⟩,⟨$(quote layout.grandProduct.start)⟩⟩))
  elabCommand (← `(def $bytes : String := $(quote source)))

end Airbender.Import.ReducedAuxiliary
