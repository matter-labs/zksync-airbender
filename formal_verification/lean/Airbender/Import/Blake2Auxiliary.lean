import Airbender.Import.Blake2Worker
import Airbender.Review.Circuits.Blake2Worker.AuxiliaryColumns

namespace Airbender.Import.Blake2Auxiliary
open Lean Elab Command

private def exactKeys (json : Json) (keys : Array String) : Except String Unit := do
  let entries := (← json.getObj?).toArray
  unless entries.size == keys.size && entries.all (fun (key, _) => keys.contains key) do
    throw "unexpected or missing Blake2 auxiliary fields"

private def readNat (json : Json) (key : String) : Except String Nat := do
  fromJson? (← json.getObjVal? key)

private def expectGroup (json : Json) (key : String) (start count : Nat) : Except String Unit := do
  let value ← json.getObjVal? key
  exactKeys value #["start","num_elements"]
  unless (← readNat value "start") == start && (← readNat value "num_elements") == count do
    throw "unsupported Blake2 auxiliary group geometry"

/-- Selected native stage2 geometry, independently validated after the unchanged
    complete body/ABI parser. No extension slot is a body logical column. -/
def parse (source : String) : Except String Airbender.Blake2Worker.AuxiliaryLayout := do
  let body ← Airbender.Import.Blake2Worker.parse source
  let stage ← body.raw.getObjVal? "stage_2_layout"
  exactKeys stage #["intermediate_polys_for_range_check_16","remainder_for_range_check_16",
    "lazy_init_address_range_check_16","intermediate_polys_for_timestamp_range_checks",
    "intermediate_polys_for_generic_lookup","intermediate_poly_for_decoder_accesses",
    "intermediate_poly_for_range_check_16_multiplicity","intermediate_poly_for_timestamp_range_check_multiplicity",
    "intermediate_polys_for_generic_multiplicities","intermediate_polys_for_decoder_multiplicities",
    "delegation_processing_aux_poly","intermediate_polys_for_memory_init_teardown",
    "intermediate_polys_for_memory_argument","intermediate_polys_for_state_permutation",
    "intermediate_polys_for_permutation_masking","intermediate_poly_for_grand_product",
    "ext4_polys_offset","total_width"]
  for key in #["remainder_for_range_check_16","lazy_init_address_range_check_16"] do
    unless (← stage.getObjVal? key) == .null do throw "unsupported Blake2 auxiliary remainder"
  for (key,pairs,base,extension) in #[
      ("intermediate_polys_for_range_check_16",1,0,44),
      ("intermediate_polys_for_timestamp_range_checks",43,1,48)] do
    let part ← stage.getObjVal? key
    exactKeys part #["num_pairs","base_field_oracles","ext_4_field_oracles"]
    unless (← readNat part "num_pairs") == pairs do throw "unsupported Blake2 auxiliary pair count"
    expectGroup part "base_field_oracles" base pairs
    expectGroup part "ext_4_field_oracles" extension pairs
  for (key,start,count) in #[
      ("intermediate_polys_for_generic_lookup",220,208),
      ("intermediate_poly_for_decoder_accesses",0,0),
      ("intermediate_poly_for_range_check_16_multiplicity",1052,1),
      ("intermediate_poly_for_timestamp_range_check_multiplicity",1056,1),
      ("intermediate_polys_for_generic_multiplicities",1060,1),
      ("intermediate_polys_for_decoder_multiplicities",0,0),
      ("delegation_processing_aux_poly",1064,1),
      ("intermediate_polys_for_memory_init_teardown",1240,0),
      ("intermediate_polys_for_memory_argument",1068,43),
      ("intermediate_polys_for_state_permutation",0,0),
      ("intermediate_polys_for_permutation_masking",0,0),
      ("intermediate_poly_for_grand_product",1240,1)] do
    expectGroup stage key start count
  let offset ← readNat stage "ext4_polys_offset"
  let width ← readNat stage "total_width"
  unless offset == 44 && width == 1244 do throw "unsupported Blake2 auxiliary row width"
  return ⟨offset,width,⟨1064⟩,(Array.range 43).map (fun i => ⟨1068+4*i⟩),⟨1240⟩⟩

elab "import_native_blake2_auxiliary " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let layout ← match parse source with
    | .ok layout => pure layout | .error e => throwError "Blake2 auxiliary import failed: {e}"
  let memories ← layout.memory.mapM fun c => `(Airbender.Blake2Worker.QuarticColumn.mk $(quote c.start))
  let memory ← `( #[$memories,*] )
  let bytes := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $name : Airbender.Blake2Worker.AuxiliaryLayout :=
    ⟨$(quote layout.extensionOffset),$(quote layout.width),⟨$(quote layout.processing.start)⟩,
      $memory,⟨$(quote layout.grandProduct.start)⟩⟩))
  elabCommand (← `(def $bytes : String := $(quote source)))

end Airbender.Import.Blake2Auxiliary
