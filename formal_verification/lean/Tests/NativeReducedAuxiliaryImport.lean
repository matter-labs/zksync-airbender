import Airbender.Review.Circuits.ReducedMachine.AuxiliaryArtifact
import Airbender.Review.Circuits.ReducedMachine.NativeArtifact

open Airbender Lean
set_option autoImplicit false

private def check (ok : Bool) (label : String) : IO Unit :=
  if ok then IO.println s!"PASS {label}" else throw (IO.userError label)

private def replaceField (json : Json) (key : String) (value : Json) : Except String Json := do
  let object ← json.getObj?
  return Json.mkObj (object.toArray.toList.filter (fun entry => entry.1 != key) ++ [(key,value)])

private def changedStage (json : Json) (key : String) (value : Json) : Except String String := do
  let stage ← json.getObjVal? "stage_2_layout"
  let stage ← replaceField stage key value
  return (← replaceField json "stage_2_layout" stage).compress

private def rejected {α : Type} : Except String α → Bool
  | .error _ => true | .ok _ => false

def main : IO UInt32 := do
  try
    let source ← IO.FS.readFile "artifacts/circuits/reduced-native-layout.json"
    check (source == ReducedMachine.Native.callerAuxiliaryLayoutSourceBytes && source == ReducedMachine.Native.importedConstraintsSourceBytes) "same-read complete main body and auxiliary source"
    let actual ← IO.ofExcept (Import.ReducedAuxiliary.parse source)
    check (actual == ReducedMachine.Native.callerAuxiliaryLayout) "complete selected native main geometry"
    check (actual.request.start == 92 && actual.memory.map (·.start) == #[96,100,104] && actual.grandProduct.start == 120) "separate quartic request and three memory slots"
    check (actual.state.start == 108 && actual.masking.start == 112 && actual.initialization.start == 116) "retain state masking initialization auxiliary families"
    let historical ← IO.FS.readFile "../../cs/reduced_machine_preprocessed_layout.json"
    check (rejected (Import.ReducedAuxiliary.parse historical)) "reject historical119equation artifact without transfer"
    let json ← IO.ofExcept (Json.parse source)
    for (key,start,count) in #[
        ("delegation_processing_aux_poly",93,1),
        ("intermediate_polys_for_memory_argument",96,2),
        ("intermediate_polys_for_memory_argument",92,3),
        ("intermediate_polys_for_state_permutation",108,0),
        ("intermediate_polys_for_permutation_masking",108,1),
        ("intermediate_polys_for_memory_init_teardown",116,0),
        ("intermediate_poly_for_grand_product",116,1)] do
      let altered ← IO.ofExcept (changedStage json key (Json.mkObj [("start",toJson start),("num_elements",toJson count)]))
      check (rejected (Import.ReducedAuxiliary.parse altered)) s!"reject changed {key} {start}/{count}"
    for (key,value) in #[("total_width",125),("ext4_polys_offset",13)] do
      let altered ← IO.ofExcept (changedStage json key (toJson value))
      check (rejected (Import.ReducedAuxiliary.parse altered)) s!"reject changed {key}"
    let extra ← IO.ofExcept (changedStage json "unexpected_auxiliary" Json.null)
    check (rejected (Import.ReducedAuxiliary.parse extra)) "reject unknown stage2 key"
    let remainder ← IO.ofExcept (changedStage json "remainder_for_range_check_16" (toJson (0 : Nat)))
    check (rejected (Import.ReducedAuxiliary.parse remainder)) "reject unsupported remainder"
    let missing ← IO.ofExcept (changedStage json "lazy_init_address_range_check_16" Json.null)
    check (rejected (Import.ReducedAuxiliary.parse missing)) "reject missing actual initialization range auxiliary"
    let equations ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "degree_1_constraints")).getArr?)
    let first ← IO.ofExcept (replaceField equations[0]! "constant_term" (toJson (1 : Nat)))
    let changed ← IO.ofExcept (replaceField json "degree_1_constraints" (toJson (equations.set! 0 first)))
    check ((← IO.ofExcept (Import.ReducedAuxiliary.parse changed.compress)) == actual) "canonical changed body retained as data without semantic transfer"
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"FAIL {error}"
    return (1 : UInt32)
