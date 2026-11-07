import Airbender.Review.Circuits.Blake2Worker.AuxiliaryArtifact
import Airbender.Review.Circuits.Blake2Worker.NativeArtifact

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
    let source ← IO.FS.readFile "artifacts/circuits/blake2-native-layout.json"
    check (source == Blake2Worker.AuxiliaryArtifact.auxiliaryLayoutSourceBytes &&
      source == Blake2Worker.Native.constraintsSourceBytes) "same-read full auxiliary/body bytes"
    let actual ← IO.ofExcept (Import.Blake2Auxiliary.parse source)
    check (actual == Blake2Worker.AuxiliaryArtifact.auxiliaryLayout) "all selected stage2 geometry"
    check (actual.memory.size == 43 && actual.memory[0]!.start == 1068 && actual.memory[42]!.start == 1236) "all43quartic slots stride4"
    check (actual.processing.start == 1064 && actual.grandProduct.start == 1240 && actual.width == 1244) "processor/grandproduct separate physical slots"
    let json ← IO.ofExcept (Json.parse source)
    for (key,start,count) in #[
        ("delegation_processing_aux_poly",1065,1),
        ("intermediate_polys_for_memory_argument",1068,42),
        ("intermediate_polys_for_memory_argument",1064,43),
        ("intermediate_poly_for_grand_product",1236,1),
        ("intermediate_polys_for_state_permutation",0,1)] do
      let altered ← IO.ofExcept (changedStage json key (Json.mkObj [("start",toJson start),("num_elements",toJson count)]))
      check (rejected (Import.Blake2Auxiliary.parse altered)) s!"reject changed {key} {start}/{count}"
    for (key,value) in #[("total_width",1243),("ext4_polys_offset",45)] do
      let altered ← IO.ofExcept (changedStage json key (toJson value))
      check (rejected (Import.Blake2Auxiliary.parse altered)) s!"reject changed {key}"
    let extra ← IO.ofExcept (changedStage json "unexpected_auxiliary" Json.null)
    check (rejected (Import.Blake2Auxiliary.parse extra)) "reject unknown auxiliary key"
    let bad ← IO.ofExcept (changedStage json "remainder_for_range_check_16" (toJson (0 : Nat)))
    check (rejected (Import.Blake2Auxiliary.parse bad)) "reject active unsupported remainder"
    let equations ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "degree_1_constraints")).getArr?)
    let first ← IO.ofExcept (replaceField equations[0]! "constant_term" (toJson (1 : Nat)))
    let changed ← IO.ofExcept (replaceField json "degree_1_constraints" (toJson (equations.set! 0 first)))
    check ((← IO.ofExcept (Import.Blake2Auxiliary.parse changed.compress)) == actual) "canonical changed body retained as data without proof transfer"
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"FAIL {error}"
    return (1 : UInt32)
