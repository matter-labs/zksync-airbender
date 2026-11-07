import Airbender.Review.Circuits.ReducedMachine.InitializationRangeArtifact
import Airbender.Review.Circuits.ReducedMachine.NativeArtifact

open Airbender Lean
set_option autoImplicit false
private def check (ok : Bool) (label : String) : IO Unit :=
  if ok then IO.println s!"PASS {label}" else throw (IO.userError label)
private def replaceField (json : Json) (key : String) (value : Json) : Except String Json := do
  let object ← json.getObj?
  return Json.mkObj (object.toArray.toList.filter (fun entry => entry.1 != key) ++ [(key,value)])
private def changed (json : Json) (partName key : String) (value : Json) : Except String String := do
  let part ← json.getObjVal? partName
  return (← replaceField json partName (← replaceField part key value)).compress
private def rejected {α : Type} : Except String α → Bool
  | .error _ => true | .ok _ => false

def main : IO UInt32 := do
  try
    let source ← IO.FS.readFile "artifacts/circuits/reduced-native-layout.json"
    check (source == ReducedMachine.Native.initializationRangeLayoutSourceBytes && source == ReducedMachine.Native.importedConstraintsSourceBytes) "same-read complete native source"
    let actual ← IO.ofExcept (Import.ReducedInitializationRange.parse source)
    check (actual == ReducedMachine.Native.initializationRangeLayout && actual.product.index == 4 && actual.accumulator.start == 28) "separate BASE4/QUARTIC28 on actual full source"
    let json ← IO.ofExcept (Json.parse source)
    let stage ← IO.ofExcept (json.getObjVal? "stage_2_layout")
    let pair ← IO.ofExcept (stage.getObjVal? "lazy_init_address_range_check_16")
    for (key,start,count) in #[("base_field_oracles",5,1),("base_field_oracles",4,0),("ext_4_field_oracles",24,1),("ext_4_field_oracles",28,0)] do
      let part ← IO.ofExcept (replaceField pair key (Json.mkObj [("start",toJson start),("num_elements",toJson count)]))
      let altered ← IO.ofExcept (changed json "stage_2_layout" "lazy_init_address_range_check_16" part)
      check (rejected (Import.ReducedInitializationRange.parse altered)) s!"reject changed {key} {start}/{count}"
    for part in #[Json.null,(← IO.ofExcept (replaceField pair "num_pairs" (toJson (2 : Nat)))),(← IO.ofExcept (replaceField pair "extra" Json.null))] do
      let altered ← IO.ofExcept (changed json "stage_2_layout" "lazy_init_address_range_check_16" part)
      check (rejected (Import.ReducedInitializationRange.parse altered)) "reject absent/extra/changed pair"
    let altered ← IO.ofExcept (changed json "stage_2_layout" "intermediate_polys_for_memory_argument" Json.null)
    check (rejected (Import.ReducedInitializationRange.parse altered)) "retain complete unrelated main-auxiliary validation"
    let historical ← IO.FS.readFile "../../cs/reduced_machine_preprocessed_layout.json"
    check (rejected (Import.ReducedInitializationRange.parse historical)) "reject historical119eqartifact"
    let equations ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "degree_1_constraints")).getArr?)
    let first ← IO.ofExcept (replaceField equations[0]! "constant_term" (toJson (1 : Nat)))
    let altered ← IO.ofExcept (replaceField json "degree_1_constraints" (toJson (equations.set! 0 first)))
    check ((← IO.ofExcept (Import.ReducedInitializationRange.parse altered.compress)) == actual) "canonical changed body retained as DATA without semantic transfer"
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"FAIL {error}"
    return (1 : UInt32)
