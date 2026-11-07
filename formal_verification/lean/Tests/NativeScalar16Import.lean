import Airbender.Review.Circuits.ReducedMachine.Scalar16Artifact
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
    check (source == ReducedMachine.Native.scalar16LayoutSourceBytes && source == ReducedMachine.Native.importedConstraintsSourceBytes) "same-read complete native source"
    let actual ← IO.ofExcept (Import.ReducedScalar16.parse source)
    check (actual == ReducedMachine.Native.scalar16Layout && actual.multiplicity.index == 7 && actual.setup.index == 0 && actual.tableAccumulator.start == 76) "distinct physical witness7/setup0/quartic76"
    check (actual.bodyColumns.toArray == #[61,62,69,70,90,91,122,123] && actual.initializationAccumulator.start == 28) "all original pairs and extra initialization pair"
    let json ← IO.ofExcept (Json.parse source)
    for (partName,key,start,count) in #[
        ("witness_layout","multiplicities_columns_for_range_check_16",8,1),
        ("witness_layout","multiplicities_columns_for_range_check_16",7,0),
        ("witness_layout","range_check_16_columns",12,8),
        ("setup_layout","range_check_16_setup_column",1,1),
        ("setup_layout","range_check_16_setup_column",0,0),
        ("stage_2_layout","intermediate_poly_for_range_check_16_multiplicity",80,1),
        ("stage_2_layout","intermediate_poly_for_range_check_16_multiplicity",76,0)] do
      let altered ← IO.ofExcept (changed json partName key (Json.mkObj [("start",toJson start),("num_elements",toJson count)]))
      check (rejected (Import.ReducedScalar16.parse altered)) s!"reject changed {partName}/{key} {start}/{count}"
    let queries ← IO.ofExcept ((← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "witness_layout")).getObjVal? "range_check_16_lookup_expressions")).getArr?)
    let altered ← IO.ofExcept (changed json "witness_layout" "range_check_16_lookup_expressions" (toJson (queries.set! 0 queries[1]!)))
    check (rejected (Import.ReducedScalar16.parse altered)) "reject changed physical query order"
    let altered ← IO.ofExcept (changed json "stage_2_layout" "lazy_init_address_range_check_16" Json.null)
    check (rejected (Import.ReducedScalar16.parse altered)) "retain complete extra initialization pair validation"
    let altered ← IO.ofExcept (changed json "witness_layout" "multiplicities_columns_for_range_check_16" (Json.mkObj [("start",toJson (7 : Nat)),("num_elements",toJson (1 : Nat)),("extra",Json.null)]))
    check (rejected (Import.ReducedScalar16.parse altered)) "reject unknown multiplicity group field"
    let historical ← IO.FS.readFile "../../cs/reduced_machine_preprocessed_layout.json"
    check (rejected (Import.ReducedScalar16.parse historical)) "reject historical119eqartifact"
    let equations ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "degree_1_constraints")).getArr?)
    let first ← IO.ofExcept (replaceField equations[0]! "constant_term" (toJson (1 : Nat)))
    let altered ← IO.ofExcept (replaceField json "degree_1_constraints" (toJson (equations.set! 0 first)))
    check ((← IO.ofExcept (Import.ReducedScalar16.parse altered.compress)) == actual) "changed body retained as DATA without semantic transfer"
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"FAIL {error}"
    return (1 : UInt32)
