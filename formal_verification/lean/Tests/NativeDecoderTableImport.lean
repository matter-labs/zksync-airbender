import Airbender.Review.Circuits.ReducedMachine.DecoderTableArtifact
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
    check (source == ReducedMachine.Native.decoderTableLayoutSourceBytes && source == ReducedMachine.Native.importedConstraintsSourceBytes) "same-read complete native source"
    let actual ← IO.ofExcept (Import.ReducedDecoderTable.parse source)
    check (actual == ReducedMachine.Native.decoderTableLayout && actual.multiplicity.index == 9 && actual.setupStart == 6 && actual.tableMultiplicity.start == 88) "distinct physical witness9/setup6/quartic88"
    let json ← IO.ofExcept (Json.parse source)
    for (partName,key,start,count) in #[
        ("witness_layout","multiplicities_columns_for_decoder_in_executor_families",7,1),
        ("witness_layout","multiplicities_columns_for_decoder_in_executor_families",9,0),
        ("setup_layout","preprocessed_decoder_setup_columns",7,1),
        ("setup_layout","preprocessed_decoder_setup_columns",6,0),
        ("stage_2_layout","intermediate_polys_for_decoder_multiplicities",89,1),
        ("stage_2_layout","intermediate_polys_for_decoder_multiplicities",88,0)] do
      let altered ← IO.ofExcept (changed json partName key (Json.mkObj [("start",toJson start),("num_elements",toJson count)]))
      check (rejected (Import.ReducedDecoderTable.parse altered)) s!"reject changed {partName}/{key} {start}/{count}"
    let missing ← IO.ofExcept (changed json "witness_layout" "multiplicities_columns_for_decoder_in_executor_families" Json.null)
    check (rejected (Import.ReducedDecoderTable.parse missing)) "reject missing physical multiplicity group"
    let extra ← IO.ofExcept (changed json "witness_layout" "multiplicities_columns_for_decoder_in_executor_families" (Json.mkObj [("start",toJson (9 : Nat)),("num_elements",toJson (1 : Nat)),("extra",Json.null)]))
    check (rejected (Import.ReducedDecoderTable.parse extra)) "reject unknown physical multiplicity field"
    let historical ← IO.FS.readFile "../../cs/reduced_machine_preprocessed_layout.json"
    check (rejected (Import.ReducedDecoderTable.parse historical)) "reject historical119eqartifact"
    let equations ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "degree_1_constraints")).getArr?)
    let first ← IO.ofExcept (replaceField equations[0]! "constant_term" (toJson (1 : Nat)))
    let altered ← IO.ofExcept (replaceField json "degree_1_constraints" (toJson (equations.set! 0 first)))
    check ((← IO.ofExcept (Import.ReducedDecoderTable.parse altered.compress)) == actual) "canonical changed body retained as DATA without semantic transfer"
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"FAIL {error}"
    return (1 : UInt32)
