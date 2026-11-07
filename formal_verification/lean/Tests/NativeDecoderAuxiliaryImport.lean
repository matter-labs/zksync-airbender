import Airbender.Review.Circuits.ReducedMachine.DecoderAuxiliaryArtifact
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
  return (← replaceField json "stage_2_layout" (← replaceField stage key value)).compress

private def rejected {α : Type} : Except String α → Bool
  | .error _ => true | .ok _ => false

def main : IO UInt32 := do
  try
    let source ← IO.FS.readFile "artifacts/circuits/reduced-native-layout.json"
    check (source == ReducedMachine.Native.decoderAuxiliaryLayoutSourceBytes && source == ReducedMachine.Native.importedConstraintsSourceBytes) "same-read complete body/decoder source"
    let actual ← IO.ofExcept (Import.ReducedDecoderAuxiliary.parse source)
    check (actual == ReducedMachine.Native.decoderAuxiliaryLayout && actual.access.start == 72) "typed actual decoder quartic72"
    let json ← IO.ofExcept (Json.parse source)
    for (key,start,count) in #[("intermediate_poly_for_decoder_accesses",73,1),
        ("intermediate_poly_for_decoder_accesses",72,0),("intermediate_polys_for_decoder_multiplicities",88,0),
        ("delegation_processing_aux_poly",72,1)] do
      let changed ← IO.ofExcept (changedStage json key (Json.mkObj [("start",toJson start),("num_elements",toJson count)]))
      check (rejected (Import.ReducedDecoderAuxiliary.parse changed)) s!"reject changed {key} {start}/{count}"
    let changed ← IO.ofExcept (changedStage json "total_width" (toJson (125 : Nat)))
    check (rejected (Import.ReducedDecoderAuxiliary.parse changed)) "reject changed width"
    let historical ← IO.FS.readFile "../../cs/reduced_machine_preprocessed_layout.json"
    check (rejected (Import.ReducedDecoderAuxiliary.parse historical)) "reject historical body without acceptance transfer"
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"FAIL {error}"
    return (1 : UInt32)
