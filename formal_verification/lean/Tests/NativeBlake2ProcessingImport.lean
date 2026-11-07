import Airbender.Review.Circuits.Blake2Worker.ProcessingArtifact
import Airbender.Review.Circuits.Blake2Worker.NativeArtifact

open Airbender Lean
set_option autoImplicit false

private def check (ok : Bool) (label : String) : IO Unit :=
  if ok then IO.println s!"PASS {label}" else throw (IO.userError label)

private def replaceField (json : Json) (key : String) (value : Json) : Except String Json := do
  let object ← json.getObj?
  return Json.mkObj (object.toArray.toList.filter (fun entry => entry.1 != key) ++ [(key,value)])

private def changedPointer (source : Json) (start : Nat) : Except String String := do
  let memory ← source.getObjVal? "memory_layout"
  let accesses ← (← memory.getObjVal? "register_and_indirect_accesses").getArr?
  let some first := accesses[0]? | throw "missing access"
  let access ← first.getObjVal? "register_access"
  let body ← access.getObjVal? "ReadAccess"
  let altered ← replaceField body "read_value" (Json.mkObj [("start",toJson start),("num_elements",toJson (1 : Nat))])
  let first ← replaceField first "register_access" (Json.mkObj [("ReadAccess",altered)])
  let memory ← replaceField memory "register_and_indirect_accesses" (toJson (accesses.set! 0 first))
  return (← replaceField source "memory_layout" memory).compress

private def rejected {α : Type} : Except String α → Bool
  | .error _ => true | .ok _ => false

def main : IO UInt32 := do
  try
    let source ← IO.FS.readFile "artifacts/circuits/blake2-native-layout.json"
    check (source == Blake2Worker.ProcessingArtifact.processingSourceBytes && source == Blake2Worker.Native.constraintsSourceBytes) "same-read native ABI/body source bytes"
    let actual ← IO.ofExcept (Import.Blake2Worker.parse source)
    let masked := Import.Blake2Processing.maskedColumns actual.abi
    check (masked == Blake2Worker.ProcessingArtifact.processingMaskedColumns && masked.size == 225) "complete native descriptor mask walk225"
    check (decide masked.toList.Nodup) "allmasked physical fields occur once"
    let memory ← IO.ofExcept ((Array.range actual.abi.memoryWidth).mapM fun i => actual.logical (.MemorySubtree i))
    check (memory == Blake2Worker.ProcessingArtifact.processingMemoryColumns && memory.size == 226) "complete actual226memory physical-logical map"
    let json ← IO.ofExcept (Json.parse source)
    let changed ← IO.ofExcept (changedPointer json 8)
    let changed ← IO.ofExcept (Import.Blake2Worker.parse changed)
    check (Import.Blake2Processing.maskedColumns changed.abi != masked) "changedcanonical ABI read retained as data without coverage certificate"
    let invalid ← IO.ofExcept (changedPointer json 226)
    check (rejected (Import.Blake2Worker.parse invalid)) "reject descriptor outside actualmemory mapping"
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"FAIL {error}"
    return (1 : UInt32)
