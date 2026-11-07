import Airbender.Review.Circuits.Blake2Worker.QueryArtifact
import Airbender.Review.Circuits.Blake2Worker.NativeArtifact

open Airbender Lean
set_option autoImplicit false

private def check (ok : Bool) (label : String) : IO Unit :=
  if ok then IO.println s!"PASS {label}" else throw (IO.userError label)

private def replaceField (json : Json) (key : String) (value : Json) : Except String Json := do
  let object ← json.getObj?
  return Json.mkObj (object.toArray.toList.filter (fun entry => entry.1 != key) ++ [(key,value)])

private def isVar (expression : Except String Airbender.Expr) (expected : Nat) : Bool :=
  match expression with | .ok (.Var n) => n == expected | _ => false

private def firstVar (artifact : Import.Blake2Worker.Artifact) (expected : Nat) : Bool :=
  match artifact.queries[0]? with
  | some (inputs,_) => match inputs[0]? with
    | some expression => isVar (artifact.lookup expression) expected
    | none => false
  | none => false

private def rejected {α : Type} : Except String α → Bool
  | .error _ => true | .ok _ => false

private def changeFirst (source : Json) (column : Nat) : Except String String := do
  let witness ← source.getObjVal? "witness_layout"
  let queries ← (← witness.getObjVal? "width_3_lookups").getArr?
  let some first := queries[0]? | throw "missing first query"
  let inputs ← (← first.getObjVal? "input_columns").getArr?
  let altered ← replaceField first "input_columns" (toJson (inputs.set! 0 (Json.mkObj [("Variable",Json.mkObj [("WitnessSubtree",toJson column)])])))
  let witness ← replaceField witness "width_3_lookups" (toJson (queries.set! 0 altered))
  return (← replaceField source "witness_layout" witness).compress

def main : IO UInt32 := do
  try
    let source ← IO.FS.readFile "artifacts/circuits/blake2-native-layout.json"
    check (source == Blake2Worker.QueryArtifact.querySourceBytes && source == Blake2Worker.Native.constraintsSourceBytes) "query and complete worker intakes retain identical source bytes"
    let actual ← IO.ofExcept (Import.Blake2Worker.parse source)
    check (actual.ranges.size == 2 && actual.clocks.size == 86 && actual.queries.size == 208) "complete296 native query observations"
    check (firstVar actual 274) "actual first query physical-to-logical source"
    let json ← IO.ofExcept (Json.parse source)
    let changed ← IO.ofExcept (changeFirst json 172)
    let changed ← IO.ofExcept (Import.Blake2Worker.parse changed)
    check (firstVar changed 272) "changed canonical query is retained as data, not semantics"
    let invalid ← IO.ofExcept (changeFirst json 648)
    check (rejected (Import.Blake2Worker.parse invalid)) "reject query physical column beyond selected layout"
    let witness ← IO.ofExcept (json.getObjVal? "witness_layout")
    let queries ← IO.ofExcept ((← IO.ofExcept (witness.getObjVal? "width_3_lookups")).getArr?)
    let witness ← IO.ofExcept (replaceField witness "width_3_lookups" (toJson (queries.extract 0 207)))
    let truncated ← IO.ofExcept (replaceField json "witness_layout" witness)
    check (rejected (Import.Blake2Worker.parse truncated.compress)) "reject missing last native fixed query"
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"FAIL {error}"
    return (1 : UInt32)
