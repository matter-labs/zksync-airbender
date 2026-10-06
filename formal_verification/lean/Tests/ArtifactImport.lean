import Airbender.Review.AddSub.Artifact
import Airbender.Import.Parse

open Airbender Lean

private def check (ok : Bool) (label : String) : IO Unit :=
  if ok then IO.println s!"PASS {label}" else throw (IO.userError s!"FAIL {label}")

private def rejected {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

def main : IO UInt32 := do
  try
    let source ← IO.FS.readFile "../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json"
    let .ok c := parseCircuit source | throw (IO.userError "no-cache artifact failed import")
    check (c.structured_statements.size == 30) "no-cache artifact: all 30 constraints imported"
    check (source == AddSub.importedConstraintsSourceBytes) "embedded source equals current artifact bytes"
    let cached ← loadCircuit "../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json"
    check (!rejected cached) "cached sibling passes structural import"
    check (rejected (StrictJson.parse "{\"a\":0,\"a\":1}")) "duplicate object key rejected"
    check (rejected (StrictJson.parse "{\"x\":{\"a\":0,\"a\":1}}")) "nested duplicate rejected"
    check (rejected (StrictJson.parse "{} trailing")) "trailing input rejected"
    check (rejected (decodeCircuitJson (.mkObj (("unexpected", .null) ::
      (toJson c).getObj?.toOption.get!.toArray.toList)))) "unknown root field rejected"
    check (rejected ((fromJson? (toJson babyBearModulus)) : Except String Coefficient))
      "out-of-range Montgomery coefficient rejected"
    check (rejected (parseCircuit (toJson {c with trace_len := 0}).compress))
      "invalid trace length rejected"
    check (rejected (parseCircuit (toJson {c with witness_layout :=
      {c.witness_layout with total_width := 0}}).compress)) "invalid witness layout rejected"
    check (rejected (parseCircuit "{\"trace_len\":1.5}")) "fractional/incomplete circuit rejected"
    return (0 : UInt32)
  catch e =>
    IO.eprintln e.toString
    return (1 : UInt32)
