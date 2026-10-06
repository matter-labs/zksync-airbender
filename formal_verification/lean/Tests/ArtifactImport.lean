import Airbender.Review.AddSub.Artifact
import Airbender.Review.JumpBranchSlt.Artifact
import Airbender.Import.Parse
import Airbender.Review.Properties
import Airbender.Proofs.BabyBear
import Airbender.Proofs.Constraints
import Tests.ZeroRegister
import Tests.InactiveRow
import Tests.Modular
import Tests.PC

open Airbender Lean

private def check (ok : Bool) (label : String) : IO Unit :=
  if ok then IO.println s!"PASS {label}" else throw (IO.userError s!"FAIL {label}")

private def rejected {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

/-- Check that the native lookup relation rejects the first value outside the table. -/
example : ¬ (Verification.range16 (Expression.const (65536 : ZMod babyBearModulus))).Contains
    (Verification.environment (fun _ => 0)) := by
  intro h
  have bound := Verification.range16_bound h
  norm_num [Expression.eval, Arithmetic.limbBase, ZMod.val_ofNat, babyBearModulus] at bound

def main : IO UInt32 := do
  try
    let source ← IO.FS.readFile "../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json"
    let .ok c := parseCircuit source | throw (IO.userError "no-cache artifact failed import")
    check (c.structured_statements.size == 30) "no-cache artifact: all 30 constraints imported"
    let .ok ranges := c.range16Expressions | throw (IO.userError "range lookup import failed")
    check (ranges.size == 6 &&
      (FlatOperation.lookups (AddSub.importedConstraints (p := babyBearModulus))).length == 6)
      "all six range queries emitted as native Clean lookups"
    check (rejected (Circuit.range16Expressions {c with placement_data :=
      ⟨c.placement_data.entries.filter (fun (v, _) => v != 33)⟩}))
      "range query with missing logical placement rejected"
    check (rejected (Circuit.range16Expressions {c with placement_data :=
      ⟨c.placement_data.entries.push (48, .BaseLayerMemory 15)⟩}))
      "range query with ambiguous logical placement rejected"
    check (source == AddSub.importedConstraintsSourceBytes) "embedded source equals current artifact bytes"
    let comparisonSource ← IO.FS.readFile "../../cs/compiled_circuits/jump_branch_slt_layout_no_caches_gkr.json"
    let .ok comparison := parseCircuit comparisonSource | throw (IO.userError "comparison artifact failed import")
    check (comparison.structured_statements.size == 26 &&
      (FlatOperation.constraints (JumpBranchSlt.importedConstraints (p := babyBearModulus))).length == 26)
      "jump/branch/SLT: all 26 retained assertions imported"
    check ((FlatOperation.lookups (JumpBranchSlt.importedConstraints (p := babyBearModulus))).length == 4)
      "jump/branch/SLT: four native range queries"
    check (comparisonSource == JumpBranchSlt.importedConstraintsSourceBytes)
      "jump/branch/SLT: embedded source equals current artifact bytes"
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
