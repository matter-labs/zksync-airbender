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
import Tests.NonDeterminism
import Tests.Comparison
import Tests.Discarded
import Tests.Branch
import Tests.Jump
import Tests.MulDiv
import Tests.MulDivProduct
import Tests.Division
import Tests.ShiftBinop
import Tests.Binop
import Tests.Shifts

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
    let mulSource ← IO.FS.readFile "../../cs/compiled_circuits/unsigned_mul_div_layout_no_caches_gkr.json"
    let .ok mul := parseCircuit mulSource | throw (IO.userError "mul/div artifact failed import")
    let .ok mulQueries := mul.mulDivQueries | throw (IO.userError "mul/div queries failed import")
    check (mul.structured_statements.size == 43 &&
      (FlatOperation.constraints (MulDiv.importedConstraints (p := babyBearModulus))).length == 43 &&
      (FlatOperation.lookups (MulDiv.importedConstraints (p := babyBearModulus))).length == 16)
      "mul/div: 43 equations and all 16 native lookups"
    check (mulQueries.map Prod.fst == #[1, 41, 41, 26, 26, 26, 41, 41] &&
      mulSource == MulDiv.importedConstraintsSourceBytes)
      "mul/div: fixed-table IDs and source bytes match"
    check (rejected (Circuit.mulDivQueries {mul with scratch_space_mapping_rev :=
      ⟨mul.scratch_space_mapping_rev.entries.filter (fun (i, _) => i != 5)⟩}))
      "lookup with missing scratch reverse map rejected"
    check (rejected (Circuit.mulDivQueries {mul with scratch_space_mapping :=
      (mul.scratch_space_mapping.filter (fun (_, i) => i != 5))}))
      "lookup with missing scratch forward map rejected"
    check (rejected (Circuit.mulDivQueries {mul with scratch_space_mapping_rev :=
      ⟨mul.scratch_space_mapping_rev.entries.map (fun (i, a) =>
        (i, if i == 5 then GKRAddress.InnerLayer 1 11 else a))⟩}))
      "lookup with inconsistent scratch maps rejected"
    check (rejected (Circuit.mulDivQueries {mul with placement_data :=
      ⟨mul.placement_data.entries.push (71, GKRAddress.InnerLayer 1 10)⟩}))
      "lookup with ambiguous scratch placement rejected"
    let shiftSource ← IO.FS.readFile "../../cs/compiled_circuits/shift_binop_layout_no_caches_gkr.json"
    let .ok shift := parseCircuit shiftSource | throw (IO.userError "shift/binop artifact failed import")
    let .ok shiftQueries := shift.shiftBinopQueries | throw (IO.userError "dynamic byte queries failed import")
    let byteLookups := (FlatOperation.lookups (ShiftBinop.importedConstraints (p := babyBearModulus))).drop 2
    check (shift.structured_statements.size == 52 && shiftQueries.size == 5 &&
      byteLookups.length == 5 && shiftSource == ShiftBinop.importedConstraintsSourceBytes)
      "shift/binop: 52 equations, all seven lookups and source bytes match"
    let tagEnv := Verification.environment (fun v => if v == 55 then 3 else (4 : ZMod babyBearModulus))
    check (byteLookups.map (fun q => (q.entry.toArray.back!.eval tagEnv).val) == [3, 4, 4, 4, 4])
      "shift/binop: every dynamic table tag is preserved"
    check (rejected (Circuit.shiftBinopQueries {shift with total_tables_size := 1573120}))
      "shift/binop: wrong setup/decoder boundary rejected"
    let wrongOffsets := shift.table_offsets.set! 5 ⟨100, by decide⟩
    check (rejected (Circuit.shiftBinopQueries {shift with table_offsets := wrongOffsets}))
      "shift/binop: populated unsupported table region rejected"
    check (rejected (Circuit.shiftBinopQueries {shift with scratch_space_mapping_rev :=
      ⟨shift.scratch_space_mapping_rev.entries.filter (fun (i, _) => i != 3)⟩}))
      "shift/binop: unresolved dynamic-tag scratch alias rejected"
    let some byteQuery := shift.generic_lookups[0]? | throw (IO.userError "missing byte query")
    let one : Coefficient := ⟨⟨268435454, by decide⟩⟩
    let replaceByteQuery := fun changed =>
      {shift with generic_lookups := shift.generic_lookups.set! 0 changed}
    check (rejected (Circuit.shiftBinopQueries (replaceByteQuery
      {byteQuery with columns := byteQuery.columns.set! 8 ⟨#[], one⟩})))
      "shift/binop: nonzero lookup padding rejected"
    check (rejected (Circuit.shiftBinopQueries (replaceByteQuery
      {byteQuery with lookup_set_index := 1})))
      "shift/binop: wrong query-set identity rejected"
    let comparisonSource ← IO.FS.readFile "../../cs/compiled_circuits/jump_branch_slt_layout_no_caches_gkr.json"
    let .ok comparison := parseCircuit comparisonSource | throw (IO.userError "comparison artifact failed import")
    check (comparison.structured_statements.size == 26 &&
      (FlatOperation.constraints (JumpBranchSlt.importedConstraints (p := babyBearModulus))).length == 26)
      "jump/branch/SLT: all 26 retained assertions imported"
    let .ok comparisonQueries := comparison.comparisonQueries | throw (IO.userError "comparison queries failed import")
    check (comparisonQueries.map Prod.fst == #[1, 5, 31, 2] &&
      (FlatOperation.lookups (JumpBranchSlt.importedConstraints (p := babyBearModulus))).length == 8)
      "jump/branch/SLT: four range and four fixed-table queries"
    let some query := comparison.generic_lookups[0]? | throw (IO.userError "missing comparison query")
    let some key := query.columns[0]? | throw (IO.userError "missing comparison key")
    let some tag := query.columns[9]? | throw (IO.userError "missing comparison table ID")
    let zero : Coefficient := ⟨⟨0, by decide⟩⟩
    let replaceQuery := fun changed =>
      {comparison with generic_lookups := comparison.generic_lookups.set! 0 changed}
    check (rejected (Circuit.comparisonQueries (replaceQuery
      {query with columns := query.columns.set! 9 {tag with constant := zero}})))
      "unsupported comparison table ID rejected"
    check (rejected (Circuit.comparisonQueries (replaceQuery
      {query with columns := query.columns.set! 9 {tag with linear_terms := key.linear_terms}})))
      "dynamic comparison table ID rejected"
    check (rejected (Circuit.comparisonQueries (replaceQuery
      {query with columns := query.columns.set! 2 key})))
      "nonzero comparison padding rejected"
    check (rejected (Circuit.comparisonQueries (replaceQuery
      {query with columns := query.columns.pop}))) "invalid comparison width rejected"
    check (rejected (Circuit.comparisonQueries {comparison with placement_data :=
      ⟨comparison.placement_data.entries.filter (fun (v, _) => v != 34)⟩}))
      "comparison query with missing logical placement rejected"
    let some (_, address) := comparison.placement_data.entries.find? (fun (v, _) => v == 34)
      | throw (IO.userError "missing comparison placement")
    check (rejected (Circuit.comparisonQueries {comparison with placement_data :=
      ⟨comparison.placement_data.entries.push (99, address)⟩}))
      "comparison query with ambiguous logical placement rejected"
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
