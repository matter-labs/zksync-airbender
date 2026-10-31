import Airbender.Proofs.Tables.LiteralSizes
import Airbender.Proofs.Tables.BinaryColumns
import Airbender.Proofs.Tables.TruncationColumn
import Airbender.Proofs.Tables.ReferenceShiftRows
import Airbender.Proofs.Tables.ShiftXorCertificate
import Airbender.Proofs.Tables.ShiftOrCertificate
import Airbender.Proofs.Tables.ShiftAndCertificate
import Mathlib.Tactic.IntervalCases

namespace Airbender.Verification.BinaryColumns
open Setup Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

private def binaryKind (kind : Fin 3) : Fin 4 := ⟨kind.val, by have := kind.isLt; omega⟩
private def output (kind : Fin 3) (n : Nat) : Nat :=
  if kind.val = 0 then n / 256 ^^^ n % 256
  else if kind.val = 1 then n / 256 ||| n % 256 else n / 256 &&& n % 256

private theorem checks (kind : Fin 3) :
    checkBlocks (output kind) 0 (data (binaryKind kind)).columns[2].blocks.toList = true := by
  fin_cases kind
  · exact ShiftCertificate.xor_outputs
  · exact ShiftCertificate.or_outputs
  · exact ShiftCertificate.and_outputs

theorem coverage (kind : Fin 3) :
    ((data (binaryKind kind)).columns[2].blocks.toList.map Block.length).sum = 65536 := by
  fin_cases kind
  ·
    dsimp only [data, binaryKind, byteXorData, byteOrData,
      Vector.getElem_mk, Fin.getElem_fin, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ]
    simp only [raw_toList_append, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Block.length, raw_literal_size, List.length_cons, List.length_nil,
      Array.size_ofFn, raw_size_append,
      Nat.reduceAdd, Nat.reduceMul]
  ·
    dsimp only [data, binaryKind, byteXorData, byteOrData,
      Vector.getElem_mk, Fin.getElem_fin, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ]
    simp only [raw_toList_append, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Block.length, raw_literal_size, List.length_cons, List.length_nil,
      Array.size_ofFn, Array.size_replicate, raw_size_append,
      Nat.reduceAdd, Nat.reduceMul]
  · exact ShiftPackedCertificate.coverage

private theorem output_get (kind : Fin 3) (n : Nat) (bound : n < 65536) :
    (data (binaryKind kind)).columns[2].get? n = some (output kind n) := by
  have values := checkBlocks_sound _ _ 0 n (checks kind) (by rw [coverage]; exact bound)
  simpa only [Column.get?, Nat.zero_add] using values

private theorem reference_binary (tag n : Nat) (bound : n < 65536) :
    binaryByteRow tag n =
      #v[n / 256, n % 256,
        if tag = 4 then n / 256 ^^^ n % 256
        else if tag = 6 then n / 256 ||| n % 256 else n / 256 &&& n % 256,
        0, 0, 0, 0, 0, 0, tag] := by
  simp [binaryByteRow, ByteUtils.splitTwoBytes, Nat.mod_eq_of_lt bound,
]

/-- Every physical column of the independently imported native bitwise rows. -/
theorem binary_row (kind : Fin 3) (n : Nat) (bound : n < 65536) :
    (data (binaryKind kind)).columns.map (fun column => (column.get? n).getD 0) =
      binaryByteRow (region (binaryKind kind)).id n := by
  rw [reference_binary _ _ bound]
  apply Vector.ext
  intro lane hLane
  interval_cases lane
  all_goals simp only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  · simp only [first _ _ bound, Option.getD_some]
  · simp only [second _ _ bound, Option.getD_some]
  · rw [output_get _ _ bound]
    fin_cases kind <;> rfl
  · simp only [padding _ ⟨0, by decide⟩ _ bound, Option.getD_some]
  · simp only [padding _ ⟨1, by decide⟩ _ bound, Option.getD_some]
  · simp only [padding _ ⟨2, by decide⟩ _ bound, Option.getD_some]
  · simp only [padding _ ⟨3, by decide⟩ _ bound, Option.getD_some]
  · simp only [padding _ ⟨4, by decide⟩ _ bound, Option.getD_some]
  · simp only [padding _ ⟨5, by decide⟩ _ bound, Option.getD_some]
  · simp only [tag _ _ bound, Option.getD_some]

/-- Native ID 8 retains both byte keys, the low five bits, padding and tag. -/
theorem truncation_row (n : Nat) (bound : n < 65536) :
    byteTruncateData.columns.map (fun column => (column.get? n).getD 0) =
      (#v[n / 256, n % 256, n / 256 % 32, 0, 0, 0, 0, 0, 0, 8] : Vector Nat 10) := by
  have first : byteTruncateData.columns[0].get? n = some (n / 256) := BinaryColumns.first ⟨3, by decide⟩ n bound
  have second : byteTruncateData.columns[1].get? n = some (n % 256) := BinaryColumns.second ⟨3, by decide⟩ n bound
  have output := truncation n bound
  have tag := BinaryColumns.tag ⟨3, by decide⟩ n bound
  apply Vector.ext
  intro lane hLane
  interval_cases lane
  all_goals simp only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  · simpa only [Option.getD_some] using congrArg (fun v => v.getD 0) first
  · simpa only [Option.getD_some] using congrArg (fun v => v.getD 0) second
  · simp only [output, Option.getD_some]
  · exact congrArg (fun v => v.getD 0) (padding ⟨3, by decide⟩ ⟨0, by decide⟩ n bound)
  · exact congrArg (fun v => v.getD 0) (padding ⟨3, by decide⟩ ⟨1, by decide⟩ n bound)
  · exact congrArg (fun v => v.getD 0) (padding ⟨3, by decide⟩ ⟨2, by decide⟩ n bound)
  · exact congrArg (fun v => v.getD 0) (padding ⟨3, by decide⟩ ⟨3, by decide⟩ n bound)
  · exact congrArg (fun v => v.getD 0) (padding ⟨3, by decide⟩ ⟨4, by decide⟩ n bound)
  · exact congrArg (fun v => v.getD 0) (padding ⟨3, by decide⟩ ⟨5, by decide⟩ n bound)
  · exact congrArg (fun v => v.getD 0) tag

/-- Exact imported physical rows for native bitwise table 4. -/
theorem xor_row (n : Nat) (bound : n < 65536) :
    byteXorData.columns.map (fun column => (column.get? n).getD 0) =
      binaryByteRow 4 n := by
  have values := binary_row ⟨0, by decide⟩ n bound
  simpa only [data, region, binaryKind, Vector.getElem_mk,
    Fin.getElem_fin, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, show byteXorDataRegion.id = 4 from rfl] using values

/-- Exact imported physical rows for native bitwise table 6. -/
theorem or_row (n : Nat) (bound : n < 65536) :
    byteOrData.columns.map (fun column => (column.get? n).getD 0) =
      binaryByteRow 6 n := by
  have values := binary_row ⟨1, by decide⟩ n bound
  simpa only [data, region, binaryKind, Vector.getElem_mk,
    Fin.getElem_fin, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, show byteOrDataRegion.id = 6 from rfl] using values

/-- Exact imported physical rows for native bitwise table 7. -/
theorem and_row (n : Nat) (bound : n < 65536) :
    byteAndData.columns.map (fun column => (column.get? n).getD 0) =
      binaryByteRow 7 n := by
  have values := binary_row ⟨2, by decide⟩ n bound
  simpa only [data, region, binaryKind, Vector.getElem_mk,
    Fin.getElem_fin, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, show byteAndDataRegion.id = 7 from rfl] using values

end Airbender.Verification.BinaryColumns
