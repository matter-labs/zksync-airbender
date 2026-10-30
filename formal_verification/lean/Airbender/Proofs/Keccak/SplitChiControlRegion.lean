import Airbender.Data.Setup.Keccak.Chi5Generic
import Airbender.Proofs.Keccak.SplitControlSetup
import Airbender.Proofs.Keccak.SplitColumnShift

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup
set_option warningAsError true
set_option maxRecDepth 65536
-- Check the short controller suffix and one prefix length per column.
set_option maxHeartbeats 2400000

/-- Both views retain the same complete native setup source. -/
theorem chi5_generic_source : chi5GenericSourceBytes = chi5ControlSourceBytes := by rfl

private theorem chi5_prefix_length : ∀ column : Fin 11,
    ((chi5GenericPrefixes[column.val]).blocks.toList.map Block.length).sum = chi5GenericPrefixLengths[column.val] := by
  intro column
  fin_cases column
  all_goals simp [chi5GenericPrefixes, chi5GenericPrefixLengths]


private theorem chi5_prefix_cut : ∀ column : Fin 11,
    chi5GenericPrefixLengths[column.val] + chi5GenericControlOffsets[column.val] = 1048576 := by
  decide +kernel

private theorem chi5_columns : ∀ column : Fin 11,
    chi5Generic.columns[column.val] =
      Column.mk (chi5GenericPrefixes[column.val].blocks ++ chi5GenericSuffixes[column.val].blocks) := by
  intro column
  fin_cases column <;> rfl

private theorem chi5_controller_suffix_equal : ∀ j : Fin chi5Control.length, ∀ column : Fin 11,
    signedValue ((chi5GenericSuffixes[column.val].get? (chi5GenericControlOffsets[column.val] + j.val)).getD 0) =
      (chi5Control.row j)[column.val] := by
  decide +kernel


/-- Every controller row equals its exact row in the complete native table. -/
theorem chi5_controller_rows_equal : ∀ j : Fin chi5Control.length,
    chi5Generic.row ⟨1048576 + j.val, by
      have bound := j.isLt
      change j.val < 121 at bound
      change 1048576 + j.val < 1048697
      omega⟩ = chi5Control.row j := by
  intro j
  ext column bound
  simp only [TableData.row, Vector.getElem_map]
  change signedValue ((chi5Generic.columns[column].get? (0 + (1048576 + j.val))).getD 0) =
    signedValue ((chi5Control.columns[column].get? (0 + j.val)).getD 0)
  simp only [Nat.zero_add]
  have same := chi5_columns ⟨column, bound⟩
  change chi5Generic.columns[column] = _ at same
  rw [same]
  have cut := chi5_prefix_cut ⟨column, bound⟩
  change chi5GenericPrefixLengths[column] + chi5GenericControlOffsets[column] = 1048576 at cut
  have index : 1048576 + j.val = chi5GenericPrefixLengths[column] +
      (chi5GenericControlOffsets[column] + j.val) := by omega
  change signedValue (((Column.mk (chi5GenericPrefixes[column].blocks ++
    chi5GenericSuffixes[column].blocks)).get? (1048576 + j.val)).getD 0) = _
  rw [index, Airbender.Setup.Proofs.column_append_shift _ _ _ _ (chi5_prefix_length ⟨column, bound⟩)]
  have tail := chi5_controller_suffix_equal j ⟨column, bound⟩
  simp only [TableData.row, Vector.getElem_map] at tail
  change signedValue ((chi5GenericSuffixes[column].get?
    (chi5GenericControlOffsets[column] + j.val)).getD 0) =
      signedValue ((chi5Control.columns[column].get? (0 + j.val)).getD 0) at tail
  simpa only [Nat.zero_add] using tail

end Airbender.Keccak.Split.Native.Fixed.Proofs
