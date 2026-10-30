import Airbender.Data.Setup.Keccak.ThetaRhoGeneric
import Airbender.Proofs.Keccak.SplitControlSetup
import Airbender.Proofs.Keccak.SplitColumnShift

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup
set_option warningAsError true
set_option maxRecDepth 65536
-- Check the short controller suffix and one prefix length per column.
set_option maxHeartbeats 2400000

/-- Both views retain the same complete native setup source. -/
theorem theta_rho_generic_source : thetaRhoGenericSourceBytes = thetaRhoControlSourceBytes := by rfl

private theorem theta_rho_prefix_length : ∀ column : Fin 9,
    ((thetaRhoGenericPrefixes[column.val]).blocks.toList.map Block.length).sum = thetaRhoGenericPrefixLengths[column.val] := by
  intro column
  fin_cases column
  all_goals simp [thetaRhoGenericPrefixes, thetaRhoGenericPrefixLengths]


private theorem theta_rho_prefix_cut : ∀ column : Fin 9,
    thetaRhoGenericPrefixLengths[column.val] + thetaRhoGenericControlOffsets[column.val] = 589824 := by
  decide +kernel

private theorem theta_rho_columns : ∀ column : Fin 9,
    thetaRhoGeneric.columns[column.val] =
      Column.mk (thetaRhoGenericPrefixes[column.val].blocks ++ thetaRhoGenericSuffixes[column.val].blocks) := by
  intro column
  fin_cases column <;> rfl

private theorem theta_rho_controller_suffix_equal : ∀ j : Fin thetaRhoControl.length, ∀ column : Fin 9,
    signedValue ((thetaRhoGenericSuffixes[column.val].get? (thetaRhoGenericControlOffsets[column.val] + j.val)).getD 0) =
      (thetaRhoControl.row j)[column.val] := by
  decide +kernel


/-- Every controller row equals its exact row in the complete native table. -/
theorem theta_rho_controller_rows_equal : ∀ j : Fin thetaRhoControl.length,
    thetaRhoGeneric.row ⟨589824 + j.val, by
      have bound := j.isLt
      change j.val < 121 at bound
      change 589824 + j.val < 590066
      omega⟩ = thetaRhoControl.row j := by
  intro j
  ext column bound
  simp only [TableData.row, Vector.getElem_map]
  change signedValue ((thetaRhoGeneric.columns[column].get? (0 + (589824 + j.val))).getD 0) =
    signedValue ((thetaRhoControl.columns[column].get? (0 + j.val)).getD 0)
  simp only [Nat.zero_add]
  have same := theta_rho_columns ⟨column, bound⟩
  change thetaRhoGeneric.columns[column] = _ at same
  rw [same]
  have cut := theta_rho_prefix_cut ⟨column, bound⟩
  change thetaRhoGenericPrefixLengths[column] + thetaRhoGenericControlOffsets[column] = 589824 at cut
  have index : 589824 + j.val = thetaRhoGenericPrefixLengths[column] +
      (thetaRhoGenericControlOffsets[column] + j.val) := by omega
  change signedValue (((Column.mk (thetaRhoGenericPrefixes[column].blocks ++
    thetaRhoGenericSuffixes[column].blocks)).get? (589824 + j.val)).getD 0) = _
  rw [index, Airbender.Setup.Proofs.column_append_shift _ _ _ _ (theta_rho_prefix_length ⟨column, bound⟩)]
  have tail := theta_rho_controller_suffix_equal j ⟨column, bound⟩
  simp only [TableData.row, Vector.getElem_map] at tail
  change signedValue ((thetaRhoGenericSuffixes[column].get?
    (thetaRhoGenericControlOffsets[column] + j.val)).getD 0) =
      signedValue ((thetaRhoControl.columns[column].get? (0 + j.val)).getD 0) at tail
  simpa only [Nat.zero_add] using tail

end Airbender.Keccak.Split.Native.Fixed.Proofs
