import Airbender.Proofs.UnifiedReduced.Tables.ImportedWideKeys
import Airbender.Proofs.UnifiedReduced.Tables.ImportedTruncation
import Airbender.Proofs.Tables.ImportedBinaryRows

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

/-- All independently imported wide binary fields, including the native tag. -/
theorem imported_wide_row (kind : Fin 3) (n : Nat) (bound : n < 65536) :
    (wideData kind).columns.map (fun column => (column.get? n).getD 0) =
      ((ordinaryData kind).columns.map (fun column => (column.get? n).getD 0)).set 9
        (52 + kind.val) := by
  apply Vector.ext
  intro lane hLane
  by_cases last : lane = 9
  · subst lane
    have shape : (wideData kind).columns[9] = Column.mk #[.affine 65536 (52 + kind.val) 0] := by
      fin_cases kind <;> rfl
    simp only [Vector.getElem_map, Vector.getElem_set_self, shape, Column.get?,
      getFromBlocks, Block.get?, Block.length, if_pos bound]
    rw [if_pos (by omega)]
    simpa only [Option.getD_some, Int.zero_mul, Int.add_zero, Int.natCast_add, Nat.cast_ofNat] using
      Int.toNat_natCast (52 + kind.val)
  · rw [Vector.getElem_set_ne (by decide : 9 < 10) hLane (by omega : 9 ≠ lane)]
    simp only [Vector.getElem_map]
    by_cases second : lane = 1
    · subst lane
      rw [wide_second_key kind n bound]
      have sample := BinaryColumns.second ⟨kind.val, by omega⟩ n bound
      have same : ordinaryData kind = BinaryColumns.data ⟨kind.val, by omega⟩ := by
        fin_cases kind <;> rfl
      rw [same, sample]
    · rw [wide_columns kind ⟨lane, by omega⟩ second]

/-- Native truncation keeps the original real-row meaning despite a different
    first periodic group in the setup compression. -/
theorem imported_truncation_row (n : Nat) (bound : n < 65536) :
    nativeTruncationData.columns.map (fun column => (column.get? n).getD 0) =
      byteTruncateData.columns.map (fun column => (column.get? n).getD 0) := by
  apply Vector.ext
  intro lane hLane
  simp only [Vector.getElem_map]
  interval_cases lane
  · rfl
  · rfl
  · rw [imported_truncation_output n bound, BinaryColumns.truncation n bound]
  all_goals rfl

end Airbender.UnifiedReduced.Setup.Proofs
