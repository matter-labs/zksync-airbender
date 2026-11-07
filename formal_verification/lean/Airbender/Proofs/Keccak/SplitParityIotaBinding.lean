import Airbender.Data.Setup.Keccak.ColumnParityIota
import Airbender.Proofs.Keccak.ImportedFixed

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000

/-- All native byte-iota columns except the differently partitioned counter retain the same blocks. -/
theorem column_parity_iota_other_columns (column : Fin 8) (other : column.val ≠ 1) :
    columnParityIota.columns[column.val] = Airbender.Keccak.iotaData.columns[column.val] := by
  fin_cases column
  all_goals first | contradiction | rfl

/-- The actual native counter column contains the original byte-iota key. -/
theorem column_parity_iota_counter (n : Nat) (bound : n < 65536) :
    (columnParityIota.columns[1].get? n) = some (n / 256) := by
  change (Column.mk #[.periodic 256 1 (Array.replicate 256 0)]).get? n = some (n / 256)
  have residue : n % 256 < 256 := Nat.mod_lt _ (by decide)
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, bound, residue]
  simpa only [Int.natCast_ediv, Nat.cast_ofNat] using
    And.intro (Int.natCast_nonneg (n / 256)) (Int.toNat_natCast (n / 256))

/-- Every actual native byte-iota row equals the unchanged arithmetic reference. -/
theorem column_parity_iota_reference (n : Nat) (bound : n < 65536) :
    columnParityIota.columns.map (fun column => (column.get? n).getD 0) = Airbender.Keccak.byteRow 38 n := by
  have old := Airbender.Keccak.Proofs.byte_region_reference 1 n bound
  have oldRow : Airbender.Keccak.iotaData.columns.map (fun column => (column.get? n).getD 0) =
      Airbender.Keccak.byteRow 38 n := old
  apply Vector.ext
  intro column valid
  simp only [Vector.getElem_map]
  by_cases counter : column = 1
  · subst column
    rw [column_parity_iota_counter n bound]
    rfl
  · rw [column_parity_iota_other_columns ⟨column, valid⟩ counter]
    simpa only [Vector.getElem_map] using congrArg (fun row : Vector Nat 8 => row[column]) oldRow

end Airbender.Keccak.Split.Native.Fixed.Proofs
