import Airbender.Data.Tables.Subword.StorePlaceData
import Airbender.Proofs.Tables.ReferenceSubwordRows
import Airbender.Proofs.Tables.PeriodicColumns

namespace Airbender.Verification.SubwordFixed
open Setup Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

private def highValues : Array Nat :=
  match (storePlaceData.columns[1].blocks[1]? : Option Setup.Block) with
  | some (.periodic _ _ values) => values
  | _ => #[]

private theorem high_size : highValues.size = 256 := by decide +kernel
private theorem high_samples (i : Fin 256) :
    highValues[i.val]'(by rw [high_size]; exact i.isLt) = 256 * i.val := by
  revert i
  decide +kernel

private theorem output_shape : storePlaceData.columns[1] = Column.mk
    #[.periodic 256 0 (Array.range 256), .periodic 256 0 highValues] := rfl

theorem periodic_range (count n : Nat) (bound : n < count * 256) :
    Block.get? (.periodic count 0 (Array.range 256)) n = some (n % 256) := by
  have row := periodic_get (Array.range 256) count 0 n (by decide)
    (by simpa only [Array.size_range] using bound)
  simpa using row

private theorem high_get (n : Nat) (bound : n < 65536) :
    Block.get? (.periodic 256 0 highValues) n = some (256 * (n % 256)) := by
  have extent : n < 256 * highValues.size := by rw [high_size]; omega
  have positive : 0 < highValues.size := by rw [high_size]; decide
  have row := periodic_get highValues 256 0 n positive extent
  have value := high_samples ⟨n % 256, Nat.mod_lt _ (by decide)⟩
  simpa only [Int.natCast_zero, high_size, Nat.zero_mul, Nat.add_zero, value] using row

/-- Native store-byte placement covers both positions and every encoded key. -/
theorem storePlace_output (n : Nat) (bound : n < 131072) :
    storePlaceData.columns[1].get? n = some (subwordStoreContribution false n) := by
  rw [output_shape]
  by_cases first : n < 65536
  · have flag : n / 65536 % 2 = 0 := by omega
    simp only [Column.get?, getFromBlocks, Block.length, Array.size_range,
      Nat.reduceMul, if_pos first]
    simpa only [subwordStoreContribution, Bool.false_eq_true, if_false, flag,
      Nat.zero_ne_one, Nat.mul_one] using periodic_range 256 n first
  · have last : n - 65536 < 65536 := by omega
    have flag : n / 65536 % 2 = 1 := by omega
    have residue : (n - 65536) % 256 = n % 256 := by omega
    simp only [Column.get?, getFromBlocks, Block.length, Array.size_range,
      Nat.reduceMul, if_neg first, high_size, if_pos last]
    simpa only [subwordStoreContribution, Bool.false_eq_true, if_false, flag,
      if_true, residue, Nat.mul_comm] using high_get (n - 65536) last

end Airbender.Verification.SubwordFixed
