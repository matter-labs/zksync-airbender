import Airbender.Review.Helpers.Tables.Subword.StoreClearData
import Airbender.Proofs.Tables.ImportedStorePlace

namespace Airbender.Verification.SubwordFixed
open Setup Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

private theorem clear_shape : storeClearData.columns[1] = Column.mk
    #[.periodic 256 256 (Array.replicate 256 0),
      .periodic 256 0 (Array.range 256)] := rfl

private theorem clear_low (n : Nat) (bound : n < 65536) :
    Block.get? (.periodic 256 256 (Array.replicate 256 0)) n =
      some (256 * (n / 256)) := by
  have row := periodic_get (Array.replicate 256 0) 256 256 n (by decide)
    (by simpa only [Array.size_replicate] using bound)
  simpa using row

/-- Native clearing retains the other byte for every key and both positions. -/
theorem storeClear_output (n : Nat) (bound : n < 131072) :
    storeClearData.columns[1].get? n = some (subwordStoreContribution true n) := by
  rw [clear_shape]
  by_cases first : n < 65536
  · have flag : n / 65536 % 2 = 0 := by omega
    have meaning : subwordStoreContribution true n = 256 * (n / 256) := by
      simp only [subwordStoreContribution, if_true, flag,
        Nat.zero_ne_one, if_false, Nat.mod_eq_of_lt first]
      omega
    rw [meaning]
    simp only [Column.get?, getFromBlocks, Block.length, Array.size_replicate,
      Nat.reduceMul, if_pos first]
    exact clear_low n first
  · have last : n - 65536 < 65536 := by omega
    have flag : n / 65536 % 2 = 1 := by omega
    have half : n % 65536 = n - 65536 := by omega
    have meaning : subwordStoreContribution true n = (n - 65536) % 256 := by
      simp only [subwordStoreContribution, if_true, flag, half]
    rw [meaning]
    simp only [Column.get?, getFromBlocks, Block.length, Array.size_replicate,
      Array.size_range, Nat.reduceMul, if_neg first, if_pos last]
    exact periodic_range 256 (n - 65536) last

end Airbender.Verification.SubwordFixed
