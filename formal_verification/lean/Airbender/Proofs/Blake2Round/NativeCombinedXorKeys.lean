import Airbender.Proofs.Blake2Round.NativeCombinedKeyShapes
import Airbender.Proofs.Blake2Round.NativeCombinedTemplateValues

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs NativeXorKeyHelpers
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

open CombinedKeyData

private theorem stored_periodic (values : Array Nat) (width count n result : Nat)
    (size : values.size = width) (bound : n < count * width)
    (present : values[n % width]? = some result) :
    (Column.mk #[.periodic count 0 values]).get? n = some result := by
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, size, bound, present]

/-- The combined row stores the four native input slices independently. -/
theorem combined_keys_get (n : Nat) (hn : n < 16384) :
    xor4x3Data.columns[0].get? n = some (n / 1024) ∧
    xor4x3Data.columns[1].get? n = some (n / 128 % 8) ∧
    xor4x3Data.columns[2].get? n = some (n / 8 % 16) ∧
    xor4x3Data.columns[3].get? n = some (n % 8) := by
  rw [combined_key0_shape, combined_key1_shape, combined_key2_shape, combined_key3_shape]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Column.get?, getFromBlocks, Block.length, Array.size_replicate,
      if_pos hn] using periodic_constant_get 1024 16 n (by decide) hn
  · have value := combined_second_optional (n % 1024) (by omega)
    have index : n % 1024 / 128 = n / 128 % 8 := by omega
    rw [index] at value
    exact stored_periodic secondTemplate 1024 16 n _ second_size hn value
  · have value := combined_third_optional (n % 128) (by omega)
    have index : n % 128 / 8 = n / 8 % 16 := by omega
    rw [index] at value
    exact stored_periodic thirdTemplate 128 128 n _ third_size hn value
  · simpa only [Column.get?, getFromBlocks, Block.length, Array.size_range,
      if_pos hn] using periodic_range_get 8 2048 n (by decide) hn

end Airbender.Blake2Round.Proofs
