import Airbender.Proofs.UnifiedReduced.Tables.Rotate7HighData
import Airbender.Proofs.Tables.PeriodicColumns

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private theorem constant_get (length value n : Nat) (bound : n < length) :
    (Block.affine length value 0).get? n = some value := by
  simp [Block.get?, Block.length, bound]

private theorem pattern_get (f : Fin 256 → Nat) (n : Nat) (bound : n < 32512) :
    (Block.periodic 127 0 (Array.ofFn f)).get? n =
      some (f ⟨n % 256, Nat.mod_lt _ (by decide)⟩) := by
  have actual := periodic_get (Array.ofFn f) 127 0 n (by simp)
    (by simpa only [Array.size_ofFn] using bound)
  simpa only [Nat.cast_zero, Array.size_ofFn, Array.getElem_ofFn,
    Nat.zero_mul, Nat.add_zero] using actual

private theorem high_reference_get (n : Nat) (bound : n < 65536) :
    rotate7HighReferenceColumn.get? n = some (n / 32768 ^^^ (n / 128 % 2)) := by
  change getFromBlocks [Block.affine 128 0 0,
    Block.periodic 127 0 (Array.ofFn (fun i : Fin 256 => 1 - i.val / 128)),
    Block.affine 256 1 0,
    Block.periodic 127 0 (Array.ofFn (fun i : Fin 256 => i.val / 128)),
    Block.affine 128 0 0] n = _
  rw [getFromBlocks]
  simp only [Block.length]
  by_cases first : n < 128
  · rw [if_pos first]
    have a : n / 32768 = 0 := by omega
    have b : n / 128 % 2 = 0 := by omega
    rw [constant_get 128 0 n first, a, b]
    rfl
  · rw [if_neg first, getFromBlocks]
    simp only [Block.length, Array.size_ofFn, Nat.reduceMul]
    by_cases second : n - 128 < 32512
    · rw [if_pos second, pattern_get _ _ second]
      have a : n / 32768 = 0 := by omega
      have b : 1 - ((n - 128) % 256 / 128) = n / 128 % 2 := by omega
      simp only [a, Nat.zero_xor]
      change some (1 - ((n - 128) % 256 / 128)) = some (n / 128 % 2)
      rw [b]
    · rw [if_neg second, getFromBlocks]
      simp only [Block.length]
      by_cases third : n - 128 - 32512 < 256
      · rw [if_pos third]
        by_cases half : n < 32768
        · have a : n / 32768 = 0 := by omega
          have b : n / 128 % 2 = 1 := by omega
          rw [constant_get 256 1 _ third, a, b]
          rfl
        · have a : n / 32768 = 1 := by omega
          have b : n / 128 % 2 = 0 := by omega
          rw [constant_get 256 1 _ third, a, b]
          rfl
      · rw [if_neg third, getFromBlocks]
        simp only [Block.length, Array.size_ofFn, Nat.reduceMul]
        by_cases fourth : n - 128 - 32512 - 256 < 32512
        · rw [if_pos fourth, pattern_get _ _ fourth]
          have a : n / 32768 = 1 := by omega
          change some ((n - 128 - 32512 - 256) % 256 / 128) =
            some (n / 32768 ^^^ (n / 128 % 2))
          by_cases low : n / 128 % 2 = 0
          · have value : (n - 128 - 32512 - 256) % 256 / 128 = 1 := by omega
            simp [a, low, value]
          · have lowOne : n / 128 % 2 = 1 := by omega
            have value : (n - 128 - 32512 - 256) % 256 / 128 = 0 := by omega
            simp [a, lowOne, value]
        · rw [if_neg fourth, getFromBlocks]
          simp only [Block.length]
          have last : n - 128 - 32512 - 256 - 32512 < 128 := by omega
          rw [if_pos last]
          have a : n / 32768 = 1 := by omega
          have b : n / 128 % 2 = 1 := by omega
          rw [constant_get 128 0 _ last, a, b]
          rfl

private theorem high_coarse (n : Nat) :
    (n / 256 ^^^ n % 256) / 128 = n / 32768 ^^^ (n / 128 % 2) := by
  simp only [show 128 = 2 ^ 7 from rfl, Nat.xor_div_two_pow]
  congr 1 <;> omega

theorem imported_rotate7high_output (n : Nat) (bound : n < 65536) :
    nativeRotate7Data.columns[2].get? n = some ((n / 256 ^^^ n % 256) / 128) := by
  rw [rotate7_high_column, high_reference_get n bound, high_coarse]

end Airbender.UnifiedReduced.Setup.Proofs
