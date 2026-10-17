import Airbender.Proofs.UnifiedReduced.Tables.Rotate12HighData
import Airbender.Proofs.Tables.UniformBlocks
import Airbender.Proofs.Tables.PeriodicColumns

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private theorem pattern_get (count : Nat) (f : Fin 256 → Nat)
    (n : Nat) (bound : n < count * 256) :
    (Block.periodic count 0 (Array.ofFn f)).get? n =
      some (f ⟨n % 256, Nat.mod_lt _ (by decide)⟩) := by
  have actual := periodic_get (Array.ofFn f) count 0 n (by simp)
    (by simpa only [Array.size_ofFn] using bound)
  simpa only [Nat.cast_zero, Array.size_ofFn, Array.getElem_ofFn,
    Nat.zero_mul, Nat.add_zero] using actual

private theorem last_prefix_get (n : Nat) (bound : n < 240) :
    (Block.periodic 15 1 (Array.replicate 16 1)).get? n = some (1 + n / 16) := by
  have actual := periodic_get (Array.replicate 16 1) 15 1 n (by simp)
    (by simpa only [Array.size_replicate] using bound)
  simpa only [Nat.cast_one, Array.size_replicate, Array.getElem_replicate, Nat.one_mul] using actual

private def highBlock (key : Nat) : Block :=
  .periodic 16 0 (Array.ofFn (fun i : Fin 256 => key ^^^ (i.val / 16)))
private def highBlocks : List Block :=
  (Array.ofFn (fun k : Fin 15 => highBlock (k.val + 1))).toList

private theorem rest_shape : ∀ block ∈ highBlocks, block.length = 4096 := by
  intro block member
  simp only [highBlocks, Array.toList_ofFn, List.mem_ofFn] at member
  obtain ⟨key, rfl⟩ := member
  simp only [highBlock, Block.length, Array.size_ofFn]

private theorem rest_selected (n : Nat) (bound : n < 15) :
    highBlocks[n]? = some (highBlock (n + 1)) := by
  simp only [highBlocks, Array.toList_ofFn, List.getElem?_ofFn, dif_pos bound]

private theorem high_reference_get (n : Nat) (bound : n < 65536) :
    rotate12HighReferenceColumn.get? n = some (n / 4096 ^^^ (n / 16 % 16)) := by
  unfold Column.get? rotate12HighReferenceColumn
  rw [raw_toList_append]
  change getFromBlocks
    (Block.affine 16 0 0 ::
      Block.periodic 15 0 (Array.ofFn (fun i : Fin 256 => (i.val / 16 + 1) % 16)) ::
      Block.periodic 15 1 (Array.replicate 16 1) :: highBlocks) n = _
  rw [getFromBlocks]
  simp only [Block.length]
  by_cases first : n < 16
  · rw [if_pos first]
    have a : n / 4096 = 0 := by omega
    have b : n / 16 % 16 = 0 := by omega
    simp [Block.get?, Block.length, first, a, b]
  · rw [if_neg first, getFromBlocks]
    simp only [Block.length, Array.size_ofFn, Nat.reduceMul]
    by_cases second : n - 16 < 3840
    · rw [if_pos second, pattern_get 15 _ _ second]
      have a : n / 4096 = 0 := by omega
      have b : ((n - 16) % 256 / 16 + 1) % 16 = n / 16 % 16 := by omega
      simp only [a, Nat.zero_xor, b]
    · rw [if_neg second, getFromBlocks]
      simp only [Block.length, Array.size_replicate, Nat.reduceMul]
      by_cases third : n - 16 - 3840 < 240
      · rw [if_pos third, last_prefix_get _ third]
        have a : n / 4096 = 0 := by omega
        have b : 1 + (n - 16 - 3840) / 16 = n / 16 % 16 := by omega
        simp only [a, Nat.zero_xor, b]
      · rw [if_neg third]
        have shift : n - 16 - 3840 - 240 = n - 4096 := by omega
        rw [shift, uniform4096_get _ rest_shape]
        rw [rest_selected _ (by omega : (n - 4096) / 4096 < 15)]
        simp only [Option.bind_some, highBlock]
        rw [pattern_get 16 _ _ (by omega : (n - 4096) % 4096 < 16 * 256)]
        change some (((n - 4096) / 4096 + 1) ^^^ ((n - 4096) % 4096 % 256 / 16)) =
          some (n / 4096 ^^^ (n / 16 % 16))
        congr 1
        congr 1 <;> omega

private theorem high_coarse (n : Nat) :
    (n / 256 ^^^ n % 256) / 16 = n / 4096 ^^^ (n / 16 % 16) := by
  simp only [show 16 = 2 ^ 4 from rfl, Nat.xor_div_two_pow]
  congr 1 <;> omega

theorem imported_rotate12high_output (n : Nat) (bound : n < 65536) :
    nativeRotate12Data.columns[5].get? n = some ((n / 256 ^^^ n % 256) / 16) := by
  rw [rotate12_high_column, high_reference_get n bound, high_coarse]

end Airbender.UnifiedReduced.Setup.Proofs
