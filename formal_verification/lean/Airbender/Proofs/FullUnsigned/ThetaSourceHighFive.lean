import Airbender.Proofs.FullUnsigned.SourceUniformChunks
import Airbender.Proofs.FullUnsigned.SourceBlockWindows
import Airbender.Proofs.FullUnsigned.ThetaSourceLowZero
import Airbender.Proofs.Keccak.SplitThetaFragmentValues

namespace Airbender.Setup.SourceCaptureThetaProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
-- Direct template selection proves all rows in this overflow case.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private noncomputable def sourceColumn : Column := (SourceCaptureTheta.columns[4]?).getD ⟨#[]⟩
private noncomputable def window : List Block := (sourceColumn.blocks.toList.drop 36).take 32
private noncomputable def blockAt (index : Fin 32) : Block := (window[index.val]?).getD (.affine 0 0 0)
private def patternArray (high : Fin 32) : Array Nat :=
  (List.ofFn fun index : Fin 256 => high.val ^^^ (index.val / 8)).toArray

private theorem prefix_length : ((sourceColumn.blocks.toList.take 36).map Block.length).sum = 393216 := by low_source_kernel_rfl
private theorem window_count : window.length = 32 := by low_source_kernel_rfl
private theorem window_length : (window.map Block.length).sum = 65536 := by low_source_kernel_rfl
private theorem window_lengths : ∀ block ∈ window, block.length = 2048 := by decide +kernel
private theorem shapes (index : Fin 32) : blockAt index = .periodic 8 0 (patternArray index) := by
  fin_cases index <;> low_source_kernel_rfl

private theorem pattern_size (high : Fin 32) : (patternArray high).size = 256 := by
  simp only [patternArray, List.size_toArray, List.length_ofFn]

private theorem block_get (high : Fin 32) (offset : Fin 2048) :
    (blockAt high).get? offset.val = some (high.val ^^^ (offset.val / 8 % 32)) := by
  rw [shapes]
  have sampled := periodic_get (patternArray high) 8 0 offset.val (by rw [pattern_size]; decide +kernel)
    (by rw [pattern_size]; exact offset.isLt)
  simp only [pattern_size, Nat.zero_mul, Nat.add_zero, Int.natCast_zero] at sampled
  have cell : (patternArray high)[offset.val % 256]'(by rw [pattern_size]; exact Nat.mod_lt _ (by decide +kernel)) =
      high.val ^^^ (offset.val % 256 / 8) := by
    simp only [patternArray, List.getElem_toArray, List.getElem_ofFn]
  rw [cell] at sampled
  have residue : offset.val % 256 / 8 = offset.val / 8 % 32 := by omega
  simpa only [residue] using sampled

/-- The exact source templates prove the complete shift-5 overflow region. -/
theorem source_split_high_five_get (index : Fin 65536) :
    ((SourceCaptureTheta.columns[4]?).getD ({ blocks := #[] } : Column)).get? (393216 + index.val) =
      some ((index.val / 2048) ^^^ (index.val / 8 % 32)) := by
  have selected := getFromBlocks_window sourceColumn.blocks.toList 36 32 393216 index.val
    prefix_length (by change index.val < (window.map Block.length).sum; rw [window_length]; exact index.isLt)
  change getFromBlocks sourceColumn.blocks.toList (393216 + index.val) = _
  rw [selected]
  change getFromBlocks window index.val = _
  rw [uniform_blocks_get _ 2048 (by decide +kernel) window_lengths]
  have bound : index.val / 2048 < window.length := by rw [window_count]; omega
  have chosen : window[index.val / 2048]? = some (blockAt ⟨index.val / 2048, by omega⟩) := by
    simp only [blockAt, List.getElem?_eq_getElem bound, Option.getD_some]
  rw [chosen, Option.bind_some]
  have value := block_get ⟨index.val / 2048, by omega⟩ ⟨index.val % 2048, by omega⟩
  have low : index.val % 2048 / 8 % 32 = index.val / 8 % 32 := by omega
  simpa only [low] using value

/-- The stored source overflow equals its original native value. -/
theorem source_split_high_five_match (index : Fin 65536) :
    (((SourceCaptureTheta.columns[4]?).getD ({ blocks := #[] } : Column)).get? (393216 + index.val)).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.columns[4]).value (327680 + index.val) := by
  rw [source_split_high_five_get, Option.getD_some]
  have native := Airbender.Keccak.Split.Native.Fixed.Proofs.theta_fragment_high_value
    ⟨327680 + index.val, by change 327680 + index.val < 524288; have bound := index.isLt; omega⟩
  have shift : (327680 + index.val) / 65536 = 5 := by omega
  have high : (327680 + index.val) / 256 % 256 = index.val / 256 % 256 := by omega
  have low : (327680 + index.val) % 256 = index.val % 256 := by omega
  rw [shift, high, low] at native
  change _ = ((index.val / 256 % 256) ^^^ (index.val % 256)) / 8 at native
  rw [native]
  have split := Nat.xor_div_two_pow (a := index.val / 256 % 256) (b := index.val % 256) (n := 3)
  change _ / 8 = _ at split
  have hdiv : index.val / 256 % 256 / 8 = index.val / 2048 := by omega
  have ldiv : index.val % 256 / 8 = index.val / 8 % 32 := by omega
  simpa only [hdiv, ldiv] using split.symm

end Airbender.Setup.SourceCaptureThetaProofs
