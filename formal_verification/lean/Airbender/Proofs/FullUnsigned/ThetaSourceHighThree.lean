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
private noncomputable def window : List Block := (sourceColumn.blocks.toList.drop 12).take 8
private noncomputable def blockAt (index : Fin 8) : Block := (window[index.val]?).getD (.affine 0 0 0)
private def patternArray (high : Fin 8) : Array Nat :=
  (List.ofFn fun index : Fin 256 => high.val ^^^ (index.val / 32)).toArray

private theorem prefix_length : ((sourceColumn.blocks.toList.take 12).map Block.length).sum = 262144 := by low_source_kernel_rfl
private theorem window_count : window.length = 8 := by low_source_kernel_rfl
private theorem window_length : (window.map Block.length).sum = 65536 := by low_source_kernel_rfl
private theorem window_lengths : ∀ block ∈ window, block.length = 8192 := by decide +kernel
private theorem shapes (index : Fin 8) : blockAt index = .periodic 32 0 (patternArray index) := by
  fin_cases index <;> low_source_kernel_rfl

private theorem pattern_size (high : Fin 8) : (patternArray high).size = 256 := by
  simp only [patternArray, List.size_toArray, List.length_ofFn]

private theorem block_get (high : Fin 8) (offset : Fin 8192) :
    (blockAt high).get? offset.val = some (high.val ^^^ (offset.val / 32 % 8)) := by
  rw [shapes]
  have sampled := periodic_get (patternArray high) 32 0 offset.val (by rw [pattern_size]; decide +kernel)
    (by rw [pattern_size]; exact offset.isLt)
  simp only [pattern_size, Nat.zero_mul, Nat.add_zero, Int.natCast_zero] at sampled
  have cell : (patternArray high)[offset.val % 256]'(by rw [pattern_size]; exact Nat.mod_lt _ (by decide +kernel)) =
      high.val ^^^ (offset.val % 256 / 32) := by
    simp only [patternArray, List.getElem_toArray, List.getElem_ofFn]
  rw [cell] at sampled
  have residue : offset.val % 256 / 32 = offset.val / 32 % 8 := by omega
  simpa only [residue] using sampled

/-- The exact source templates prove the complete shift-3 overflow region. -/
theorem source_split_high_three_get (index : Fin 65536) :
    ((SourceCaptureTheta.columns[4]?).getD ({ blocks := #[] } : Column)).get? (262144 + index.val) =
      some ((index.val / 8192) ^^^ (index.val / 32 % 8)) := by
  have selected := getFromBlocks_window sourceColumn.blocks.toList 12 8 262144 index.val
    prefix_length (by change index.val < (window.map Block.length).sum; rw [window_length]; exact index.isLt)
  change getFromBlocks sourceColumn.blocks.toList (262144 + index.val) = _
  rw [selected]
  change getFromBlocks window index.val = _
  rw [uniform_blocks_get _ 8192 (by decide +kernel) window_lengths]
  have bound : index.val / 8192 < window.length := by rw [window_count]; omega
  have chosen : window[index.val / 8192]? = some (blockAt ⟨index.val / 8192, by omega⟩) := by
    simp only [blockAt, List.getElem?_eq_getElem bound, Option.getD_some]
  rw [chosen, Option.bind_some]
  have value := block_get ⟨index.val / 8192, by omega⟩ ⟨index.val % 8192, by omega⟩
  have low : index.val % 8192 / 32 % 8 = index.val / 32 % 8 := by omega
  simpa only [low] using value

/-- The stored source overflow equals its original native value. -/
theorem source_split_high_three_match (index : Fin 65536) :
    (((SourceCaptureTheta.columns[4]?).getD ({ blocks := #[] } : Column)).get? (262144 + index.val)).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.columns[4]).value (196608 + index.val) := by
  rw [source_split_high_three_get, Option.getD_some]
  have native := Airbender.Keccak.Split.Native.Fixed.Proofs.theta_fragment_high_value
    ⟨196608 + index.val, by change 196608 + index.val < 524288; have bound := index.isLt; omega⟩
  have shift : (196608 + index.val) / 65536 = 3 := by omega
  have high : (196608 + index.val) / 256 % 256 = index.val / 256 % 256 := by omega
  have low : (196608 + index.val) % 256 = index.val % 256 := by omega
  rw [shift, high, low] at native
  change _ = ((index.val / 256 % 256) ^^^ (index.val % 256)) / 32 at native
  rw [native]
  have split := Nat.xor_div_two_pow (a := index.val / 256 % 256) (b := index.val % 256) (n := 5)
  change _ / 32 = _ at split
  have hdiv : index.val / 256 % 256 / 32 = index.val / 8192 := by omega
  have ldiv : index.val % 256 / 32 = index.val / 32 % 8 := by omega
  simpa only [hdiv, ldiv] using split.symm

end Airbender.Setup.SourceCaptureThetaProofs
