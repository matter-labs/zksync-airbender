import Airbender.Proofs.FullUnsigned.SourceBlockTrimming
import Airbender.Proofs.FullUnsigned.SourceScaledChunks
import Airbender.Proofs.FullUnsigned.SourceBlockWindows
import Airbender.Proofs.FullUnsigned.ThetaSourceLowZero
import Airbender.Proofs.Keccak.SplitThetaFragmentValues

namespace Airbender.Setup.SourceCaptureThetaProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private noncomputable def sourceColumn : Column := (SourceCaptureTheta.columns[4]?).getD ⟨#[]⟩
private noncomputable def window : List Block := (sourceColumn.blocks.toList.drop 0).take 5
private def model : List ChunkBlock := [.constant 1 0, .periodic 127 0 #[1, 0], .constant 2 1, .periodic 127 0 #[0, 1], .constant 1 0]
private def expected (index : Nat) : Nat := (index / 256) ^^^ (index % 2)
private theorem model_length : ((model.map ChunkBlock.compact).map Block.length).sum = 512 := by low_source_kernel_rfl
private theorem model_checked : checkBlockRows expected 0 (model.map ChunkBlock.compact) = true := by decide +kernel
private theorem prefix_length : ((sourceColumn.blocks.toList.take 0).map Block.length).sum = 0 := by low_source_kernel_rfl
private theorem window_length : (window.map Block.length).sum = 196672 := by low_source_kernel_rfl
private noncomputable def front : List Block := (model.take 4).map (ChunkBlock.expandBy 128)
private theorem front_length : (front.map Block.length).sum = 65408 := by low_source_kernel_rfl
private theorem source_shape : window = .affine 131200 0 0 ::
    ((model.drop 1 |>.take 3).map (ChunkBlock.expandBy 128) ++ [.affine 192 0 0]) := by low_source_kernel_rfl

private theorem source_window (index : Fin 65536) : sourceColumn.get? (131072 + index.val) =
    getFromBlocks (model.map (ChunkBlock.expandBy 128)) index.val := by
  have selected := getFromBlocks_window sourceColumn.blocks.toList 0 5 0 (131072 + index.val)
    prefix_length (by change 131072 + index.val < (window.map Block.length).sum; rw [window_length]; omega)
  simp only [Nat.zero_add] at selected
  change getFromBlocks sourceColumn.blocks.toList (131072 + index.val) = _
  rw [selected]
  change getFromBlocks window (131072 + index.val) = _
  rw [source_shape, skip_constant_head 131200 0 131072 index.val _ (by decide +kernel)]
  change getFromBlocks (front ++ [.affine (128 + 64) 0 0]) index.val = _
  rw [shorten_constant_tail front 128 64 0 index.val (by rw [front_length]; omega)]
  rfl

/-- Exact scaled source blocks prove this complete overflow region. -/
theorem source_split_high_one_get (index : Fin 65536) :
    ((SourceCaptureTheta.columns[4]?).getD ({ blocks := #[] } : Column)).get? (131072 + index.val) =
      some ((index.val / 32768) ^^^ (index.val / 128 % 2)) := by
  change sourceColumn.get? (131072 + index.val) = _
  rw [source_window, getFromBlocks_expandBy 128 (by decide +kernel)]
  have checked := checkBlockRows_sound expected (model.map ChunkBlock.compact) 0 (index.val / 128)
    model_checked (by rw [model_length]; omega)
  have high : index.val / 128 / 256 = index.val / 32768 := by omega
  simpa only [Nat.zero_add, expected, high] using checked

/-- The stored source overflow equals its complete native value. -/
theorem source_split_high_one_match (index : Fin 65536) :
    (((SourceCaptureTheta.columns[4]?).getD ({ blocks := #[] } : Column)).get? (131072 + index.val)).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.columns[4]).value (65536 + index.val) := by
  rw [source_split_high_one_get, Option.getD_some]
  have native := Airbender.Keccak.Split.Native.Fixed.Proofs.theta_fragment_high_value
    ⟨65536 + index.val, by change 65536 + index.val < 524288; have bound := index.isLt; omega⟩
  have shift : (65536 + index.val) / 65536 = 1 := by omega
  have high : (65536 + index.val) / 256 % 256 = index.val / 256 % 256 := by omega
  have low : (65536 + index.val) % 256 = index.val % 256 := by omega
  rw [shift, high, low] at native
  change _ = ((index.val / 256 % 256) ^^^ (index.val % 256)) / 128 at native
  rw [native]
  have split := Nat.xor_div_two_pow (a := index.val / 256 % 256) (b := index.val % 256) (n := 7)
  change _ / 128 = _ at split
  have hdiv : index.val / 256 % 256 / 128 = index.val / 32768 := by omega
  have ldiv : index.val % 256 / 128 = index.val / 128 % 2 := by omega
  simpa only [hdiv, ldiv] using split.symm

end Airbender.Setup.SourceCaptureThetaProofs
