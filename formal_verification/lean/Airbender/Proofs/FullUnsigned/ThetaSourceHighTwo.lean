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
private noncomputable def window : List Block := (sourceColumn.blocks.toList.drop 4).take 8
private def model : List ChunkBlock := [.constant 1 0, .periodic 63 0 #[1, 2, 3, 0], .constant 1 1, .constant 1 2, .constant 1 3, .periodic 64 0 #[1, 0, 3, 2], .periodic 64 0 #[2, 3, 0, 1], .periodic 64 0 #[3, 2, 1, 0]]
private def expected (index : Nat) : Nat := (index / 256) ^^^ (index % 4)
private theorem model_length : ((model.map ChunkBlock.compact).map Block.length).sum = 1024 := by low_source_kernel_rfl
private theorem model_checked : checkBlockRows expected 0 (model.map ChunkBlock.compact) = true := by decide +kernel
private theorem prefix_length : ((sourceColumn.blocks.toList.take 4).map Block.length).sum = 196480 := by low_source_kernel_rfl
private theorem window_length : (window.map Block.length).sum = 65664 := by low_source_kernel_rfl
private theorem source_shape : window = .affine 192 0 0 ::
    ((model.drop 1).map (ChunkBlock.expandBy 64)) := by low_source_kernel_rfl

private theorem source_window (index : Fin 65536) : sourceColumn.get? (196608 + index.val) =
    getFromBlocks (model.map (ChunkBlock.expandBy 64)) index.val := by
  have selected := getFromBlocks_window sourceColumn.blocks.toList 4 8 196480 (128 + index.val)
    prefix_length (by change 128 + index.val < (window.map Block.length).sum; rw [window_length]; omega)
  have offset : 196480 + (128 + index.val) = 196608 + index.val := by omega
  rw [offset] at selected
  change getFromBlocks sourceColumn.blocks.toList (196608 + index.val) = _
  rw [selected]
  change getFromBlocks window (128 + index.val) = _
  rw [source_shape, skip_constant_head 192 0 128 index.val _ (by decide +kernel)]
  rfl

/-- Exact scaled source blocks prove this complete overflow region. -/
theorem source_split_high_two_get (index : Fin 65536) :
    ((SourceCaptureTheta.columns[4]?).getD ({ blocks := #[] } : Column)).get? (196608 + index.val) =
      some ((index.val / 16384) ^^^ (index.val / 64 % 4)) := by
  change sourceColumn.get? (196608 + index.val) = _
  rw [source_window, getFromBlocks_expandBy 64 (by decide +kernel)]
  have checked := checkBlockRows_sound expected (model.map ChunkBlock.compact) 0 (index.val / 64)
    model_checked (by rw [model_length]; omega)
  have high : index.val / 64 / 256 = index.val / 16384 := by omega
  simpa only [Nat.zero_add, expected, high] using checked

/-- The stored source overflow equals its complete native value. -/
theorem source_split_high_two_match (index : Fin 65536) :
    (((SourceCaptureTheta.columns[4]?).getD ({ blocks := #[] } : Column)).get? (196608 + index.val)).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.columns[4]).value (131072 + index.val) := by
  rw [source_split_high_two_get, Option.getD_some]
  have native := Airbender.Keccak.Split.Native.Fixed.Proofs.theta_fragment_high_value
    ⟨131072 + index.val, by change 131072 + index.val < 524288; have bound := index.isLt; omega⟩
  have shift : (131072 + index.val) / 65536 = 2 := by omega
  have high : (131072 + index.val) / 256 % 256 = index.val / 256 % 256 := by omega
  have low : (131072 + index.val) % 256 = index.val % 256 := by omega
  rw [shift, high, low] at native
  change _ = ((index.val / 256 % 256) ^^^ (index.val % 256)) / 64 at native
  rw [native]
  have split := Nat.xor_div_two_pow (a := index.val / 256 % 256) (b := index.val % 256) (n := 6)
  change _ / 64 = _ at split
  have hdiv : index.val / 256 % 256 / 64 = index.val / 16384 := by omega
  have ldiv : index.val % 256 / 64 = index.val / 64 % 4 := by omega
  simpa only [hdiv, ldiv] using split.symm

end Airbender.Setup.SourceCaptureThetaProofs
