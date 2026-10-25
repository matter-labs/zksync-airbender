import GKRProtocol.DenseZeroTag
import GKRProtocol.ColumnSlices
import GKRProtocol.MaterializedNative.UnifiedUncached

namespace Airbender.Compiler.ROMNative.UnifiedTag
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

abbrev nativeSetup := Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model

def segments : List (Nat × Nat) := [(131072, 1), (65536, 2), (256, 3), (65536, 5), (65536, 8), (262144, 9), (1048576, 34), (65536, 47), (65536, 48), (65536, 49), (65536, 50), (128, 51), (65536, 52), (65536, 53), (65536, 54), (1048576, 46), (5242495, 0)]

theorem shape : nativeSetup.imported.data.columns[9].blocks.toList =
    .dense #[0] :: segments.map (fun entry => Setup.Block.affine entry.1 entry.2 0) := by rfl

theorem tag_value (row : Fin nativeSetup.imported.data.length) :
    nativeSetup.value row (.generic 9) = if row.val < 1 then 0 else constantTagValue segments (row.val - 1) := by
  rw [nativeSetup.generic_cell_value row (⟨9, by decide⟩ : Fin 10)]
  simp only [show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  change (((Setup.getFromBlocks nativeSetup.imported.data.columns[9].blocks.toList row.val).getD 0) : Source.BaseField) = _
  rw [shape]
  exact dense_zero_tag segments row.val

theorem rom_region (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 9) = 34) :
    590081 ≤ row.val ∧ row.val < 1638657 := by
  rw [tag_value] at selected
  by_cases leading : row.val < 1
  · rw [if_pos leading] at selected
    exact False.elim ((by decide +kernel : (0 : Source.BaseField) ≠ 34) selected)
  · rw [if_neg leading] at selected
    have step0 := constant_tag_skip 131072 1 (segments.drop 1) (row.val - 1) 34
      (by decide +kernel) selected
    have step1 := constant_tag_skip 65536 2 (segments.drop 2) ((row.val - 1) - 131072) 34
      (by decide +kernel) step0.2
    have step2 := constant_tag_skip 256 3 (segments.drop 3) (((row.val - 1) - 131072) - 65536) 34
      (by decide +kernel) step1.2
    have step3 := constant_tag_skip 65536 5 (segments.drop 4) ((((row.val - 1) - 131072) - 65536) - 256) 34
      (by decide +kernel) step2.2
    have step4 := constant_tag_skip 65536 8 (segments.drop 5) (((((row.val - 1) - 131072) - 65536) - 256) - 65536) 34
      (by decide +kernel) step3.2
    have step5 := constant_tag_skip 262144 9 (segments.drop 6) ((((((row.val - 1) - 131072) - 65536) - 256) - 65536) - 65536) 34
      (by decide +kernel) step4.2
    have inside := constant_tag_head_bounded 1048576 34 (segments.drop 7) (((((((row.val - 1) - 131072) - 65536) - 256) - 65536) - 65536) - 262144) 34
      (by decide +kernel) (by decide +kernel) step5.2
    omega

end Airbender.Compiler.ROMNative.UnifiedTag
