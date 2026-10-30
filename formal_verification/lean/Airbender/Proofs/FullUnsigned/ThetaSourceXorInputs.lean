import Airbender.Proofs.FullUnsigned.SourceFirstBlocks
import Airbender.Proofs.FullUnsigned.Source.Theta
import Airbender.Proofs.Keccak.SplitThetaXorValues
import Airbender.Proofs.Tables.PeriodicColumns

namespace Airbender.Setup.SourceCaptureThetaProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
-- Eight source fields use their first retained block on this 65,536-row region.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def sourceField (column : Fin 8) : Fin 9 :=
  ⟨if column.val < 2 then column.val else column.val + 1, by split <;> omega⟩

private def firstBlock (column : Fin 8) : Block :=
  match column.val with
  | 0 => .periodic 256 1 (Array.replicate 256 0)
  | 1 => .periodic 256 0 (Array.range 256)
  | 2 => .affine 65537 0 0
  | 3 => .affine 131200 0 0
  | 4 => .affine 589827 0 0
  | 5 => .affine 589828 0 0
  | 6 => .affine 589829 0 0
  | _ => .affine 65536 4 0

private theorem first_shape (column : Fin 8) :
    (((SourceCaptureTheta.columns[(sourceField column).val]?).getD ({ blocks := #[] } : Column)).blocks.toList).head? =
      some (firstBlock column) := by
  fin_cases column <;> setup_source_rfl

private theorem first_length : ∀ column : Fin 8, 65536 ≤ (firstBlock column).length := by decide +kernel

private theorem source_first_get (column : Fin 8) (index : Fin 65536) :
    ((SourceCaptureTheta.columns[(sourceField column).val]?).getD ({ blocks := #[] } : Column)).get? index.val =
      (firstBlock column).get? index.val := by
  exact getFromBlocks_first _ _ _ (first_shape column) (lt_of_lt_of_le index.isLt (first_length column))

/-- The first source key is the high byte of its row coordinate. -/
theorem source_xor_high_get (index : Fin 65536) :
    ((SourceCaptureTheta.columns[0]?).getD ({ blocks := #[] } : Column)).get? index.val = some (index.val / 256) := by
  have selected := source_first_get (⟨0, by decide +kernel⟩ : Fin 8) index
  change ((SourceCaptureTheta.columns[0]?).getD ({ blocks := #[] } : Column)).get? index.val =
    (Block.periodic 256 1 (Array.replicate 256 0)).get? index.val at selected
  have value := periodic_get (Array.replicate 256 0) 256 1 index.val (by simp)
    (by simpa only [Array.size_replicate] using index.isLt)
  exact selected.trans (by
    simpa only [Array.size_replicate, Array.getElem_replicate, Nat.zero_add, Nat.one_mul, Int.natCast_one] using value)

/-- The second source key is the low byte of its row coordinate. -/
theorem source_xor_low_get (index : Fin 65536) :
    ((SourceCaptureTheta.columns[1]?).getD ({ blocks := #[] } : Column)).get? index.val = some (index.val % 256) := by
  have selected := source_first_get (⟨1, by decide +kernel⟩ : Fin 8) index
  change ((SourceCaptureTheta.columns[1]?).getD ({ blocks := #[] } : Column)).get? index.val =
    (Block.periodic 256 0 (Array.range 256)).get? index.val at selected
  have value := periodic_get (Array.range 256) 256 0 index.val (by simp)
    (by simpa only [Array.size_range] using index.isLt)
  exact selected.trans (by
    simpa only [Array.size_range, Array.getElem_range, Nat.zero_mul, Nat.add_zero, Int.natCast_zero] using value)

/-- All five unused source fields stay zero throughout the byte-XOR region. -/
theorem source_xor_padding_get (column : Fin 5) (index : Fin 65536) :
    ((SourceCaptureTheta.columns[3 + column.val]?).getD ({ blocks := #[] } : Column)).get? index.val = some 0 := by
  fin_cases column
  · have selected := source_first_get (⟨2, by decide +kernel⟩ : Fin 8) index
    change ((SourceCaptureTheta.columns[3]?).getD ({ blocks := #[] } : Column)).get? index.val =
      (Block.affine 65537 0 0).get? index.val at selected
    exact selected.trans (constant_affine_get _ _ _ (by have bound := index.isLt; omega))
  · have selected := source_first_get (⟨3, by decide +kernel⟩ : Fin 8) index
    change ((SourceCaptureTheta.columns[4]?).getD ({ blocks := #[] } : Column)).get? index.val =
      (Block.affine 131200 0 0).get? index.val at selected
    exact selected.trans (constant_affine_get _ _ _ (by have bound := index.isLt; omega))
  · have selected := source_first_get (⟨4, by decide +kernel⟩ : Fin 8) index
    change ((SourceCaptureTheta.columns[5]?).getD ({ blocks := #[] } : Column)).get? index.val =
      (Block.affine 589827 0 0).get? index.val at selected
    exact selected.trans (constant_affine_get _ _ _ (by have bound := index.isLt; omega))
  · have selected := source_first_get (⟨5, by decide +kernel⟩ : Fin 8) index
    change ((SourceCaptureTheta.columns[6]?).getD ({ blocks := #[] } : Column)).get? index.val =
      (Block.affine 589828 0 0).get? index.val at selected
    exact selected.trans (constant_affine_get _ _ _ (by have bound := index.isLt; omega))
  · have selected := source_first_get (⟨6, by decide +kernel⟩ : Fin 8) index
    change ((SourceCaptureTheta.columns[7]?).getD ({ blocks := #[] } : Column)).get? index.val =
      (Block.affine 589829 0 0).get? index.val at selected
    exact selected.trans (constant_affine_get _ _ _ (by have bound := index.isLt; omega))

/-- The source discriminator is the original byte-XOR table tag. -/
theorem source_xor_tag_get (index : Fin 65536) :
    ((SourceCaptureTheta.columns[8]?).getD ({ blocks := #[] } : Column)).get? index.val = some 4 := by
  exact (source_first_get (⟨7, by decide +kernel⟩ : Fin 8) index).trans
    (constant_affine_get _ _ _ index.isLt)

/-- Both source keys equal their original native literal-tree keys. -/
theorem source_xor_keys_match (column : Fin 2) (index : Fin 65536) :
    (((SourceCaptureTheta.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? index.val).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXor.columns[column.val]).value index.val := by
  fin_cases column
  · rw [source_xor_high_get, Option.getD_some, Airbender.Keccak.Split.Native.Fixed.Proofs.xor_byte_high_value]
    have bound : index.val / 256 < 256 := by omega
    rw [Nat.mod_eq_of_lt bound]
  · rw [source_xor_low_get, Option.getD_some, Airbender.Keccak.Split.Native.Fixed.Proofs.xor_byte_low_value]

end Airbender.Setup.SourceCaptureThetaProofs
