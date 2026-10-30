import Airbender.Data.Setup.Keccak.ThetaRhoXorSplit
import Airbender.Proofs.Keccak.SplitThetaXorValues

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup.LiteralTree
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false

/-- The actual split keys retain their complete native depths and roots. -/
theorem theta_split_key_shapes :
    ((thetaRhoXorSplit.columns[0]).depth = 5 ∧ (thetaRhoXorSplit.columns[0]).root = 20) ∧
      ((thetaRhoXorSplit.columns[1]).depth = 5 ∧ (thetaRhoXorSplit.columns[1]).root = 273) ∧
      ((thetaRhoXorSplit.columns[2]).depth = 5 ∧ (thetaRhoXorSplit.columns[2]).root = 8) := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Check every actual first-key transition below its shift root. -/
theorem theta_split_first_entries : ∀ (node : Fin 18) (digit : Fin 16),
    (thetaRhoXorSplit.columns[0]).entry node.val digit.val = xorByteLowEntry node.val digit.val := by
  decide +kernel

/-- Check every actual second-key transition below its shift root. -/
theorem theta_split_second_entries : ∀ (node : Fin 273) (digit : Fin 16),
    (thetaRhoXorSplit.columns[1]).entry node.val digit.val = xorByteHighEntry node.val digit.val := by
  decide +kernel

/-- Check all actual key roots on the complete eight-shift domain. -/
theorem theta_split_key_roots : ∀ shift : Fin 8,
    (thetaRhoXorSplit.columns[0]).entry 20 shift.val = 17 ∧
      (thetaRhoXorSplit.columns[1]).entry 273 shift.val = 272 ∧
      (thetaRhoXorSplit.columns[2]).entry 8 shift.val = shift.val := by
  decide +kernel

/-- Every actual shift node preserves its selected value. -/
theorem theta_split_shift_entries : ∀ (shift : Fin 8) (digit : Fin 16),
    (thetaRhoXorSplit.columns[2]).entry shift.val digit.val = shift.val := by
  decide +kernel

/-- All actual physical padding columns retain their complete zero trees. -/
theorem theta_split_padding_shapes : ∀ column : Fin 3,
    (thetaRhoXorSplit.columns[5 + column.val]).depth = 5 ∧
      (thetaRhoXorSplit.columns[5 + column.val]).root = 0 := by
  decide +kernel

/-- Every actual padding transition stays zero. -/
theorem theta_split_padding_entries : ∀ (column : Fin 3) (digit : Fin 16),
    (thetaRhoXorSplit.columns[5 + column.val]).entry 0 digit.val = 0 := by
  decide +kernel

/-- The actual discriminator retains its complete native depth and root. -/
theorem theta_split_tag_shape :
    (thetaRhoXorSplit.columns[8]).depth = 5 ∧ (thetaRhoXorSplit.columns[8]).root = 5 := by
  exact ⟨rfl, rfl⟩

/-- Check the actual discriminator root on every native shift. -/
theorem theta_split_tag_roots : ∀ shift : Fin 8,
    (thetaRhoXorSplit.columns[8]).entry 5 shift.val = 3 := by
  decide +kernel

/-- Check every actual discriminator transition below its shift root. -/
theorem theta_split_tag_entries : ∀ (node : Fin 4) (digit : Fin 16),
    (thetaRhoXorSplit.columns[8]).entry node.val digit.val =
      if node.val = 0 then 58 else node.val - 1 := by
  decide +kernel

end Airbender.Keccak.Split.Native.Fixed.Proofs
