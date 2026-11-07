import Airbender.Proofs.Keccak.SplitThetaFragmentLow0
import Airbender.Proofs.Keccak.SplitThetaFragmentLow1
import Airbender.Proofs.Keccak.SplitThetaFragmentLow2
import Airbender.Proofs.Keccak.SplitThetaFragmentLow3
import Airbender.Proofs.Keccak.SplitThetaFragmentLow4
import Airbender.Proofs.Keccak.SplitThetaFragmentLow5
import Airbender.Proofs.Keccak.SplitThetaFragmentLow6
import Airbender.Proofs.Keccak.SplitThetaFragmentLow7
import Airbender.Proofs.Keccak.SplitThetaFragmentHigh0
import Airbender.Proofs.Keccak.SplitThetaFragmentHigh1
import Airbender.Proofs.Keccak.SplitThetaFragmentHigh2
import Airbender.Proofs.Keccak.SplitThetaFragmentHigh3
import Airbender.Proofs.Keccak.SplitThetaFragmentHigh4
import Airbender.Proofs.Keccak.SplitThetaFragmentHigh5
import Airbender.Proofs.Keccak.SplitThetaFragmentHigh6
import Airbender.Proofs.Keccak.SplitThetaFragmentHigh7

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup.LiteralTree
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false

/-- Select the checked low-fragment correspondence for the actual shift. -/
def thetaFragmentLowMap (shift : Fin 8) : XorFragmentMap :=
  ![thetaFragmentLowMap0, thetaFragmentLowMap1, thetaFragmentLowMap2, thetaFragmentLowMap3,
    thetaFragmentLowMap4, thetaFragmentLowMap5, thetaFragmentLowMap6, thetaFragmentLowMap7] shift

/-- Select the checked high-fragment correspondence for the actual shift. -/
def thetaFragmentHighMap (shift : Fin 8) : XorFragmentMap :=
  ![thetaFragmentHighMap0, thetaFragmentHighMap1, thetaFragmentHighMap2, thetaFragmentHighMap3,
    thetaFragmentHighMap4, thetaFragmentHighMap5, thetaFragmentHighMap6, thetaFragmentHighMap7] shift

/-- The low-fragment certificate covers every native shift. -/
theorem theta_fragment_low_certificate (shift : Fin 8) :
    XorFragmentRefines (thetaRhoXorSplit.columns[3]) (xorFragmentLow shift.val)
      (thetaFragmentLowMap shift) := by
  fin_cases shift
  · exact theta_fragment_low_certificate0
  · exact theta_fragment_low_certificate1
  · exact theta_fragment_low_certificate2
  · exact theta_fragment_low_certificate3
  · exact theta_fragment_low_certificate4
  · exact theta_fragment_low_certificate5
  · exact theta_fragment_low_certificate6
  · exact theta_fragment_low_certificate7

/-- The high-fragment certificate covers every native shift. -/
theorem theta_fragment_high_certificate (shift : Fin 8) :
    XorFragmentRefines (thetaRhoXorSplit.columns[4]) (xorFragmentHigh shift.val)
      (thetaFragmentHighMap shift) := by
  fin_cases shift
  · exact theta_fragment_high_certificate0
  · exact theta_fragment_high_certificate1
  · exact theta_fragment_high_certificate2
  · exact theta_fragment_high_certificate3
  · exact theta_fragment_high_certificate4
  · exact theta_fragment_high_certificate5
  · exact theta_fragment_high_certificate6
  · exact theta_fragment_high_certificate7

/-- Check the actual low-fragment root for all eight shifts. -/
theorem theta_fragment_low_roots : ∀ shift : Fin 8,
    (thetaRhoXorSplit.columns[3]).entry (thetaRhoXorSplit.columns[3]).root shift.val =
      (thetaFragmentLowMap shift).root := by
  decide +kernel

/-- Check the actual high-fragment root for all eight shifts. -/
theorem theta_fragment_high_roots : ∀ shift : Fin 8,
    (thetaRhoXorSplit.columns[4]).entry (thetaRhoXorSplit.columns[4]).root shift.val =
      (thetaFragmentHighMap shift).root := by
  decide +kernel

/-- Every actual low fragment is the selected shifted XOR byte. -/
theorem theta_fragment_low_value (row : Fin thetaRhoXorSplit.length) :
    (thetaRhoXorSplit.columns[3]).value row.val =
      ((row.val / 256 % 256) ^^^ (row.val % 256)) * 2 ^ (row.val / 65536) % 256 := by
  have bound : row.val < 524288 := row.isLt
  let shift : Fin 8 := ⟨row.val / 65536, by omega⟩
  have value := xor_fragment_value (theta_fragment_low_certificate shift) rfl row.val shift.val
    (by dsimp [shift]; omega) (theta_fragment_low_roots shift)
  rw [xor_byte_output_value] at value
  exact value

/-- Every actual high fragment is the selected XOR byte's overflow. -/
theorem theta_fragment_high_value (row : Fin thetaRhoXorSplit.length) :
    (thetaRhoXorSplit.columns[4]).value row.val =
      ((row.val / 256 % 256) ^^^ (row.val % 256)) / 2 ^ (8 - row.val / 65536) := by
  have bound : row.val < 524288 := row.isLt
  let shift : Fin 8 := ⟨row.val / 65536, by omega⟩
  have value := xor_fragment_value (theta_fragment_high_certificate shift) rfl row.val shift.val
    (by dsimp [shift]; omega) (theta_fragment_high_roots shift)
  rw [xor_byte_output_value] at value
  exact value

end Airbender.Keccak.Split.Native.Fixed.Proofs
