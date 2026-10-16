import Airbender.Proofs.Keccak.RotationCertificate
import Mathlib.Tactic.FinCases

namespace Airbender.Keccak.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/-- The imported high rotation piece for every native shift and word. -/
theorem rotation_high_get (shift : Fin 16) (word : Fin 65536) :
    rotationData.columns[1].get? (65536 * shift.val + word.val) =
      some (word.val / 2 ^ (16 - shift.val)) := by
  have hs := shift.isLt
  have hw := word.isLt
  have bound : 65536 * shift.val + word.val < 1048576 := by omega
  have quotient : (65536 * shift.val + word.val) / 65536 = shift.val := by omega
  have residue : (65536 * shift.val + word.val) % 65536 = word.val := by omega
  have result := rotation_high_column (65536 * shift.val + word.val) bound
  simpa only [rotationHigh, quotient, residue] using result

/-- The imported low rotation piece for every native shift and word. -/
theorem rotation_low_get (shift : Fin 16) (word : Fin 65536) :
    rotationData.columns[2].get? (65536 * shift.val + word.val) =
      some ((word.val * 2 ^ shift.val) % 65536) := by
  have hs := shift.isLt
  have hw := word.isLt
  have bound : 65536 * shift.val + word.val < 1048576 := by omega
  have quotient : (65536 * shift.val + word.val) / 65536 = shift.val := by omega
  have residue : (65536 * shift.val + word.val) % 65536 = word.val := by omega
  have result := rotation_low_column (65536 * shift.val + word.val) bound
  simpa only [rotationLow, quotient, residue] using result

end Airbender.Keccak.Proofs
