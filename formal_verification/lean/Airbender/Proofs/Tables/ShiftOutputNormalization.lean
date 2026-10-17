import Airbender.Proofs.Tables.ShiftOutputNat

namespace Airbender.Verification.ShiftCertificate
set_option warningAsError true
set_option Elab.async false

def outputNatByte (lane key : Nat) : Nat :=
  contributionNat (key / 65536) (key / 256 % 256) (key / 8 % 32) (key % 8) /
    256 ^ lane % 256

/-- Normalize the reference once before checking the imported finite data. -/
theorem outputByte_normalized (lane : Nat) : outputByte lane = outputNatByte lane := by
  funext key
  simp only [outputByte, outputNatByte, contribution_toNat]

end Airbender.Verification.ShiftCertificate
