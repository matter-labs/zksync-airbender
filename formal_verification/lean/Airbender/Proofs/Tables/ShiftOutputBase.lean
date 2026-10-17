import Airbender.Proofs.Tables.ReferenceShiftRows
import Airbender.Proofs.Tables.ImportedBlocks

namespace Airbender.Verification.ShiftCertificate

def outputByte (lane key : Nat) : Nat :=
  let output := (shiftByteContribution (key / 65536) (key / 256 % 256)
    (key / 8 % 32) (key % 8)).toNat
  output / 256 ^ lane % 256

end Airbender.Verification.ShiftCertificate
