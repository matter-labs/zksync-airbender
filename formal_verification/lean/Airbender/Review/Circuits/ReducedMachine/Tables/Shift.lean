import Airbender.Review.Circuits.ReducedMachine.Tables.Native

namespace Airbender.ReducedMachine.NativeFixed

/-- Native sign-fill key: input sign, arithmetic-shift flag, then five-bit amount.
    Shift zero has an explicit zero filler in the original Rust. -/
def signFillMask (key : Nat) : Nat :=
  if key % 4 = 3 ∧ key / 4 ≠ 0 then 4294967296 - 2 ^ (32 - key / 4) else 0

def signFillOutputs (key : Nat) : Vector Nat 2 :=
  #v[signFillMask key % 65536,signFillMask key / 65536]

end Airbender.ReducedMachine.NativeFixed
