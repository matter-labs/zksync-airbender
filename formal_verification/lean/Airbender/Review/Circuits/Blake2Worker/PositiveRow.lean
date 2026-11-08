import Airbender.Review.Circuits.Blake2Worker.Processing

namespace Airbender.Blake2Worker.PositiveRow
abbrev F := ZMod mersenne31Modulus

/-- Explicit local worker-row fixture. All values are zero except multiplicity1,
    processing clock(3,0), and the43 timestamp borrows1. This supplies no source
    proof, initialized history, issued request, round schedule or Sail result. -/
def assignment (column : Nat) : F :=
  if column = 0 then 1 else if column = 740 then 3 else
  if 742 ≤ column ∧ column < 871 ∧ (column-742)%3 = 0 then 1 else 0

end Airbender.Blake2Worker.PositiveRow
