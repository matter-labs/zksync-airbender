module
public import Slop.KeccakSplit.ThetaRho.Rotate0
public import Slop.KeccakSplit.ThetaRho.Rotate1
public import Slop.KeccakSplit.ThetaRho.Rotate2
public import Slop.KeccakSplit.ThetaRho.Rotate3
public import Slop.KeccakSplit.ThetaRho.Rotate4

@[expose] public section

namespace Airbender.Keccak.Split.ThetaRho.Proofs
open Airbender.Arithmetic
set_option warningAsError true

/-- The byte-fragment rotation is the 64-bit rotation for every rho offset. -/
theorem rotate_rho {bytes : Vector Nat 8} (bounds : ∀ digit : Fin 8, bytes[digit] < 256)
    (column lane : Fin 5) :
    rotLeft64 (packByteLane bytes) (Call.rotations[column][lane]) =
      packByteLane ((Vector.finRange 8).map (rotatedLaneByte bytes (Call.rotations[column][lane]))) := by
  fin_cases column
  · exact rotate_column0 bounds lane
  · exact rotate_column1 bounds lane
  · exact rotate_column2 bounds lane
  · exact rotate_column3 bounds lane
  · exact rotate_column4 bounds lane

end Airbender.Keccak.Split.ThetaRho.Proofs
