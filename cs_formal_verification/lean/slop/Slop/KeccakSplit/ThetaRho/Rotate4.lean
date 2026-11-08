module
public import Slop.KeccakSplit.ThetaRho.ByteLane
public import Human.Circuits.KeccakSplit.Call

@[expose] public section

/- The byte-fragment rotation is the 64-bit rotation, for the rho offsets of column 4. -/

namespace Airbender.Keccak.Split.ThetaRho.Proofs
open Airbender.Arithmetic
set_option warningAsError true
set_option maxRecDepth 65536

set_option maxHeartbeats 2400000 in
theorem rotate_column4 {bytes : Vector Nat 8}
    (bounds : ∀ digit : Fin 8, bytes[digit] < 256) (lane : Fin 5) :
    rotLeft64 (packByteLane bytes) (Call.rotations[4][lane]) =
      packByteLane ((Vector.finRange 8).map (rotatedLaneByte bytes (Call.rotations[4][lane]))) := by
  have h0 := bounds 0; have h1 := bounds 1; have h2 := bounds 2; have h3 := bounds 3
  have h4 := bounds 4; have h5 := bounds 5; have h6 := bounds 6; have h7 := bounds 7
  change bytes[(0 : Nat)] < 256 at h0
  change bytes[(1 : Nat)] < 256 at h1
  change bytes[(2 : Nat)] < 256 at h2
  change bytes[(3 : Nat)] < 256 at h3
  change bytes[(4 : Nat)] < 256 at h4
  change bytes[(5 : Nat)] < 256 at h5
  change bytes[(6 : Nat)] < 256 at h6
  change bytes[(7 : Nat)] < 256 at h7
  fin_cases lane <;>
    dsimp [Call.rotations, packByteLane, rotatedLaneByte, byteRotationSource, byteRotationPrevious,
      rotLeft64, rotRight64] <;>
    simp [rotatedLaneByte, byteRotationSource, byteRotationPrevious] <;> omega

end Airbender.Keccak.Split.ThetaRho.Proofs
