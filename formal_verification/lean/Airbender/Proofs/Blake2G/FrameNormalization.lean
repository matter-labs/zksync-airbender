import Airbender.Proofs.Blake2G.Frame

namespace Airbender.Blake2G.Proofs
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- Recompose arithmetic carries before substituting a native layout. This
    keeps layout checks independent of the quotient/remainder encoding. -/
def Frame.normalizedAssignment {p : Nat} (f : Frame p) (column : Nat) : ZMod p :=
  match column with
  | 17 => f.inputs[0] + f.inputs[2] + f.inputs[8] - 65536 * f.addCarries[0] +
      f.packedB[0] + 128 * f.firstBMiddle[1] + f.inputs[10] - 65536 * f.addCarries[2]
  | 18 => f.inputs[1] + f.inputs[3] + f.inputs[9] + f.addCarries[0] -
      65536 * f.addCarries[1] + f.packedB[1] + 128 * f.firstBMiddle[0] +
      f.inputs[11] + f.addCarries[2] - 65536 * f.addCarries[3]
  | 21 => f.secondBChunks[1] + 512 * f.secondBChunks[2]
  | 22 => f.secondBChunks[3] + 512 * f.secondBChunks[0]
  | 25 => f.inputs[4] + f.firstDBytes[2] + 256 * f.firstDBytes[3] -
      65536 * f.cCarries[0] + f.secondDBytes[1] + 256 * f.secondDBytes[2] -
      65536 * f.cCarries[2]
  | 26 => f.inputs[5] + f.firstDBytes[0] + 256 * f.firstDBytes[1] +
      f.cCarries[0] - 65536 * f.cCarries[1] + f.secondDBytes[3] +
      256 * f.secondDBytes[0] + f.cCarries[2] - 65536 * f.cCarries[3]
  | 29 => f.secondDBytes[1] + 256 * f.secondDBytes[2]
  | 30 => f.secondDBytes[3] + 256 * f.secondDBytes[0]
  | n => f.base n

theorem Frame.assignment_eq_normalized {p : Nat} [Fact p.Prime] (f : Frame p) :
    f.assignment = f.normalizedAssignment := by
  funext column
  by_cases aLow : column = 17
  · subst column
    simp only [Frame.assignment, assemble, secondAlo, firstAlo, Frame.base,
      Frame.normalizedAssignment]
    linear_combination -65536 * carry_recompose f.addCarries[0] -
      65536 * carry_recompose f.addCarries[2] + combined_recompose f.packedB[0]
  by_cases aHigh : column = 18
  · subst column
    simp only [Frame.assignment, assemble, secondAhi, firstAhi, Frame.base,
      Frame.normalizedAssignment]
    linear_combination carry_recompose f.addCarries[0] -
      65536 * carry_recompose f.addCarries[1] + carry_recompose f.addCarries[2] -
      65536 * carry_recompose f.addCarries[3] + combined_recompose f.packedB[1]
  by_cases bLow : column = 21
  · subst column; rfl
  by_cases bHigh : column = 22
  · subst column; rfl
  by_cases cLow : column = 25
  · subst column; rfl
  by_cases cHigh : column = 26
  · subst column; rfl
  by_cases dLow : column = 29
  · subst column; rfl
  by_cases dHigh : column = 30
  · subst column; rfl
  simp [Frame.assignment, assemble, Frame.normalizedAssignment,
         ]

end Airbender.Blake2G.Proofs
