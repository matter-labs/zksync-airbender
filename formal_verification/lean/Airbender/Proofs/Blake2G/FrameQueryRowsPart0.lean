import Airbender.Proofs.Arithmetic.ExpressionRows
import Airbender.Proofs.Blake2G.FrameQueryShapes

namespace Airbender.Blake2G.Proofs.FrameQueryShapes
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def values0 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.dBytes[0], f.firstABytes[0], f.firstDBytes[0], 0, 0, 0, 0, 0, 4]

theorem rawRow0 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry0 table).map (Expression.eval (Verification.environment f.assignment)) = values0 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [entry0, values0, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base]

def values1 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[-7864320 * f.inputs[6] + 7864320 * f.dBytes[0], -7864320 * f.inputs[0] - 7864320 * f.inputs[2] - 7864320 * f.inputs[8] - 256 * f.addCarries[0] + 7864320 * f.firstABytes[0], f.firstDBytes[1], 0, 0, 0, 0, 0, 4]

theorem rawRow1 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry1 table).map (Expression.eval (Verification.environment f.assignment)) = values1 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [entry1, values1, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base,
    carryLow_as_value] <;> ring)

def values2 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.dBytes[1], f.firstABytes[1], f.firstDBytes[2], 0, 0, 0, 0, 0, 4]

theorem rawRow2 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry2 table).map (Expression.eval (Verification.environment f.assignment)) = values2 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [entry2, values2, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base]

end Airbender.Blake2G.Proofs.FrameQueryShapes
