import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Helpers.Properties
import Mathlib.Tactic.IntervalCases
import Airbender.Proofs.Blake2G.FrameQueryEntries
import Airbender.Proofs.Blake2G.FrameNormalization
import Airbender.Proofs.Arithmetic.FieldSliceNormalization
import Airbender.Proofs.Blake2G.SerializedField

namespace Airbender.Blake2G.Proofs.FrameQueryShapes
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000





theorem row0 {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry0 table).map (Expression.eval (Verification.environment f.assignment)) =
      #v[f.dBytes[0], f.firstABytes[0], f.firstDBytes[0], 0, 0, 0, 0, 0, 4] := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [entry0, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base]

theorem row1 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry1 table).map (Expression.eval (Verification.environment f.assignment)) =
      #v[(-7864320 : ZMod p) * (f.inputs[6] - f.dBytes[0]),
         (-7864320 : ZMod p) * (f.inputs[0] + f.inputs[2] + f.inputs[8] -
           65536 * f.addCarries[0] - f.firstABytes[0]),
         f.firstDBytes[1], 0, 0, 0, 0, 0, 4] := by
  have inverse := inverse256 compatible
  have scale : (-7864320 : ZMod p) * 65536 = 256 := by
    linear_combination 256 * inverse
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [entry1, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base,
    carryLow_as_value]
  all_goals ring_nf
  all_goals linear_combination f.addCarries[0] * scale

theorem row2 {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry2 table).map (Expression.eval (Verification.environment f.assignment)) =
      #v[f.dBytes[1], f.firstABytes[1], f.firstDBytes[2], 0, 0, 0, 0, 0, 4] := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [entry2, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base]

end Airbender.Blake2G.Proofs.FrameQueryShapes
