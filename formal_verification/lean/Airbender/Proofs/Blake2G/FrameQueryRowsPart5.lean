import Airbender.Proofs.Arithmetic.ExpressionRows
import Airbender.Proofs.Blake2G.FrameQueryShapes

namespace Airbender.Blake2G.Proofs.FrameQueryShapes
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def entry15 {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    Vector (Expression (ZMod p)) 9 :=
  show Vector (Expression (ZMod p)) table.toRaw.arity from
  #v[Arithmetic.linearExpression (0) [(1, 63)],
      Arithmetic.linearExpression (0) [(-15728640, 23), (-15728640, 47), (2, 48), (-512, 49), (-15728640, 72), (2, 73), (-512, 75), (15728640, 77)],
      Arithmetic.linearExpression (0) [(1, 80)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem lookup15_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨15, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry15 table) := rfl

def values15 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.firstBMiddle[1], -15728640 * f.inputs[4] - 15728640 * f.firstDBytes[2] + 2 * f.firstDBytes[3] - 512 * f.cCarries[0] - 15728640 * f.secondDBytes[1] + 2 * f.secondDBytes[2] - 512 * f.cCarries[2] + 15728640 * f.secondCLow[0], f.secondBChunks[1], 0, 0, 0, 0, 0, 20]

theorem rawRow15 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry15 table).map (Expression.eval (Verification.environment f.assignment)) = values15 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [entry15, values15, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base] <;> ring)

def entry16 {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    Vector (Expression (ZMod p)) 9 :=
  show Vector (Expression (ZMod p)) table.toRaw.arity from
  #v[Arithmetic.linearExpression (0) [(16, 57), (1, 64)],
      Arithmetic.linearExpression (0) [(1, 78)],
      Arithmetic.linearExpression (0) [(1, 81)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (19) []]

theorem lookup16_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨16, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry16 table) := rfl

def values16 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.packedB[1], f.secondCLow[1], f.secondBChunks[2], 0, 0, 0, 0, 0, 19]

theorem rawRow16 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry16 table).map (Expression.eval (Verification.environment f.assignment)) = values16 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [entry16, values16, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base,
    combinedLow_as_value]

def entry17 {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    Vector (Expression (ZMod p)) 9 :=
  show Vector (Expression (ZMod p)) table.toRaw.arity from
  #v[Arithmetic.linearExpression (0) [(1, 58)],
      Arithmetic.linearExpression (0) [(-15728640, 24), (-15728640, 44), (2, 45), (-15728640, 49), (-512, 50), (2, 71), (-15728640, 74), (-15728640, 75), (-512, 76), (15728640, 78)],
      Arithmetic.linearExpression (0) [(1, 82)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem lookup17_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨17, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry17 table) := rfl

def values17 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.firstBMiddle[0], -15728640 * f.inputs[5] - 15728640 * f.firstDBytes[0] + 2 * f.firstDBytes[1] - 15728640 * f.cCarries[0] - 512 * f.cCarries[1] + 2 * f.secondDBytes[0] - 15728640 * f.secondDBytes[3] - 15728640 * f.cCarries[2] - 512 * f.cCarries[3] + 15728640 * f.secondCLow[1], f.secondBChunks[3], 0, 0, 0, 0, 0, 20]

theorem rawRow17 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry17 table).map (Expression.eval (Verification.environment f.assignment)) = values17 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [entry17, values17, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base] <;> ring)

end Airbender.Blake2G.Proofs.FrameQueryShapes
