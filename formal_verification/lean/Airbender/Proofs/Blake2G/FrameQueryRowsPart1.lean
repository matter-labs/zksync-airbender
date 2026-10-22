import Airbender.Proofs.Arithmetic.ExpressionRows
import Airbender.Proofs.Blake2G.FrameQueryShapes

namespace Airbender.Blake2G.Proofs.FrameQueryShapes
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def entry3 {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    Vector (Expression (ZMod p)) 9 :=
  show Vector (Expression (ZMod p)) table.toRaw.arity from
  #v[Arithmetic.linearExpression (0) [(-7864320, 28), (7864320, 46)],
      Arithmetic.linearExpression (0) [(-7864320, 16), (-7864320, 20), (-7864320, 34), (-7864320, 37), (-15728640, 38), (-256, 39), (-512, 40), (7864320, 42)],
      Arithmetic.linearExpression (0) [(1, 48)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem lookup3_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨3, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry3 table) := rfl

def values3 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[-7864320 * f.inputs[7] + 7864320 * f.dBytes[1], -7864320 * f.inputs[1] - 7864320 * f.inputs[3] - 7864320 * f.inputs[9] - 7864320 * f.addCarries[0] - 256 * f.addCarries[1] + 7864320 * f.firstABytes[1], f.firstDBytes[3], 0, 0, 0, 0, 0, 4]

theorem rawRow3 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry3 table).map (Expression.eval (Verification.environment f.assignment)) = values3 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [entry3, values3, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base,
    carryLow_as_value] <;> ring)

def entry4 {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    Vector (Expression (ZMod p)) 9 :=
  show Vector (Expression (ZMod p)) table.toRaw.arity from
  #v[Arithmetic.linearExpression (0) [(1, 55)],
      Arithmetic.linearExpression (0) [(1, 51)],
      Arithmetic.linearExpression (0) [(1, 57)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (17) []]

theorem lookup4_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨4, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry4 table) := rfl

def values4 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.bLow[0], f.cLow[0], (combinedHigh f.packedB[1]), 0, 0, 0, 0, 0, 17]

theorem rawRow4 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry4 table).map (Expression.eval (Verification.environment f.assignment)) = values4 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [entry4, values4, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base]

def entry5 {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    Vector (Expression (ZMod p)) 9 :=
  show Vector (Expression (ZMod p)) table.toRaw.arity from
  #v[Arithmetic.linearExpression (0) [(1, 56)],
      Arithmetic.linearExpression (0) [(1, 52)],
      Arithmetic.linearExpression (0) [(1, 58)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem lookup5_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨5, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry5 table) := rfl

def values5 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.bMiddle[0], f.cMiddle[0], f.firstBMiddle[0], 0, 0, 0, 0, 0, 20]

theorem rawRow5 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry5 table).map (Expression.eval (Verification.environment f.assignment)) = values5 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [entry5, values5, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base]

end Airbender.Blake2G.Proofs.FrameQueryShapes
