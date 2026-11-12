module
public import Slop.NonVacuous.KeccakSplitSpan.ThetaRho.Honest
public import Slop.NonVacuous.SpanTactics
public import Slop.KeccakSplit.ThetaRho.OpIndex

@[expose] public section

/-! The first ten theta+rho rotation equations (lanes 0 and 1, limbs 0 and 1 of lane 2) hold for
    the honest assignment: in each column the flags are 0 or 1 and the written limb unfolds at that column's rho. -/

namespace Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
open Arithmetic Keccak.Split Keccak.Split.SetupProofs

/-- The call's column. -/
theorem column_cases (x : RowInput) :
    x.call % 5 = 0 ∨ x.call % 5 = 1 ∨ x.call % 5 = 2 ∨ x.call % 5 = 3 ∨ x.call % 5 = 4 := by
  omega

/-- A theta+rho rotation equation in one column: the flags are 0 or 1 and the written limb unfolds at the column's
    rho. -/
scoped macro "rotation_column " h:ident : tactic => `(tactic| (
  simp only [Expression.eval, Verification.environment, honest_column, flag, out, outByte, $h:ident, rho,
    List.getD_cons_zero, List.getD_cons_succ, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.reduceEqDiff, ↓reduceIte, OfNat.ofNat_ne_zero, zero_ne_one, one_ne_zero]
  push_cast
  ring))

variable {p : Nat} [Fact p.Prime]

theorem rotation_3 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨3, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

theorem rotation_4 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨4, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

theorem rotation_5 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨5, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

theorem rotation_6 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨6, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

theorem rotation_7 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨7, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

theorem rotation_8 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨8, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

theorem rotation_9 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨9, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

theorem rotation_10 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨10, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

theorem rotation_11 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨11, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

theorem rotation_12 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨12, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

end Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
