module
public import Proven.NonVacuous.KeccakSplitSpan.ThetaRho.RotationA

@[expose] public section

/-! The last ten theta+rho rotation equations hold for the honest assignment (`RotationA.lean`). -/

namespace Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
open Arithmetic Keccak.Split Keccak.Split.SetupProofs

variable {p : Nat} [Fact p.Prime]

theorem rotation_13 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨13, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

theorem rotation_14 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨14, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

theorem rotation_15 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨15, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

theorem rotation_16 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨16, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

theorem rotation_17 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨17, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

theorem rotation_18 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨18, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

theorem rotation_19 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨19, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

theorem rotation_20 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨20, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

theorem rotation_21 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨21, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

theorem rotation_22 (x : RowInput) (setup : Table (ZMod p) (fields 9)) :
    ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨22, by
      have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
      omega⟩).eval (Verification.environment (assignment x)) = 0 := by
  op_index
  rcases column_cases x with c | c | c | c | c <;> rotation_column c

end Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
