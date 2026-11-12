module
public import Proven.NonVacuous.KeccakSpan.Route

@[expose] public section

/-! The thirteen routing assertions of the second operation (imported assertions 32 to 44). -/

namespace Airbender.NonVacuous.KeccakSpan

variable {p : Nat} [Fact p.Prime]

theorem op1_32 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 32 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨32, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op1

theorem op1_33 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 33 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨33, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op1

theorem op1_34 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 34 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨34, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op1

theorem op1_35 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 35 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨35, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op1

theorem op1_36 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 36 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨36, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op1

theorem op1_37 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 37 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨37, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op1

theorem op1_38 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 38 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨38, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op1

theorem op1_39 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 39 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨39, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op1

theorem op1_40 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 40 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨40, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op1

theorem op1_41 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 41 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨41, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op1

theorem op1_42 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 42 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨42, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op1

theorem op1_43 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 43 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨43, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op1

theorem op1_44 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 44 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨44, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op1

end Airbender.NonVacuous.KeccakSpan
