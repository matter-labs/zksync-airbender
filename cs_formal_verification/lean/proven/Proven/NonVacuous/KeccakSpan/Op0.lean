module
public import Proven.NonVacuous.KeccakSpan.Route

@[expose] public section

/-! The thirteen routing assertions of the first operation (imported assertions 19 to 31). -/

namespace Airbender.NonVacuous.KeccakSpan

variable {p : Nat} [Fact p.Prime]

theorem op0_19 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 19 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨19, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op0

theorem op0_20 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 20 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨20, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op0

theorem op0_21 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 21 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨21, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op0

theorem op0_22 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 22 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨22, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op0

theorem op0_23 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 23 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨23, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op0

theorem op0_24 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 24 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨24, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op0

theorem op0_25 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 25 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨25, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op0

theorem op0_26 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 26 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨26, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op0

theorem op0_27 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 27 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨27, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op0

theorem op0_28 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 28 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨28, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op0

theorem op0_29 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 29 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨29, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op0

theorem op0_30 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 30 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨30, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op0

theorem op0_31 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 31 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨31, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op0

end Airbender.NonVacuous.KeccakSpan
