module
public import Proven.NonVacuous.KeccakSpan.Route

@[expose] public section

/-! The thirteen routing assertions of the third operation (imported assertions 45 to 57). -/

namespace Airbender.NonVacuous.KeccakSpan

variable {p : Nat} [Fact p.Prime]

theorem op2_45 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 45 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨45, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op2

theorem op2_46 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 46 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨46, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op2

theorem op2_47 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 47 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨47, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op2

theorem op2_48 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 48 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨48, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op2

theorem op2_49 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 49 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨49, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op2

theorem op2_50 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 50 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨50, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op2

theorem op2_51 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 51 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨51, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op2

theorem op2_52 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 52 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨52, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op2

theorem op2_53 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 53 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨53, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op2

theorem op2_54 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 54 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨54, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op2

theorem op2_55 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 55 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨55, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op2

theorem op2_56 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 56 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨56, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op2

theorem op2_57 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 57 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨57, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op2

end Airbender.NonVacuous.KeccakSpan
