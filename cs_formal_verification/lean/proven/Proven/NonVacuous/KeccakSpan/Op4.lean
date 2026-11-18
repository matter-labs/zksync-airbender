module
public import Proven.NonVacuous.KeccakSpan.Route

@[expose] public section

/-! The thirteen routing assertions of the fifth operation (imported assertions 71 to 83). -/

namespace Airbender.NonVacuous.KeccakSpan

variable {p : Nat} [Fact p.Prime]

theorem op4_71 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 71 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨71, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op4

theorem op4_72 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 72 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨72, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op4

theorem op4_73 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 73 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨73, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op4

theorem op4_74 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 74 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨74, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op4

theorem op4_75 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 75 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨75, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op4

theorem op4_76 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 76 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨76, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op4

theorem op4_77 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 77 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨77, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op4

theorem op4_78 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 78 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨78, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op4

theorem op4_79 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 79 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨79, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op4

theorem op4_80 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 80 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨80, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op4

theorem op4_81 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 81 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨81, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op4

theorem op4_82 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 82 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨82, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op4

theorem op4_83 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 83 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨83, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op4

end Airbender.NonVacuous.KeccakSpan
