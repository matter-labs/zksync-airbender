module
public import Slop.NonVacuous.KeccakSpan.Route

@[expose] public section

/-! The thirteen routing assertions of the fourth operation (imported assertions 58 to 70). -/

namespace Airbender.NonVacuous.KeccakSpan

variable {p : Nat} [Fact p.Prime]

theorem op3_58 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 58 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨58, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op3

theorem op3_59 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 59 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨59, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op3

theorem op3_60 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 60 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨60, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op3

theorem op3_61 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 61 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨61, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op3

theorem op3_62 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 62 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨62, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op3

theorem op3_63 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 63 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨63, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op3

theorem op3_64 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 64 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨64, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op3

theorem op3_65 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 65 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨65, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op3

theorem op3_66 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 66 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨66, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op3

theorem op3_67 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 67 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨67, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op3

theorem op3_68 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 68 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨68, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op3

theorem op3_69 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 69 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨69, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op3

theorem op3_70 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 70 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨70, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  route RowInput.op3

end Airbender.NonVacuous.KeccakSpan
