module
public import Slop.NonVacuous.KeccakSpan.Route

@[expose] public section

/-! The gated copy assertions 120 to 155: a mode writes back the lanes it leaves unchanged. -/

namespace Airbender.NonVacuous.KeccakSpan

variable {p : Nat} [Fact p.Prime]

theorem copy_120 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 120 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨120, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_121 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 121 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨121, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_122 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 122 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨122, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_123 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 123 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨123, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_124 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 124 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨124, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_125 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 125 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨125, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_126 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 126 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨126, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_127 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 127 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨127, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_128 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 128 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨128, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_129 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 129 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨129, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_130 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 130 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨130, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_131 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 131 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨131, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_132 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 132 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨132, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_133 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 133 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨133, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_134 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 134 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨134, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_135 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 135 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨135, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_136 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 136 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨136, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_137 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 137 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨137, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_138 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 138 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨138, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_139 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 139 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨139, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_140 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 140 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨140, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_141 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 141 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨141, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_142 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 142 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨142, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_143 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 143 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨143, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_144 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 144 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨144, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_145 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 145 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨145, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_146 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 146 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨146, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_147 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 147 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨147, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_148 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 148 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨148, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_149 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 149 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨149, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_150 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 150 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨150, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_151 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 151 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨151, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_152 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 152 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨152, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_153 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 153 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨153, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_154 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 154 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨154, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_155 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 155 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨155, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

end Airbender.NonVacuous.KeccakSpan
