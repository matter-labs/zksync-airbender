module
public import Slop.NonVacuous.KeccakSpan.Route

@[expose] public section

/-! The gated copy assertions 84 to 119: a mode writes back the lanes it leaves unchanged. -/

namespace Airbender.NonVacuous.KeccakSpan

variable {p : Nat} [Fact p.Prime]

theorem copy_84 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 84 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨84, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_85 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 85 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨85, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_86 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 86 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨86, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_87 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 87 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨87, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_88 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 88 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨88, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_89 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 89 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨89, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_90 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 90 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨90, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_91 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 91 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨91, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_92 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 92 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨92, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_93 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 93 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨93, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_94 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 94 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨94, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_95 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 95 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨95, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_96 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 96 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨96, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_97 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 97 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨97, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_98 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 98 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨98, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_99 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 99 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨99, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_100 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 100 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨100, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_101 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 101 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨101, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_102 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 102 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨102, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_103 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 103 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨103, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_104 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 104 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨104, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_105 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 105 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨105, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_106 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 106 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨106, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_107 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 107 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨107, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_108 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 108 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨108, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_109 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 109 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨109, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_110 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 110 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨110, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_111 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 111 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨111, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_112 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 112 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨112, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_113 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 113 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨113, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_114 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 114 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨114, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_115 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 115 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨115, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_116 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 116 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨116, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_117 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 117 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨117, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_118 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 118 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨118, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

theorem copy_119 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 119 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨119, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  copy

end Airbender.NonVacuous.KeccakSpan
