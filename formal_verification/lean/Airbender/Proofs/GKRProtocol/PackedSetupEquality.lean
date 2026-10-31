import Airbender.Import.SetupPacked

namespace Airbender.Compiler.PackedSetupEquality
open Airbender.Setup
set_option warningAsError true

/-- Literal leaves have at most 64 bytes. The importer keeps larger source
arrays as the same balanced append tree. -/
def bytes : Nat → Nat → List Nat
  | 0, _ => []
  | length + 1, payload => payload % 256 :: bytes length (payload / 256)

/-- Numeric parameters preserve the array expressions in the native import. -/
inductive ArrayCode where
  | literal (length payload : Nat)
  | append (left right : ArrayCode)
  | constant (length value : Nat)
  | range (length : Nat)
  | linear (length first : Nat)
  | rotate (length first : Nat)
  | linearRuns (length first step run : Nat)
  | lookupRuns (length run : Nat) (values : ArrayCode)
  | packedBytes (length payload : Nat)
  deriving DecidableEq

abbrev ArrayCode.decode : ArrayCode → Array Nat
  | .literal length payload => (bytes length payload).toArray
  | .append left right => left.decode ++ right.decode
  | .constant length value => Array.replicate length value
  | .range length => Array.range length
  | .linear length first => Array.ofFn fun index : Fin length => first + index.val
  | .rotate length first => Array.ofFn fun index : Fin length => (first + index.val) % length
  | .linearRuns length first step run =>
      Array.ofFn fun index : Fin length => first + step * (index.val / run)
  | .lookupRuns length run values =>
      Array.ofFn fun index : Fin length => (values.decode[index.val / run]?).getD 0
  | .packedBytes length payload => packedArray length payload

inductive BlockCode where
  | affine (length first : Nat) (stride : Int)
  | dense (values : ArrayCode)
  | periodic (count : Nat) (stride : Int) (values : ArrayCode)
  deriving DecidableEq

abbrev BlockCode.decode : BlockCode → Block
  | .affine length first stride => .affine length first stride
  | .dense values => .dense values.decode
  | .periodic count stride values => .periodic count stride values.decode

def ArrayCode.length : ArrayCode → Nat
  | .literal length _ | .constant length _ | .range length | .linear length _
  | .rotate length _ | .linearRuns length _ _ _ | .lookupRuns length _ _
  | .packedBytes length _ => length
  | .append left right => left.length + right.length

def BlockCode.length : BlockCode → Nat
  | .affine length _ _ => length
  | .dense values => values.length
  | .periodic count _ values => count * values.length

theorem bytes_length (length payload : Nat) : (bytes length payload).length = length := by
  induction length generalizing payload with
  | zero => rfl
  | succ length ih => simp only [bytes, List.length_cons, ih]

theorem ArrayCode.decode_length (code : ArrayCode) : code.decode.size = code.length := by
  induction code with
  | literal length payload => simp only [decode, ArrayCode.length, List.size_toArray, bytes_length]
  | append left right first second => simp only [decode, ArrayCode.length, Array.size_append, first, second]
  | constant length value => simp only [decode, ArrayCode.length, Array.size_replicate]
  | range length => simp only [decode, ArrayCode.length, Array.size_range]
  | linear length first => simp only [decode, ArrayCode.length, Array.size_ofFn]
  | rotate length first => simp only [decode, ArrayCode.length, Array.size_ofFn]
  | linearRuns length first step run => simp only [decode, ArrayCode.length, Array.size_ofFn]
  | lookupRuns length run values ih => simp only [decode, ArrayCode.length, Array.size_ofFn]
  | packedBytes length payload => simp only [decode, ArrayCode.length, packedArray, Array.size_ofFn]

theorem BlockCode.decode_length (code : BlockCode) : code.decode.length = code.length := by
  cases code <;> simp only [BlockCode.length, Block.length, ArrayCode.decode_length]

def rowCount (code : List BlockCode) (first count : Nat) : Nat :=
  (((code.drop first).take count).map BlockCode.length).sum

theorem rowCount_eq (code : List BlockCode) (first count : Nat) :
    rowCount code first count =
      ((((code.map BlockCode.decode).drop first).take count).map Block.length).sum := by
  simp [rowCount, List.map_map, Function.comp_def, BlockCode.decode_length]

structure LengthCheck where
  first : Nat
  count : Nat
  expected : Nat
  deriving DecidableEq

def check (left right : List BlockCode) : Bool := decide (left = right)

/-- Equality of the numeric encodings proves exact equality of the source
blocks. It includes block boundaries, signed strides and every array value. -/
theorem check_sound (left right : List BlockCode) (checked : check left right = true) :
    left.map BlockCode.decode = right.map BlockCode.decode :=
  congrArg (List.map BlockCode.decode) (of_decide_eq_true checked)

def checkWithLengths (left right : List BlockCode) (lengths : List LengthCheck) : Bool :=
  check left right && lengths.all (fun item => rowCount left item.first item.count == item.expected)

theorem checkWithLengths_sound (left right : List BlockCode) (lengths : List LengthCheck)
    (checked : checkWithLengths left right lengths = true) :
    left.map BlockCode.decode = right.map BlockCode.decode ∧
    ∀ item ∈ lengths,
      ((((left.map BlockCode.decode).drop item.first).take item.count).map Block.length).sum = item.expected := by
  simp only [checkWithLengths, Bool.and_eq_true] at checked
  refine ⟨check_sound _ _ checked.1, ?_⟩
  intro item member
  have accepted := (List.all_eq_true.mp checked.2) item member
  have equal : rowCount left item.first item.count = item.expected := by
    simpa only [beq_iff_eq] using accepted
  exact (rowCount_eq _ _ _).symm.trans equal

theorem select_middle (values front middle tail : List Block) (first count : Nat)
    (layout : values = front ++ middle ++ tail) (frontSize : front.length = first)
    (width : middle.length = count) : (values.drop first).take count = middle := by
  rw [layout, ← frontSize, ← width]
  simp

end Airbender.Compiler.PackedSetupEquality
