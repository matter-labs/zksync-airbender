import Airbender.Proofs.Tables.PackedXor9Checks

namespace Airbender.Setup.Proofs.PackedByteTableChecks
open PackedSignedRun PackedWordBlocks PackedWordBounds
set_option warningAsError true

inductive Operation where
  | bitAnd | bitOr | bitXor | chi

def Operation.apply : Operation → Nat → Nat → Nat
  | .bitAnd => Nat.land
  | .bitOr => Nat.lor
  | .bitXor => Nat.xor
  | .chi => fun row column => (column ^^^ 255) &&& row

def indexPacked : Nat := PackedXor9Checks.indexPacked % 65536 ^ 256

theorem index_digit (index : Nat) (within : index < 256) :
    digit 65536 indexPacked index = index := by
  have segment := segment_digit 65536 PackedXor9Checks.indexPacked 0 256 index within
  simp only [pow_zero, Nat.div_one, Nat.zero_add] at segment
  rw [indexPacked, segment, PackedXor9Checks.index_correct]
  have result := PackedRadix.extractDigitBase 65536 (List.range 512) index (by omega)
    (fun value member => by have bound := List.mem_range.mp member; omega) (by simpa using (show index < 512 by omega))
  simpa only [digit, List.getElem_range] using result

def unboundedRow (operation : Operation) (row : Nat) : Nat :=
  match operation with
  | .bitAnd => indexPacked &&& (row * units 256)
  | .bitOr => indexPacked ||| (row * units 256)
  | .bitXor => indexPacked ^^^ (row * units 256)
  | .chi => (indexPacked ^^^ (255 * units 256)) &&& (row * units 256)

def expectedRow (operation : Operation) (row : Nat) : Nat := unboundedRow operation row % 65536 ^ 256

theorem expected_digit (operation : Operation) (row column : Nat) (rowBound : row < 256)
    (columnBound : column < 256) :
    digit 65536 (expectedRow operation row) column = operation.apply row column := by
  have projected := segment_digit 65536 (unboundedRow operation row) 0 256 column columnBound
  simp only [pow_zero, Nat.div_one, Nat.zero_add] at projected
  rw [expectedRow, projected]
  have repeated := repeated_digit row 256 column (by omega) columnBound
  cases operation with
  | bitAnd =>
    rw [unboundedRow, extract_and, index_digit column columnBound, repeated]
    exact Nat.and_comm _ _
  | bitOr =>
    rw [unboundedRow, extract_or, index_digit column columnBound, repeated]
    exact Nat.or_comm _ _
  | bitXor =>
    rw [unboundedRow, PackedXor9Checks.extract_xor, index_digit column columnBound, repeated]
    exact Nat.xor_comm _ _
  | chi =>
    rw [unboundedRow, extract_and, PackedXor9Checks.extract_xor, index_digit column columnBound,
      repeated_digit 255 256 column (by omega) columnBound, repeated]
    rfl

def window (operation : Operation) (row : Nat) : Nat :=
  expectedRow operation row + 65536 ^ 256 * expectedRow operation (row + 1)
def span (operation : Operation) (origin length : Nat) : Nat :=
  (window operation (origin / 256) / 65536 ^ (origin % 256)) % 65536 ^ length
def legal (origin length : Nat) : Bool := origin + length ≤ 65536 && origin % 256 + length ≤ 512

theorem window_low (operation : Operation) (row index : Nat) (rowBound : row < 256) (within : index < 256) :
    digit 65536 (window operation row) index = operation.apply row index := by
  have bounded : expectedRow operation row < 65536 ^ 256 := Nat.mod_lt _ (by positivity)
  have reduced : window operation row % 65536 ^ 256 = expectedRow operation row := by
    simp only [window, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bounded]
  have projected := segment_digit 65536 (window operation row) 0 256 index within
  simp only [Nat.pow_zero, Nat.div_one, Nat.zero_add, reduced] at projected
  rw [← projected]
  exact expected_digit operation row index rowBound within

theorem window_high (operation : Operation) (row index : Nat) (rowBound : row + 1 < 256) (within : index < 256) :
    digit 65536 (window operation row) (256 + index) = operation.apply (row + 1) index := by
  have bounded : expectedRow operation row < 65536 ^ 256 := Nat.mod_lt _ (by positivity)
  have divided : window operation row / 65536 ^ 256 = expectedRow operation (row + 1) := by
    simp only [window, Nat.add_mul_div_left _ _ (show 0 < 65536 ^ 256 by positivity),
      Nat.div_eq_of_lt bounded, Nat.zero_add]
  unfold digit
  rw [pow_add, ← Nat.div_div_eq_div_mul, divided]
  exact expected_digit operation (row + 1) index rowBound within

theorem span_digit (operation : Operation) (origin length index : Nat) (accepted : legal origin length = true)
    (within : index < length) :
    digit 65536 (span operation origin length) index = operation.apply ((origin + index) / 256) ((origin + index) % 256) := by
  simp only [legal, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have originParts := Nat.div_add_mod origin 256
  have totalParts := Nat.div_add_mod (origin + index) 256
  have projected := segment_digit 65536 (window operation (origin / 256)) (origin % 256) length index within
  rw [span, projected]
  by_cases first : origin % 256 + index < 256
  · rw [window_low operation (origin / 256) (origin % 256 + index) (by omega) first]
    exact congrArg₂ operation.apply (by omega) (by omega)
  · have columnBound : origin % 256 + index - 256 < 256 := by omega
    have indexSplit : origin % 256 + index = 256 + (origin % 256 + index - 256) := by omega
    rw [indexSplit, window_high operation (origin / 256) _ (by omega) columnBound]
    exact congrArg₂ operation.apply (by omega) (by omega)

def checkBlock (operation : Operation) (origin : Nat) (block : Code) : Bool :=
  legal origin block.length && fastValid block.input &&
    block.input.packed 65536 == span operation origin block.length

def check (operation : Operation) (origin : Nat) (blocks : List Code) : Bool :=
  (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun block _ tail position =>
      match position with
      | 0 => checkBlock operation 0 block && tail block.length
      | next + 1 => checkBlock operation (next + 1) block && tail (next + 1 + block.length)) blocks) origin

theorem check_cons (operation : Operation) (origin : Nat) (block : Code) (rest : List Code) :
    check operation origin (block :: rest) =
      (checkBlock operation origin block && check operation (origin + block.length) rest) := by
  cases origin with
  | zero => simp only [check, Nat.zero_add]
  | succ origin => rfl

theorem checkBlock_sound (operation : Operation) (origin : Nat) (block : Code)
    (checked : checkBlock operation origin block = true) (index : Nat)
    (within : index < (block.decode 65536).length) :
    (block.decode 65536).get? index =
      some (operation.apply ((origin + index) / 256) ((origin + index) % 256)) := by
  simp only [checkBlock, Bool.and_eq_true, beq_iff_eq] at checked
  have raw := input_sound 65536 (by omega) block (fastValid_sound block.input checked.1.2) index
    (by rwa [decode_length] at within)
  rw [checked.2, span_digit operation origin block.length index checked.1.1
    (by rwa [decode_length] at within)] at raw
  exact raw

theorem check_sound (operation : Operation) (origin : Nat) (blocks : List Code)
    (checked : check operation origin blocks = true) :
    checkBlocks (fun index => operation.apply (index / 256) (index % 256)) origin
      (blocks.map (Code.decode 65536)) = true := by
  induction blocks generalizing origin with
  | nil => rfl
  | cons block rest ih =>
    simp only [check_cons, Bool.and_eq_true] at checked
    rw [List.map_cons, checkBlocks_cons_iff]
    constructor
    · intro index
      exact checkBlock_sound operation origin block checked.1 index.val index.isLt
    · rw [decode_length]
      exact ih _ checked.2

end Airbender.Setup.Proofs.PackedByteTableChecks
