import Airbender.Proofs.Tables.PackedXor9Checks

namespace Airbender.Setup.Proofs.PackedXor7Checks
open PackedSignedRun PackedWordBlocks
set_option warningAsError true
set_option maxRecDepth 32768

def indexPacked : Nat := PackedXor9Checks.indexPacked % 65536 ^ 128
def repeatedOnes : Nat := PackedXor9Checks.repeatedOnes % 65536 ^ 128

theorem index_correct : indexPacked = Nat.ofDigits 65536 (List.range 128) := by decide +kernel
theorem ones_correct : repeatedOnes = Nat.ofDigits 65536 (List.replicate 128 1) := by decide +kernel

theorem extract_xor (left right index : Nat) :
    digit 65536 (left ^^^ right) index =
      digit 65536 left index ^^^ digit 65536 right index := by
  have power : (65536 : Nat) ^ index = 2 ^ (16 * index) := by
    rw [pow_mul]
    norm_num
  simp only [digit, power]
  rw [Nat.xor_div_two_pow]
  simpa only [show (2 : Nat) ^ 16 = 65536 by norm_num] using
    (Nat.xor_mod_two_pow (a := left / 2 ^ (16 * index))
      (b := right / 2 ^ (16 * index)) (n := 16))

def expectedRow (row : Nat) : Nat := (indexPacked ^^^ (row * repeatedOnes)) % 65536 ^ 128

theorem expected_digit (row column : Nat) (rowBound : row < 128) (columnBound : column < 128) :
    digit 65536 (expectedRow row) column = row ^^^ column := by
  have projected := segment_digit 65536 (indexPacked ^^^ (row * repeatedOnes)) 0 128 column columnBound
  simp only [pow_zero, Nat.div_one, Nat.zero_add] at projected
  rw [expectedRow, projected, extract_xor, index_correct, ones_correct]
  have indexDigit : digit 65536 (Nat.ofDigits 65536 (List.range 128)) column = column := by
    have extracted := PackedRadix.extractDigitBase 65536 (List.range 128) column (by omega)
      (fun value member => by have bound := List.mem_range.mp member; omega)
      (by simpa using columnBound)
    simpa only [digit, List.getElem_range] using extracted
  have repeated : digit 65536 (row * Nat.ofDigits 65536 (List.replicate 128 1)) column = row := by
    rw [Nat.mul_ofDigits]
    simp only [List.map_replicate, mul_one]
    have extracted := PackedRadix.extractDigitBase 65536 (List.replicate 128 row) column (by omega)
      (fun value member => by have same := List.eq_of_mem_replicate member; omega)
      (by simpa using columnBound)
    simpa only [digit, List.getElem_replicate] using extracted
  rw [indexDigit, repeated, Nat.xor_comm]

def window (row : Nat) : Nat := expectedRow row + 65536 ^ 128 * expectedRow (row + 1)
def span (origin length : Nat) : Nat := (window (origin / 128) / 65536 ^ (origin % 128)) % 65536 ^ length
def legal (origin length : Nat) : Bool := origin + length ≤ 16384 && origin % 128 + length ≤ 256

theorem window_low (row index : Nat) (rowBound : row < 128) (within : index < 128) :
    digit 65536 (window row) index = row ^^^ index := by
  have bounded : expectedRow row < 65536 ^ 128 := Nat.mod_lt _ (by positivity)
  have reduced : window row % 65536 ^ 128 = expectedRow row := by
    simp only [window, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bounded]
  have projected := segment_digit 65536 (window row) 0 128 index within
  simp only [Nat.pow_zero, Nat.div_one, Nat.zero_add, reduced] at projected
  rw [← projected]
  exact expected_digit row index rowBound within

theorem window_high (row index : Nat) (rowBound : row + 1 < 128) (within : index < 128) :
    digit 65536 (window row) (128 + index) = (row + 1) ^^^ index := by
  have bounded : expectedRow row < 65536 ^ 128 := Nat.mod_lt _ (by positivity)
  have divided : window row / 65536 ^ 128 = expectedRow (row + 1) := by
    simp only [window, Nat.add_mul_div_left _ _ (show 0 < 65536 ^ 128 by positivity),
      Nat.div_eq_of_lt bounded, Nat.zero_add]
  unfold digit
  rw [pow_add, ← Nat.div_div_eq_div_mul, divided]
  exact expected_digit (row + 1) index rowBound within

theorem span_digit (origin length index : Nat) (accepted : legal origin length = true)
    (within : index < length) :
    digit 65536 (span origin length) index = (origin + index) / 128 ^^^ (origin + index) % 128 := by
  simp only [legal, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have originParts := Nat.div_add_mod origin 128
  have totalParts := Nat.div_add_mod (origin + index) 128
  have projected := segment_digit 65536 (window (origin / 128)) (origin % 128) length index within
  rw [span, projected]
  by_cases first : origin % 128 + index < 128
  · rw [window_low (origin / 128) (origin % 128 + index) (by omega) first]
    exact congrArg₂ Nat.xor (by omega) (by omega)
  · have columnBound : origin % 128 + index - 128 < 128 := by omega
    have indexSplit : origin % 128 + index = 128 + (origin % 128 + index - 128) := by omega
    rw [indexSplit, window_high (origin / 128) _ (by omega) columnBound]
    exact congrArg₂ Nat.xor (by omega) (by omega)

def checkBlock (origin : Nat) (block : Code) : Bool :=
  legal origin block.length && PackedWordBounds.fastValid block.input &&
    block.input.packed 65536 == span origin block.length

def check (origin : Nat) (blocks : List Code) : Bool :=
  (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun block _ tail position =>
      match position with
      | 0 => checkBlock 0 block && tail block.length
      | next + 1 => checkBlock (next + 1) block && tail (next + 1 + block.length)) blocks) origin

theorem check_cons (origin : Nat) (block : Code) (rest : List Code) :
    check origin (block :: rest) = (checkBlock origin block && check (origin + block.length) rest) := by
  cases origin with
  | zero => simp only [check, Nat.zero_add]
  | succ origin => rfl

theorem checkBlock_sound (origin : Nat) (block : Code) (checked : checkBlock origin block = true)
    (index : Nat) (within : index < (block.decode 65536).length) :
    (block.decode 65536).get? index = some ((origin + index) / 128 ^^^ (origin + index) % 128) := by
  simp only [checkBlock, Bool.and_eq_true, beq_iff_eq] at checked
  have raw := input_sound 65536 (by omega) block (PackedWordBounds.fastValid_sound block.input checked.1.2) index (by rwa [decode_length] at within)
  rw [checked.2, span_digit origin block.length index checked.1.1 (by rwa [decode_length] at within)] at raw
  exact raw

theorem check_sound (origin : Nat) (blocks : List Code) (checked : check origin blocks = true) :
    checkBlocks (fun index => index / 128 ^^^ index % 128) origin (blocks.map (Code.decode 65536)) = true := by
  induction blocks generalizing origin with
  | nil => rfl
  | cons block rest ih =>
    simp only [check_cons, Bool.and_eq_true] at checked
    rw [List.map_cons, checkBlocks_cons_iff]
    constructor
    · intro index
      exact checkBlock_sound origin block checked.1 index.val index.isLt
    · rw [decode_length]
      exact ih _ checked.2

structure Request where
  origin : Nat
  blocks : List Code
  length : Nat

def checkRequests (requests : List Request) : Bool :=
  requests.all (fun request => check request.origin request.blocks &&
    (request.blocks.map Code.length).sum == request.length)

theorem requests_sound (requests : List Request) (checked : checkRequests requests = true)
    (index : Nat) (request : Request) (found : requests[index]? = some request) :
    checkBlocks (fun value => value / 128 ^^^ value % 128) request.origin
      (request.blocks.map (Code.decode 65536)) = true ∧
    ((request.blocks.map (Code.decode 65536)).map Block.length).sum = request.length := by
  obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp found
  have member : request ∈ requests := same ▸ List.getElem_mem within
  have result := List.all_eq_true.mp checked request member
  simp only [Bool.and_eq_true, beq_iff_eq] at result
  refine ⟨check_sound request.origin request.blocks result.1, ?_⟩
  simpa only [List.map_map, Function.comp_def, decode_length] using result.2

end Airbender.Setup.Proofs.PackedXor7Checks
