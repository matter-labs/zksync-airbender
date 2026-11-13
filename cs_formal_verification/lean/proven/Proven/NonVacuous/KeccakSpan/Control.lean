module
public import Proven.NonVacuous.KeccakSpan.Route
public import Proven.NonVacuous.ClockCompleteness

@[expose] public section

/-! The control assertions of a Keccak row (imported assertions 0 to 18 and 156 to 186) hold for the honest
    assignment: the active flag, the zero high limbs of x10, the decomposition of the control word into one-hot
    mode and iteration flags and five round bits, the next control word, Rho's iteration flags, the Iota round and
    constant limbs, and the Boolean flags (the borrow flags of the fourteen ports hold 1). -/

namespace Airbender.NonVacuous.KeccakSpan

variable {p : Nat} [Fact p.Prime]

namespace RowInput
variable (x : RowInput)

theorem packed_eq : x.state.packed = x.mode + 8 * x.iteration + 64 * x.round := rfl

theorem next_eq : x.state.nextPacked =
    (if x.mode = 6 then (if x.iteration = 4 then 0 else 5)
      else if x.mode = 1 ∨ x.mode = 2 ∨ x.mode = 5 then x.mode + 1
      else x.mode + if x.iteration = 4 then 1 else 0) +
    8 * (if x.mode = 0 ∨ x.mode = 3 ∨ x.mode = 4 ∨ x.mode = 6 then
      (if x.iteration = 4 then 0 else x.iteration + 1) else x.iteration) +
    64 * (x.round + if x.mode = 6 ∧ x.iteration = 4 then 1 else 0) := rfl

/-- The round is its five bits. -/
theorem round_cast : (x.round : ZMod p) = ((x.round / 2 ^ 0 % 2 : Nat) : ZMod p) +
    2 * ((x.round / 2 ^ 1 % 2 : Nat) : ZMod p) + 4 * ((x.round / 2 ^ 2 % 2 : Nat) : ZMod p) +
    8 * ((x.round / 2 ^ 3 % 2 : Nat) : ZMod p) + 16 * ((x.round / 2 ^ 4 % 2 : Nat) : ZMod p) := by
  have bound : x.round < 32 := x.state.round.isLt
  have identity : x.round = x.round / 2 ^ 0 % 2 + 2 * (x.round / 2 ^ 1 % 2) + 4 * (x.round / 2 ^ 2 % 2) +
      8 * (x.round / 2 ^ 3 % 2) + 16 * (x.round / 2 ^ 4 % 2) := by omega
  conv_lhs => rw [identity]
  push_cast
  ring

/-- The five iterations of a row. -/
theorem iterations :
    x.iteration = 0 ∨ x.iteration = 1 ∨ x.iteration = 2 ∨ x.iteration = 3 ∨ x.iteration = 4 := by
  have iteration := x.state.iteration.isLt
  simp only [RowInput.iteration]
  omega

/-- The 35 cases of a row: a mode and an iteration. -/
theorem states :
    (x.mode = 0 ∧ x.iteration = 0) ∨
      (x.mode = 0 ∧ x.iteration = 1) ∨
      (x.mode = 0 ∧ x.iteration = 2) ∨
      (x.mode = 0 ∧ x.iteration = 3) ∨
      (x.mode = 0 ∧ x.iteration = 4) ∨
      (x.mode = 1 ∧ x.iteration = 0) ∨
      (x.mode = 1 ∧ x.iteration = 1) ∨
      (x.mode = 1 ∧ x.iteration = 2) ∨
      (x.mode = 1 ∧ x.iteration = 3) ∨
      (x.mode = 1 ∧ x.iteration = 4) ∨
      (x.mode = 2 ∧ x.iteration = 0) ∨
      (x.mode = 2 ∧ x.iteration = 1) ∨
      (x.mode = 2 ∧ x.iteration = 2) ∨
      (x.mode = 2 ∧ x.iteration = 3) ∨
      (x.mode = 2 ∧ x.iteration = 4) ∨
      (x.mode = 3 ∧ x.iteration = 0) ∨
      (x.mode = 3 ∧ x.iteration = 1) ∨
      (x.mode = 3 ∧ x.iteration = 2) ∨
      (x.mode = 3 ∧ x.iteration = 3) ∨
      (x.mode = 3 ∧ x.iteration = 4) ∨
      (x.mode = 4 ∧ x.iteration = 0) ∨
      (x.mode = 4 ∧ x.iteration = 1) ∨
      (x.mode = 4 ∧ x.iteration = 2) ∨
      (x.mode = 4 ∧ x.iteration = 3) ∨
      (x.mode = 4 ∧ x.iteration = 4) ∨
      (x.mode = 5 ∧ x.iteration = 0) ∨
      (x.mode = 5 ∧ x.iteration = 1) ∨
      (x.mode = 5 ∧ x.iteration = 2) ∨
      (x.mode = 5 ∧ x.iteration = 3) ∨
      (x.mode = 5 ∧ x.iteration = 4) ∨
      (x.mode = 6 ∧ x.iteration = 0) ∨
      (x.mode = 6 ∧ x.iteration = 1) ∨
      (x.mode = 6 ∧ x.iteration = 2) ∨
      (x.mode = 6 ∧ x.iteration = 3) ∨
      (x.mode = 6 ∧ x.iteration = 4) := by
  rcases RowInput.modes x with hm | hm | hm | hm | hm | hm | hm <;>
  rcases iterations x with ht | ht | ht | ht | ht <;> simp [hm, ht]

end RowInput

set_option hygiene false in
/-- The identity left once the flags are fixed. -/
local macro "evaluate" : tactic => `(tactic| (
  simp only [Expression.eval, Verification.environment, honest_column, RowInput.packed_eq, RowInput.next_eq,
    RowInput.iotaRound, RowInput.iotaB, ↓reduceIte, reduceIte, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceMul,
    Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero, false_and, and_false,
    and_self, true_and, or_self, true_or, or_true, false_or, or_false, Int.cast_negSucc, *] <;>
  push_cast [RowInput.round_cast x] <;> ring))

set_option hygiene false in
/-- Close a control assertion of the row `x`, by mode and iteration. -/
local macro "control" : tactic => `(tactic| (
  rcases RowInput.states x with
    ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ |
    ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ |
    ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ |
    ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ |
    ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ <;>
  evaluate))

set_option hygiene false in
/-- Close a control assertion of the row `x`, by mode. -/
local macro "by_mode" : tactic => `(tactic| (
  rcases RowInput.modes x with hm | hm | hm | hm | hm | hm | hm <;> evaluate))

set_option hygiene false in
/-- Close a control assertion of the row `x`, by iteration. -/
local macro "by_iteration" : tactic => `(tactic| (
  rcases RowInput.iterations x with ht | ht | ht | ht | ht <;> evaluate))

private theorem bit_of_ite (c : Prop) [Decidable c] : (if c then 1 else 0 : Nat) ≤ 1 := by split <;> omega

theorem control_0 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 0 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨0, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  simp only [Expression.eval, Verification.environment, honest_column]
  push_cast
  ring

theorem control_1 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 1 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨1, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  simp only [Expression.eval, Verification.environment, honest_column, Nat.cast_zero]

theorem control_2 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 2 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨2, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  simp only [Expression.eval, Verification.environment, honest_column, Nat.cast_zero]

theorem control_3 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 3 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨3, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  control

theorem control_4 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 4 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨4, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  by_mode

theorem control_5 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 5 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨5, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  by_iteration

theorem control_6 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 6 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨6, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  by_mode

theorem control_7 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 7 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨7, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  by_iteration

theorem control_8 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 8 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨8, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  control

theorem control_9 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 9 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨9, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  by_mode

theorem control_10 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 10 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨10, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  by_mode

theorem control_11 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 11 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨11, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  by_mode

theorem control_12 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 12 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨12, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  by_mode

theorem control_13 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 13 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨13, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  by_mode

theorem control_14 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 14 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨14, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  by_iteration

theorem control_15 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 15 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨15, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  evaluate

theorem control_16 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 16 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨16, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  evaluate

theorem control_17 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 17 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨17, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  evaluate

theorem control_18 (x : RowInput) (setup : Table (ZMod p) (fields 8))
    (h : 18 < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨18, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  op_index
  evaluate

/-- The Boolean assertions 156 to 186: mode, iteration and round flags, and the ports' borrow flags. -/
theorem flags (x : RowInput) (setup : Table (ZMod p) (fields 8)) (i : Nat) (low : 156 ≤ i) (high : i < 187)
    (h : i < (FlatOperation.constraints (Keccak.importedConstraints setup)).length) :
    ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨i, h⟩).eval
      (Verification.environment x.assignment) = 0 := by
  have bit {k n : Nat} (column : x.assignment (p := p) k = (n : ZMod p)) (bound : n ≤ 1) :=
    flag_eval column bound
  interval_cases i <;> op_index
  all_goals first
    | exact bit (RowInput.assignment_63 x) (bit_of_ite _)
    | exact bit (RowInput.assignment_64 x) (bit_of_ite _)
    | exact bit (RowInput.assignment_65 x) (bit_of_ite _)
    | exact bit (RowInput.assignment_66 x) (bit_of_ite _)
    | exact bit (RowInput.assignment_67 x) (bit_of_ite _)
    | exact bit (RowInput.assignment_68 x) (bit_of_ite _)
    | exact bit (RowInput.assignment_69 x) (bit_of_ite _)
    | exact bit (RowInput.assignment_70 x) (bit_of_ite _)
    | exact bit (RowInput.assignment_71 x) (bit_of_ite _)
    | exact bit (RowInput.assignment_72 x) (bit_of_ite _)
    | exact bit (RowInput.assignment_73 x) (bit_of_ite _)
    | exact bit (RowInput.assignment_74 x) (bit_of_ite _)
    | exact bit (RowInput.assignment_75 x) (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))
    | exact bit (RowInput.assignment_76 x) (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))
    | exact bit (RowInput.assignment_77 x) (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))
    | exact bit (RowInput.assignment_78 x) (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))
    | exact bit (RowInput.assignment_79 x) (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))
    | exact bit (n := 1) rfl le_rfl

end Airbender.NonVacuous.KeccakSpan
