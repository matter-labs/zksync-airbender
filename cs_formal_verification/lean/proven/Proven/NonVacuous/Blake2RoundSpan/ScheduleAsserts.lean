module
public import Proven.NonVacuous.Blake2RoundSpan.Honest
public import Proven.Blake2Round.Schedule

@[expose] public section

/-! The 32 message-schedule equations of an honest round row (imported constraints 74 to 105) hold: each sums, over
    the ten round bits, the round's selected message limb (`Schedule.Proofs.round_sum`); the honest mode products
    are zero and the round mask selects the row's round, whose scheduled word is the honest column. -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Blake2Round.Schedule.Proofs
open scoped BigOperators

variable {p : Nat} [Fact p.Prime]

theorem assignment_products (x : RowInput) {n : Nat} (low : 202 ≤ n) (high : n < 224) :
    x.assignment (p := p) n = 0 := by
  rw [RowInput.assignment, RowInput.column_products x low high, Nat.cast_zero]

theorem schedule_asserts (x : RowInput) (setup : Table (ZMod p) (fields 6)) (j : Nat) (hj : j < 16) (limb : Nat)
    (hl : limb < 2) :
    ((FlatOperation.constraints (Blake2Round.importedConstraints setup)).get
      ⟨74 + 2 * j + limb, by rw [Blake2Round.constraint_count]; omega⟩).eval
        (Verification.environment x.assignment) = 0 := by
  have products : ∀ r < 10, x.assignment (p := p) (204 + r) = x.assignment (142 + r) * x.assignment 203 ∧
      x.assignment (p := p) (214 + r) = x.assignment (142 + r) * x.assignment 202 := fun r hr => by
    simp only [assignment_products x (n := 204 + r) (by omega) (by omega),
      assignment_products x (n := 214 + r) (by omega) (by omega), assignment_products x (n := 203) (by omega)
        (by omega), assignment_products x (n := 202) (by omega) (by omega), mul_zero, and_self]
  have shape := message_shape setup ⟨j, hj⟩ ⟨limb, hl⟩
  simp only at shape
  rw [shape, messageConstraint, Expression.eval, Expression.eval, round_sum products ⟨j, hj⟩ limb 10 le_rfl]
  have bit (r : Fin 10) : x.assignment (p := p) (142 + r.val) = if r = x.round then 1 else 0 := by
    rw [RowInput.assignment, RowInput.column_bits x (by omega) (by omega)]
    by_cases same : r = x.round
    · rw [ite_eq_left (by rw [same]), ite_eq_left same, Nat.cast_one]
    · rw [ite_eq_right (fun e => same (Fin.ext (by omega))), ite_eq_right same, Nat.cast_zero]
  simp only [bit, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have limbs (word : Nat) (hw : word < 16) : Blake2Round.Preparation.messageLimb x.assignment word limb =
      ((RowInput.limb (x.message word) limb : Nat) : ZMod p) := by
    unfold Blake2Round.Preparation.messageLimb
    rw [assignment_products x (n := 203) (by omega) (by omega), assignment_products x (n := 202) (by omega)
      (by omega), RowInput.assignment, RowInput.column_message x (by omega) (by omega),
      show (103 + 2 * word + limb - 103) / 2 = word by omega, show (103 + 2 * word + limb - 103) % 2 = limb by omega]
    split_ifs <;> ring
  simp only [Expression.eval, Verification.environment]
  rw [limbs _ (column x.round ⟨j, hj⟩).isLt, RowInput.assignment, RowInput.column_scheduled x (by omega) (by omega),
    show (224 + 2 * j + limb - 224) / 2 = j by omega, show (224 + 2 * j + limb - 224) % 2 = limb by omega]
  simp only [RowInput.sched]
  have index : (Fin.ofNat 16 j : Fin 16) = ⟨j, hj⟩ := Fin.ext (by simp [Nat.mod_eq_of_lt hj])
  rw [index]
  push_cast
  ring

end Airbender.NonVacuous.Blake2RoundSpan
