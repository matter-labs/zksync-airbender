import Airbender.Proofs.Blake2Round.ArtifactChecks
import Airbender.Review.Circuits.Blake2Round.Schedule
import Airbender.Proofs.Constraints
import Airbender.Proofs.Arithmetic.Lemmas
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2Round.Schedule.Proofs
open Arithmetic
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- No wrapping is used by the shared, fixed SIGMA schedule. -/
theorem schedule_indices : ∀ (round : Fin 10) (column : Fin 16),
    Blake2G.Control.messageSchedule[round][column] < 16 := by decide

private def column (round : Fin 10) (position : Fin 16) : Fin 16 :=
  Fin.ofNat 16 Blake2G.Control.messageSchedule[round][position]

/-- Normalize each imported equation once to a sum over rounds. The exclusive
    mask is used only afterward; the circuit's multi-selector behavior is retained. -/
theorem equations {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 6)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    ∀ j : Fin 16,
      w Variables.scheduledMessage[j].1 = ∑ r : Fin 10,
        w Variables.roundBits[r] * Preparation.messageLimb w (column r j).val 0 ∧
      w Variables.scheduledMessage[j].2 = ∑ r : Fin 10,
        w Variables.roundBits[r] * Preparation.messageLimb w (column r j).val 1 := by
  have products (r : Fin 10) :
      w (204 + r.val) = w Variables.roundBits[r] * w 203 ∧
      w (214 + r.val) = w Variables.roundBits[r] * w 202 := by
    have left := Verification.assertion_of_holds h ⟨54 + r.val,
      by rw [constraint_count]; have := r.isLt; omega⟩
    have right := Verification.assertion_of_holds h ⟨64 + r.val,
      by rw [constraint_count]; have := r.isLt; omega⟩
    fin_cases r <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, Variables.roundBits] at left right ⊢
    all_goals constructor
    all_goals first | linear_combination -left | linear_combination -right
  have product0 := products 0
  have product1 := products 1
  have product2 := products 2
  have product3 := products 3
  have product4 := products 4
  have product5 := products 5
  have product6 := products 6
  have product7 := products 7
  have product8 := products 8
  have product9 := products 9
  norm_num [Variables.roundBits] at product0 product1 product2 product3 product4 product5 product6 product7 product8 product9
  intro j
  have lo := Verification.assertion_of_holds h ⟨74 + 2 * j.val,
    by rw [constraint_count]; have := j.isLt; omega⟩
  have high := Verification.assertion_of_holds h ⟨75 + 2 * j.val,
    by rw [constraint_count]; have := j.isLt; omega⟩
  clear h
  fin_cases j <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at lo high
  all_goals try simp only [product0.1, product0.2, product1.1, product1.2, product2.1, product2.2, product3.1, product3.2, product4.1, product4.2, product5.1, product5.2, product6.1, product6.2, product7.1, product7.2, product8.1, product8.2, product9.1, product9.2] at lo high
  all_goals norm_num [Fin.sum_univ_succ, Variables.scheduledMessage,
    Preparation.messageLimb, Variables.roundBits, column, Blake2G.Control.messageSchedule, Fin.ofNat]
  all_goals constructor
  all_goals first | linear_combination -lo | linear_combination -high


theorem soundness {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 6)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions spec := by
  intro input output w ⟨interface, h, mapping⟩
  have fields := equations h
  have selected (f : Fin 10 → ZMod p) : (∑ r, w Variables.roundBits[r] * f r) = f input.round := by
    calc
      _ = ∑ r : Fin 10, (if r = input.round then 1 else 0) * f r := by
        apply Finset.sum_congr rfl
        intro r _
        rw [interface.roundMask r]
      _ = _ := by simp
  unfold spec step
  rw [mapping.output, mapping.message]
  apply Vector.ext
  intro j hj
  obtain ⟨lo, high⟩ := fields ⟨j, hj⟩
  rw [selected] at lo high
  simp only [Fin.getElem_fin] at lo high
  simp only [Preparation.words, Preparation.messageWords, Vector.getElem_map]
  rw [lo, high]
  simp only [column, Fin.getElem_fin, Vector.getElem_ofFn]

end Airbender.Blake2Round.Schedule.Proofs
