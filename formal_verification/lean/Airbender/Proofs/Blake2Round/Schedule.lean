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
    {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    ∀ j : Fin 16,
      w Variables.scheduledMessage[j].1 = ∑ r : Fin 10,
        w Variables.roundBits[r] * w Variables.preparedMessage[column r j].1 ∧
      w Variables.scheduledMessage[j].2 = ∑ r : Fin 10,
        w Variables.roundBits[r] * w Variables.preparedMessage[column r j].2 := by
  intro j
  have lo := Verification.assertion_of_holds h ⟨86 + 2 * j.val,
    by rw [constraint_count]; have := j.isLt; omega⟩
  have high := Verification.assertion_of_holds h ⟨87 + 2 * j.val,
    by rw [constraint_count]; have := j.isLt; omega⟩
  clear h
  fin_cases j <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at lo high
  all_goals norm_num [Fin.sum_univ_succ, Variables.scheduledMessage, Variables.preparedMessage,
    Variables.roundBits, column, Blake2G.Control.messageSchedule, Fin.ofNat]
  all_goals constructor
  all_goals first | linear_combination -lo | linear_combination -high

theorem soundness {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) :
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
  simp only [Preparation.words, Vector.getElem_map]
  rw [lo, high]
  simp only [column, Fin.getElem_fin, Vector.getElem_map]

end Airbender.Blake2Round.Schedule.Proofs
