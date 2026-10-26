import Airbender.Review.Circuits.Blake2Round.Artifact
import Airbender.Proofs.Blake2Round.ArtifactChecks
import Airbender.Proofs.Delegation.ClockFacts

namespace Airbender.Blake2Round.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

theorem clock_facts {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 6)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setup)) :
    Delegation.Proofs.ClockFacts importedConstraintsDelegationColumns w := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (importedConstraints setup) importedConstraintsTimestampLookups)
  have timestamps := Verification.holds_of_sublist h
    (List.sublist_append_right (importedConstraints setup) importedConstraintsTimestampLookups)
  refine ⟨?_, ?_⟩
  · intro port member
    rw [delegation_columns] at member
    simp only [Vector.toArray_ofFn, Array.mem_ofFn] at member
    obtain ⟨i, rfl⟩ := member
    change (2 : Nat) < 4
    decide
  · intro port member
    rw [delegation_columns] at member
    simp only [Vector.toArray_ofFn, Array.mem_ofFn] at member
    obtain ⟨i, rfl⟩ := member
    have bit := Verification.assertion_of_holds core
      ⟨177 + i.val, by rw [constraint_count]; omega⟩
    have lowerLookup := Verification.lookup_of_holds timestamps
      ⟨1 + 2 * i.val, by rw [timestamp_count]; omega⟩
    have upperLookup := Verification.lookup_of_holds timestamps
      ⟨2 + 2 * i.val, by rw [timestamp_count]; omega⟩
    fin_cases i
    all_goals have lower := Trace.Proofs.range_bound lowerLookup
    all_goals have upper := Trace.Proofs.range_bound upperLookup
    all_goals simp [importedConstraints, importedConstraintsDelegationColumns, FlatOperation.constraints,
        Expression.eval, Verification.environment,
        sub_eq_add_neg, Trace.timestampBase] at bit lower upper ⊢
    all_goals refine ⟨?_, ?_, ?_⟩
    all_goals first
      | simpa only [add_comm] using bit
      | solve | convert lower using 1; congr 1; ring
      | solve | convert upper using 1; congr 1; ring

end Airbender.Blake2Round.Proofs
