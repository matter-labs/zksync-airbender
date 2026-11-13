module
public import Human.Circuits.Keccak.Artifact
public import Proven.Keccak.ArtifactChecks
public import Proven.Delegation.ClockFacts
public import Proven.Keccak.OpIndex
public import Proven.CleanCore.Circuit.Operations

@[expose] public section

namespace Airbender.Keccak.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

theorem clock_facts {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 8)}
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
      ⟨173 + i.val, by rw [constraint_count]; omega⟩
    have lowerLookup := Verification.lookup_of_holds timestamps
      ⟨1 + 2 * i.val, by rw [timestamp_count]; omega⟩
    have upperLookup := Verification.lookup_of_holds timestamps
      ⟨2 + 2 * i.val, by rw [timestamp_count]; omega⟩
    fin_cases i
    all_goals have lower := Trace.Proofs.range_bound lowerLookup
    all_goals have upper := Trace.Proofs.range_bound upperLookup
    all_goals op_index at bit lower upper
    all_goals simp [importedConstraintsDelegationColumns, Expression.eval, Verification.environment,
        sub_eq_add_neg, Trace.timestampBase] at bit lower upper ⊢
    all_goals refine ⟨?_, ?_, ?_⟩
    all_goals first
      | simpa only [add_comm] using bit
      | solve | convert lower using 1; congr 1; ring
      | solve | convert upper using 1; congr 1; ring

end Airbender.Keccak.Proofs
