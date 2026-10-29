import Airbender.Review.Circuits.Keccak.SplitColumnParity
import Airbender.Review.Circuits.Keccak.SplitColumnParityCached
import Airbender.Proofs.Delegation.ClockFacts

namespace Airbender.Keccak.Split.Proofs
open Airbender.Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private theorem column_parity_clock_index {port : TimestampPort}
    (member : port ∈ ColumnParity.importedConstraintsDelegationColumns.ports) :
    ∃ i : Fin 14, port = ColumnParity.importedConstraintsDelegationColumns.ports[i.val] := by
  obtain ⟨i, bound, equal⟩ := Array.mem_iff_getElem.mp member
  change i < 14 at bound
  exact ⟨⟨i, bound⟩, equal.symm⟩

/-- Column parity uses the ordinary per-port timestamp comparisons. -/
theorem column_parity_clock_facts {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ColumnParity.clockConstraints setup)) :
    Delegation.Proofs.ClockFacts
      ColumnParity.importedConstraintsDelegationColumns w := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (ColumnParity.importedConstraints setup)
      ColumnParity.importedConstraintsTimestampLookups)
  have timestamps := Verification.holds_of_sublist h
    (List.sublist_append_right (ColumnParity.importedConstraints setup)
      ColumnParity.importedConstraintsTimestampLookups)
  refine ⟨?_, ?_⟩
  · intro port member
    obtain ⟨i, rfl⟩ := column_parity_clock_index member
    fin_cases i <;> decide
  · intro port member
    obtain ⟨i, rfl⟩ := column_parity_clock_index member
    have bit := Verification.assertion_of_holds core
      ⟨6 + i.val, by simp [ColumnParity.importedConstraints, FlatOperation.constraints]; omega⟩
    have timestampCount :
        (FlatOperation.lookups (ColumnParity.importedConstraintsTimestampLookups
          (p := p))).length = 30 := by rfl
    have lowerLookup := Verification.lookup_of_holds timestamps
      ⟨1 + 2 * i.val, by rw [timestampCount]; omega⟩
    have upperLookup := Verification.lookup_of_holds timestamps
      ⟨2 + 2 * i.val, by rw [timestampCount]; omega⟩
    fin_cases i
    all_goals have lower := Trace.Proofs.range_bound lowerLookup
    all_goals have upper := Trace.Proofs.range_bound upperLookup
    all_goals simp [ColumnParity.importedConstraints,
      ColumnParity.importedConstraintsDelegationColumns,
      FlatOperation.constraints, Expression.eval, Verification.environment,
      sub_eq_add_neg, Trace.timestampBase] at bit lower upper ⊢
    all_goals refine ⟨?_, ?_, ?_⟩
    all_goals first
      | simpa only [add_comm] using bit
      | solve | convert lower using 1; congr 1; ring
      | solve | convert upper using 1; congr 1; ring

private theorem column_parity_cached_clock_index {port : TimestampPort}
    (member : port ∈ ColumnParityCached.importedConstraintsDelegationColumns.ports) :
    ∃ i : Fin 14,
      port = ColumnParityCached.importedConstraintsDelegationColumns.ports[i.val] := by
  obtain ⟨i, bound, equal⟩ := Array.mem_iff_getElem.mp member
  change i < 14 at bound
  exact ⟨⟨i, bound⟩, equal.symm⟩

theorem column_parity_cached_clock_facts {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ColumnParityCached.clockConstraints setup)) :
    Delegation.Proofs.ClockFacts
      ColumnParityCached.importedConstraintsDelegationColumns w := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (ColumnParityCached.importedConstraints setup)
      ColumnParityCached.importedConstraintsTimestampLookups)
  have timestamps := Verification.holds_of_sublist h
    (List.sublist_append_right (ColumnParityCached.importedConstraints setup)
      ColumnParityCached.importedConstraintsTimestampLookups)
  refine ⟨?_, ?_⟩
  · intro port member
    obtain ⟨i, rfl⟩ := column_parity_cached_clock_index member
    fin_cases i <;> decide
  · intro port member
    obtain ⟨i, rfl⟩ := column_parity_cached_clock_index member
    have bit := Verification.assertion_of_holds core
      ⟨6 + i.val, by simp [ColumnParityCached.importedConstraints, FlatOperation.constraints]; omega⟩
    have timestampCount :
        (FlatOperation.lookups (ColumnParityCached.importedConstraintsTimestampLookups
          (p := p))).length = 30 := by rfl
    have lowerLookup := Verification.lookup_of_holds timestamps
      ⟨1 + 2 * i.val, by rw [timestampCount]; omega⟩
    have upperLookup := Verification.lookup_of_holds timestamps
      ⟨2 + 2 * i.val, by rw [timestampCount]; omega⟩
    fin_cases i
    all_goals have lower := Trace.Proofs.range_bound lowerLookup
    all_goals have upper := Trace.Proofs.range_bound upperLookup
    all_goals simp [ColumnParityCached.importedConstraints,
      ColumnParityCached.importedConstraintsDelegationColumns,
      FlatOperation.constraints, Expression.eval, Verification.environment,
      sub_eq_add_neg, Trace.timestampBase] at bit lower upper ⊢
    all_goals refine ⟨?_, ?_, ?_⟩
    all_goals first
      | simpa only [add_comm] using bit
      | solve | convert lower using 1; congr 1; ring
      | solve | convert upper using 1; congr 1; ring

end Airbender.Keccak.Split.Proofs
