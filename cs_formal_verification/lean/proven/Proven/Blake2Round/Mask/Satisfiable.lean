module
public import Proven.Blake2Round.Mask.WitnessLookups
public import Proven.Blake2Round.Mask.WitnessClockValues
public import Proven.Blake2Round.Mask.WitnessReads

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic
set_option maxRecDepth 32768

/-- The zero-mask assignment also meets every native timestamp lookup. -/
theorem zero_clocks : FlatOperation.ConstraintsHoldFlat (Verification.environment zeroAssignment)
    (clockConstraints setupTable) := by
  apply Verification.holds_append zero_holds
  apply NonVacuous.holds_of_get
  · intro i bound
    have empty : FlatOperation.constraints (importedConstraintsTimestampLookups (p := babyBearModulus)) = [] := rfl
    rw [empty] at bound
    exact absurd bound (Nat.not_lt_zero i)
  · intro i bound
    have old := NonVacuous.Blake2RoundSpan.timestamps (p := babyBearModulus) rfl zeroSource_valid i bound
    have same := zero_timestamp_values ⟨i, by rwa [timestamp_count] at bound⟩
    dsimp only at same
    unfold Lookup.Contains at old ⊢
    rw [same]
    exact old

/-- An active zero-mask row meets all equations, lookups, source bounds and port mappings. -/
theorem satisfiable : SatisfiableClaim :=
  ⟨inputOf zeroAssignment, outputOf zeroAssignment, zeroAssignment,
    native_assumptions zero_reads, zero_holds, native_mapping zero_holds, zero_rounds⟩

end Airbender.Blake2Round.Mask.Proofs
