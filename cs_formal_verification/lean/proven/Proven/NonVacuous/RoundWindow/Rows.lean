module
public import Proven.NonVacuous.RoundWindow.Model

@[expose] public section
namespace Airbender.NonVacuous.RoundWindow
open Trace HashCallers
set_option warningAsError true
local notation "P" => babyBearModulus

/-- The CSR column is outside the ADD/SUB equations. -/
theorem unrolled_asserts (pc clock previous : Nat) :
    ∀ index (bound : index < (FlatOperation.constraints (AddSub.importedConstraints (p := P))).length),
      ((FlatOperation.constraints (AddSub.importedConstraints (p := P))).get ⟨index, bound⟩).eval
        (Verification.environment (unrolledAssignment pc clock previous)) = 0 := by
  intro index bound
  have equal :
      ((FlatOperation.constraints (AddSub.importedConstraints (p := P))).get ⟨index, bound⟩).eval
          (Verification.environment (unrolledAssignment pc clock previous)) =
      ((FlatOperation.constraints (AddSub.importedConstraints (p := P))).get ⟨index, bound⟩).eval
          (Verification.environment (PooledRow.assignment pc clock previous)) := by
    have small : index < 30 := by rwa [AddSub.constraint_count] at bound
    interval_cases index <;> op_index <;> rfl
  exact equal.trans (PooledRow.asserts pc clock previous index bound)

/-- The CSR column is outside the ADD/SUB range queries. -/
theorem unrolled_lookups {pc clock previous : Nat} (valid : PooledRow.Valid pc clock previous) :
    ∀ index (bound : index < (FlatOperation.lookups (AddSub.importedConstraints (p := P))).length),
      ((FlatOperation.lookups (AddSub.importedConstraints (p := P))).get ⟨index, bound⟩).Contains
        (Verification.environment (unrolledAssignment pc clock previous)) := by
  intro index bound
  have equal :
      ((FlatOperation.lookups (AddSub.importedConstraints (p := P))).get ⟨index, bound⟩).Contains
          (Verification.environment (unrolledAssignment pc clock previous)) =
      ((FlatOperation.lookups (AddSub.importedConstraints (p := P))).get ⟨index, bound⟩).Contains
          (Verification.environment (PooledRow.assignment pc clock previous)) := by
    have small : index < 6 := by rwa [AddSub.lookup_count] at bound
    interval_cases index <;> op_index <;>
      simp only [Lookup.Contains] <;> congr 1 <;> apply Vector.ext <;> intro slot bound <;>
      have zero : slot = 0 := by have : slot < 1 := bound; omega
    all_goals subst slot; simp only [Vector.getElem_map]; rfl
  rw [equal]
  exact PooledRow.lookups valid index bound

/-- The CSR column is outside the ADD/SUB timestamp queries. -/
theorem unrolled_timestamps {pc clock previous : Nat} (valid : PooledRow.Valid pc clock previous) :
    ∀ index (bound : index < (FlatOperation.lookups (AddSub.importedConstraintsTimestampLookups (p := P))).length),
      ((FlatOperation.lookups (AddSub.importedConstraintsTimestampLookups (p := P))).get ⟨index, bound⟩).Contains
        (Verification.environment (unrolledAssignment pc clock previous)) := by
  intro index bound
  have equal :
      ((FlatOperation.lookups (AddSub.importedConstraintsTimestampLookups (p := P))).get ⟨index, bound⟩).Contains
          (Verification.environment (unrolledAssignment pc clock previous)) =
      ((FlatOperation.lookups (AddSub.importedConstraintsTimestampLookups (p := P))).get ⟨index, bound⟩).Contains
          (Verification.environment (PooledRow.assignment pc clock previous)) := by
    have small : index < 8 := by rwa [AddSub.timestamp_count] at bound
    interval_cases index <;> op_index <;>
      simp only [Lookup.Contains] <;> congr 1 <;> apply Vector.ext <;> intro slot bound <;>
      have zero : slot = 0 := by have : slot < 1 := bound; omega
    all_goals subst slot; simp only [Vector.getElem_map]; rfl
  rw [equal]
  exact PooledRow.timestamps valid index bound

/-- Every unrolled caller satisfies its equations and both lookup groups. -/
theorem unrolled_satisfies {pc clock previous : Nat} (valid : PooledRow.Valid pc clock previous) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (unrolledAssignment pc clock previous))
      (AddSub.clockConstraints (p := P)) := by
  refine Verification.holds_append (holds_of_get (unrolled_asserts pc clock previous) (unrolled_lookups valid))
    (holds_of_get (fun index bound => ?_) (unrolled_timestamps valid))
  have empty : FlatOperation.constraints (AddSub.importedConstraintsTimestampLookups (p := P)) = [] := rfl
  rw [empty] at bound
  exact absurd bound (Nat.not_lt_zero index)

/-- Each submitted unrolled row has an index below ten. -/
theorem unrolled_mem_rows {row : Row P PooledFamily} (member : row ∈ unrolledRows) :
    ∃ index < 10, row = unrolledRow index := by
  change row ∈ (List.range 10).map unrolledRow at member
  obtain ⟨index, present, rfl⟩ := List.mem_map.mp member
  exact ⟨index, List.mem_range.mp present, rfl⟩

/-- PCs, clocks and the preceding x0 write remain in range. -/
theorem unrolled_valid {index : Nat} (bound : index < 10) :
    PooledRow.Valid (4 * index) (4 + 4 * index) (previousOf 0 4 index) := by
  refine ⟨by omega, by simp only [timestampBase]; omega, ?_⟩
  unfold previousOf
  split <;> omega

/-- Caller rows participate in the CPU and request arguments. -/
theorem unrolled_active (index : Nat) :
    (unrolledRow index).assignment (unrolledRow index).columns.execute = 1 := by rfl

theorem unrolled_selected (index : Nat) : Delegation.Requests.Selected (unrolledRow index).assignment := by rfl

/-- The two architectural transfers are the x0 chain's exact edges. -/
theorem unrolled_steps (index : Nat) :
    Delegation.Caller.architecturalSteps (unrolledRow index).assignment =
      x0Edges (previousOf 0 4 index) (4 + 4 * index) := by
  have equal : Delegation.Caller.architecturalSteps (unrolledRow index).assignment =
      Delegation.Caller.architecturalSteps
        (PooledRow.row (4 * index) (4 + 4 * index) (previousOf 0 4 index)).assignment := rfl
  exact equal.trans (PooledRow.steps ..)

end Airbender.NonVacuous.RoundWindow
