import Tests.ShiftRouting
import Airbender.Review.Trace.Families.ShiftBinop.History

namespace Tests.ShiftHistoryRows
open Airbender Verification ShiftBinop Tests.ShiftRoutingWitness
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Immediate x0 destinations read the timestamp refreshed by the second port.
    All other native columns and all four dynamic queries are unchanged. -/
def assignment (sample : Fin 24) (column : Nat) : ZMod mersenne31Modulus :=
  if 18 ≤ sample.val ∧ column = 71 then 5 else ShiftRoutingWitness.assignment sample column

private theorem constraints_18 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨18, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, ShiftRoutingWitness.assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨18, by decide⟩ ⟨0, by decide⟩
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨18, by decide⟩ ⟨1, by decide⟩
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨18, by decide⟩ ⟨2, by decide⟩
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨18, by decide⟩ ⟨3, by decide⟩

private theorem constraints_19 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨19, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, ShiftRoutingWitness.assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨19, by decide⟩ ⟨0, by decide⟩
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨19, by decide⟩ ⟨1, by decide⟩
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨19, by decide⟩ ⟨2, by decide⟩
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨19, by decide⟩ ⟨3, by decide⟩

private theorem constraints_20 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨20, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, ShiftRoutingWitness.assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨20, by decide⟩ ⟨0, by decide⟩
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨20, by decide⟩ ⟨1, by decide⟩
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨20, by decide⟩ ⟨2, by decide⟩
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨20, by decide⟩ ⟨3, by decide⟩

private theorem constraints_21 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨21, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, ShiftRoutingWitness.assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨21, by decide⟩ ⟨0, by decide⟩
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨21, by decide⟩ ⟨1, by decide⟩
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨21, by decide⟩ ⟨2, by decide⟩
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨21, by decide⟩ ⟨3, by decide⟩

private theorem constraints_22 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨22, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, ShiftRoutingWitness.assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨22, by decide⟩ ⟨0, by decide⟩
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨22, by decide⟩ ⟨1, by decide⟩
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨22, by decide⟩ ⟨2, by decide⟩
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨22, by decide⟩ ⟨3, by decide⟩

private theorem constraints_23 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨23, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, ShiftRoutingWitness.assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨23, by decide⟩ ⟨0, by decide⟩
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨23, by decide⟩ ⟨1, by decide⟩
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨23, by decide⟩ ⟨2, by decide⟩
  · apply tagged_query_contains
    simpa [Expression.eval, environment, assignment] using
      ShiftRoutingQueries.lookup_members ⟨23, by decide⟩ ⟨3, by decide⟩

/-- Every native equation and lookup holds for all twelve forms and x0 variants,
    with alias clocks suitable for initialized native memory matching. -/
theorem native_constraints (sample : Fin 24) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment sample))
      ShiftBinop.importedConstraints := by
  fin_cases sample
  · exact ShiftRouting.native_constraints ⟨0, by decide⟩
  · exact ShiftRouting.native_constraints ⟨1, by decide⟩
  · exact ShiftRouting.native_constraints ⟨2, by decide⟩
  · exact ShiftRouting.native_constraints ⟨3, by decide⟩
  · exact ShiftRouting.native_constraints ⟨4, by decide⟩
  · exact ShiftRouting.native_constraints ⟨5, by decide⟩
  · exact ShiftRouting.native_constraints ⟨6, by decide⟩
  · exact ShiftRouting.native_constraints ⟨7, by decide⟩
  · exact ShiftRouting.native_constraints ⟨8, by decide⟩
  · exact ShiftRouting.native_constraints ⟨9, by decide⟩
  · exact ShiftRouting.native_constraints ⟨10, by decide⟩
  · exact ShiftRouting.native_constraints ⟨11, by decide⟩
  · exact ShiftRouting.native_constraints ⟨12, by decide⟩
  · exact ShiftRouting.native_constraints ⟨13, by decide⟩
  · exact ShiftRouting.native_constraints ⟨14, by decide⟩
  · exact ShiftRouting.native_constraints ⟨15, by decide⟩
  · exact ShiftRouting.native_constraints ⟨16, by decide⟩
  · exact ShiftRouting.native_constraints ⟨17, by decide⟩
  · exact constraints_18
  · exact constraints_19
  · exact constraints_20
  · exact constraints_21
  · exact constraints_22
  · exact constraints_23

end Tests.ShiftHistoryRows
