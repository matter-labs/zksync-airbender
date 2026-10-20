import Tests.ShiftRoutingQueries

namespace Tests.ShiftRoutingPart3
open Airbender Verification ShiftBinop Trace Tests.ShiftRoutingWitness
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem constraints_12 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨12, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨12, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨12, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨12, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨12, by decide⟩ ⟨3, by decide⟩

private theorem constraints_13 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨13, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨13, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨13, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨13, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨13, by decide⟩ ⟨3, by decide⟩

private theorem constraints_14 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨14, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨14, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨14, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨14, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨14, by decide⟩ ⟨3, by decide⟩

private theorem constraints_15 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨15, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨15, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨15, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨15, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨15, by decide⟩ ⟨3, by decide⟩

theorem native_constraints (sample : Fin 4) :
    FlatOperation.ConstraintsHoldFlat
      (environment (assignment ⟨12 + sample.val, by have := sample.isLt; omega⟩))
      ShiftBinop.importedConstraints := by
  fin_cases sample
  · exact constraints_12
  · exact constraints_13
  · exact constraints_14
  · exact constraints_15

end Tests.ShiftRoutingPart3
