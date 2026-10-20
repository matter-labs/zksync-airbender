import Tests.ShiftRoutingQueries

namespace Tests.ShiftRoutingPart0
open Airbender Verification ShiftBinop Trace Tests.ShiftRoutingWitness
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem constraints_0 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨0, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨0, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨0, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨0, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨0, by decide⟩ ⟨3, by decide⟩

private theorem constraints_1 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨1, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨1, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨1, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨1, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨1, by decide⟩ ⟨3, by decide⟩

private theorem constraints_2 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨2, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨2, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨2, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨2, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨2, by decide⟩ ⟨3, by decide⟩

private theorem constraints_3 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨3, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨3, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨3, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨3, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨3, by decide⟩ ⟨3, by decide⟩

theorem native_constraints (sample : Fin 4) :
    FlatOperation.ConstraintsHoldFlat
      (environment (assignment ⟨0 + sample.val, by have := sample.isLt; omega⟩))
      ShiftBinop.importedConstraints := by
  fin_cases sample
  · exact constraints_0
  · exact constraints_1
  · exact constraints_2
  · exact constraints_3

end Tests.ShiftRoutingPart0
