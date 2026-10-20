import Tests.ShiftRoutingQueries

namespace Tests.ShiftRoutingPart2
open Airbender Verification ShiftBinop Trace Tests.ShiftRoutingWitness
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem constraints_8 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨8, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨8, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨8, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨8, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨8, by decide⟩ ⟨3, by decide⟩

private theorem constraints_9 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨9, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨9, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨9, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨9, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨9, by decide⟩ ⟨3, by decide⟩

private theorem constraints_10 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨10, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨10, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨10, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨10, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨10, by decide⟩ ⟨3, by decide⟩

private theorem constraints_11 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨11, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨11, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨11, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨11, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨11, by decide⟩ ⟨3, by decide⟩

theorem native_constraints (sample : Fin 4) :
    FlatOperation.ConstraintsHoldFlat
      (environment (assignment ⟨8 + sample.val, by have := sample.isLt; omega⟩))
      ShiftBinop.importedConstraints := by
  fin_cases sample
  · exact constraints_8
  · exact constraints_9
  · exact constraints_10
  · exact constraints_11

end Tests.ShiftRoutingPart2
