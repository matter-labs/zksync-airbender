import Tests.ShiftRoutingQueries

namespace Tests.ShiftRoutingPart1
open Airbender Verification ShiftBinop Trace Tests.ShiftRoutingWitness
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem constraints_4 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨4, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨4, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨4, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨4, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨4, by decide⟩ ⟨3, by decide⟩

private theorem constraints_5 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨5, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨5, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨5, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨5, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨5, by decide⟩ ⟨3, by decide⟩

private theorem constraints_6 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨6, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨6, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨6, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨6, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨6, by decide⟩ ⟨3, by decide⟩

private theorem constraints_7 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨7, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨7, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨7, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨7, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨7, by decide⟩ ⟨3, by decide⟩

theorem native_constraints (sample : Fin 4) :
    FlatOperation.ConstraintsHoldFlat
      (environment (assignment ⟨4 + sample.val, by have := sample.isLt; omega⟩))
      ShiftBinop.importedConstraints := by
  fin_cases sample
  · exact constraints_4
  · exact constraints_5
  · exact constraints_6
  · exact constraints_7

end Tests.ShiftRoutingPart1
