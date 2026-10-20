import Tests.ShiftRoutingQueries

namespace Tests.ShiftRoutingPart4
open Airbender Verification ShiftBinop Trace Tests.ShiftRoutingWitness
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem constraints_16 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨16, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨16, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨16, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨16, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨16, by decide⟩ ⟨3, by decide⟩

private theorem constraints_17 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨17, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨17, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨17, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨17, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨17, by decide⟩ ⟨3, by decide⟩

private theorem constraints_18 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨18, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨18, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨18, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨18, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨18, by decide⟩ ⟨3, by decide⟩

private theorem constraints_19 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨19, by decide⟩))
      ShiftBinop.importedConstraints := by
  simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  · exact ShiftRoutingQueries.lookup_holds ⟨19, by decide⟩ ⟨0, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨19, by decide⟩ ⟨1, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨19, by decide⟩ ⟨2, by decide⟩
  · exact ShiftRoutingQueries.lookup_holds ⟨19, by decide⟩ ⟨3, by decide⟩

theorem native_constraints (sample : Fin 4) :
    FlatOperation.ConstraintsHoldFlat
      (environment (assignment ⟨16 + sample.val, by have := sample.isLt; omega⟩))
      ShiftBinop.importedConstraints := by
  fin_cases sample
  · exact constraints_16
  · exact constraints_17
  · exact constraints_18
  · exact constraints_19

end Tests.ShiftRoutingPart4
