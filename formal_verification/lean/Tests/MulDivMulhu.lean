import Tests.MulDivWitness

namespace Tests.MulDivMulhu
open Airbender Arithmetic MulDiv Verification Tests.MulDivWitness

private theorem constraints_0 (discarded : Bool) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment .mulhu 0 discarded))
      MulDiv.importedConstraints := by
  cases discarded <;>
    simp [MulDiv.importedConstraints,FlatOperation.ConstraintsHoldFlat,Expression.eval,
      environment,assignment,witnessValues]
  all_goals repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) |
    (apply byte_query_contains <;> decide) |
    decide

private theorem constraints_1 (discarded : Bool) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment .mulhu 1 discarded))
      MulDiv.importedConstraints := by
  cases discarded <;>
    simp [MulDiv.importedConstraints,FlatOperation.ConstraintsHoldFlat,Expression.eval,
      environment,assignment,witnessValues]
  all_goals repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) |
    (apply byte_query_contains <;> decide) |
    decide

private theorem constraints_2 (discarded : Bool) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment .mulhu 2 discarded))
      MulDiv.importedConstraints := by
  cases discarded <;>
    simp [MulDiv.importedConstraints,FlatOperation.ConstraintsHoldFlat,Expression.eval,
      environment,assignment,witnessValues]
  all_goals repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) |
    (apply byte_query_contains <;> decide) |
    decide

private theorem constraints_3 (discarded : Bool) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment .mulhu 3 discarded))
      MulDiv.importedConstraints := by
  cases discarded <;>
    simp [MulDiv.importedConstraints,FlatOperation.ConstraintsHoldFlat,Expression.eval,
      environment,assignment,witnessValues]
  all_goals repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) |
    (apply byte_query_contains <;> decide) |
    decide

private theorem constraints_4 (discarded : Bool) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment .mulhu 4 discarded))
      MulDiv.importedConstraints := by
  cases discarded <;>
    simp [MulDiv.importedConstraints,FlatOperation.ConstraintsHoldFlat,Expression.eval,
      environment,assignment,witnessValues]
  all_goals repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) |
    (apply byte_query_contains <;> decide) |
    decide

/-- Ten accepted full native rows, including actual x0 writes. -/
theorem native_constraints (sample : Fin 5) (discarded : Bool) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment .mulhu sample discarded))
      MulDiv.importedConstraints := by
  fin_cases sample
  · exact constraints_0 discarded
  · exact constraints_1 discarded
  · exact constraints_2 discarded
  · exact constraints_3 discarded
  · exact constraints_4 discarded

/-- Nonvacuous applications of the public numerical theorem, retaining the
    selected result and the circuit's actual masked destination write. -/
theorem native_results (sample : Fin 5) (discarded : Bool) :
    let w := assignment .mulhu sample discarded
    (selectedWord w).value = Operation.result .mulhu (left w) (right w) ∧
      (writtenWord w).value = if discarded then 0 else Operation.result .mulhu (left w) (right w) := by
  apply native_unsigned_result (assignment .mulhu sample discarded) .mulhu discarded
    (native_constraints sample discarded)
  · fin_cases sample <;> cases discarded <;> decide
  · fin_cases sample <;> cases discarded <;> constructor <;> decide
  · cases discarded <;> rfl

/-- Corrupting the actual write is rejected even when the selected arithmetic
    value is unchanged. -/
theorem altered_write_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat
      (environment (fun i => if i = 60 then 1 else assignment .mulhu 1 true i))
      MulDiv.importedConstraints := by
  intro holds
  have wrong := assertion_of_holds holds ⟨35,by rw [MulDiv.Proofs.constraint_count]; decide⟩
  revert wrong
  decide

end Tests.MulDivMulhu
