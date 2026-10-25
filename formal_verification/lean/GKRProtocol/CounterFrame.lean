import GKRProtocol.CanonicalSource

namespace Airbender.Compiler.Source
set_option warningAsError true

/-- Multiplicity columns are compiler witnesses, independently of logical
source columns, histories, and subtraction borrows. -/
noncomputable def assignCounters (slots : Fin k → Fin n) (values : Fin n → BaseField)
    (counts : Fin k → BaseField) : Fin n → BaseField := assignBorrows slots values counts

theorem assignCounters_at (slots : Fin k → Fin n) (unique : Function.Injective slots)
    (values : Fin n → BaseField) (counts : Fin k → BaseField) (index : Fin k) :
    assignCounters slots values counts (slots index) = counts index :=
  assignBorrows_at slots unique values counts index

theorem assignCounters_frame (slots : Fin k → Fin n) (values : Fin n → BaseField)
    (counts : Fin k → BaseField) (index : Fin n) (outside : ∀ counter, slots counter ≠ index) :
    assignCounters slots values counts index = values index := assignBorrows_frame slots values counts index outside

theorem assignCounters_satisfies (slots : Fin k → Fin n) (relations : List (Polynomial n BaseField))
    (checked : relations.all (erasureUntouched (List.ofFn slots)) = true)
    (values : Fin n → BaseField) (counts : Fin k → BaseField) (holds : Satisfies relations values) :
    Satisfies relations (assignCounters slots values counts) := by
  intro polynomial member
  exact (evaluate_assignBorrows_disjoint polynomial slots values counts
    (List.all_eq_true.mp checked polynomial member)).trans (holds polynomial member)

theorem HelperField.assignCounters_value (field : HelperField) (placement : HelperPlacement n)
    (slots : Fin k → Fin n)
    (checked : erasureUntouched (List.ofFn slots) (field.polynomial placement) = true)
    (values : Fin n → BaseField) (counts : Fin k → BaseField) :
    field.value (placement.project (assignCounters slots values counts)) = field.value (placement.project values) := by
  rw [← field.polynomial_value, ← field.polynomial_value]
  exact evaluate_assignBorrows_disjoint _ slots values counts checked

end Airbender.Compiler.Source
