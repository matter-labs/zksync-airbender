import Airbender.Proofs.GKRProtocol.CanonicalHelpers

namespace Airbender.Compiler.Source
set_option warningAsError true

/-- Override only the explicitly allocated compiler-borrow coordinates. -/
noncomputable def assignBorrows (slots : Fin k → Fin n) (values : Fin n → BaseField)
    (borrows : Fin k → BaseField) (index : Fin n) : BaseField :=
  if found : ∃ borrow, slots borrow = index then borrows found.choose else values index

theorem assignBorrows_at (slots : Fin k → Fin n) (unique : Function.Injective slots)
    (values : Fin n → BaseField) (borrows : Fin k → BaseField) (index : Fin k) :
    assignBorrows slots values borrows (slots index) = borrows index := by
  classical
  unfold assignBorrows
  split_ifs with found
  · exact congrArg borrows (unique found.choose_spec)
  · exact False.elim (found ⟨index, rfl⟩)

theorem assignBorrows_frame (slots : Fin k → Fin n) (values : Fin n → BaseField)
    (borrows : Fin k → BaseField) (index : Fin n) (outside : ∀ borrow, slots borrow ≠ index) :
    assignBorrows slots values borrows index = values index := by
  classical
  unfold assignBorrows
  exact dif_neg (by simpa only [not_exists] using outside)

end Airbender.Compiler.Source
