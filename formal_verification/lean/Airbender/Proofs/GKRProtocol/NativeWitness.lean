import Airbender.Proofs.GKRProtocol.BaseEncoding

namespace Airbender.Compiler
set_option warningAsError true

/-- An actual native graph assignment with consistent base roles has exactly
its original values after the consumer's base/extension interpretation. -/
theorem TypedAssignment.value_eq {R : Type} [CommRing R]
    (assignment : TypedAssignment R) (typing : ConsumerTyping) (hom : Source.BaseField →+* R)
    (baseLaw : ∀ address, typing.compatible (address, .base) = true →
      assignment.extension address = hom (assignment.base address)) :
    assignment.value typing hom = assignment.extension := by
  funext address
  unfold value
  split_ifs with base
  · exact (baseLaw address base).symm
  · rfl

end Airbender.Compiler
