import GKRCompiler.Forward

namespace Airbender.Compiler
set_option warningAsError true

def Certificate.forwardOnly {translation : Translation n m F} (certificate : Certificate translation) :
    ForwardCertificate translation := ⟨certificate.forward⟩

theorem Certificate.forwardOnly_valid [CommRing F] [DecidableEq F]
    {translation : Translation n m F} {certificate : Certificate translation}
    (valid : certificate.Valid) : certificate.forwardOnly.Valid := ⟨valid.1, valid.2.2⟩

theorem Certificate.backward_of_valid [CommRing F] [DecidableEq F]
    {translation : Translation n m F} {certificate : Certificate translation}
    (valid : certificate.Valid) {values : Fin m → F} (holds : Satisfies translation.lowered values) :
    Satisfies translation.source (values ∘ translation.projection) := by
  intro relation member
  obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
  have same := equal_sound (valid.2.1 index) values
  rw [evaluate_rename] at same
  exact same.trans (combination_zero holds _)

theorem ArithmeticExtension.backward [CommRing F] [DecidableEq F] (artifact : ArithmeticExtension n m F)
    (certificate : Certificate artifact.translation) (valid : certificate.Valid)
    (gateChecks : artifact.gates.all ArithmeticGate.check = true)
    {values : Fin m → F} (holds : ∀ gate ∈ artifact.gates, gate.expressionResidual values = 0) :
    Satisfies artifact.source (values ∘ artifact.projection) := by
  apply Certificate.backward_of_valid valid
  intro relation member
  obtain ⟨gate, included, rfl⟩ := List.mem_map.mp member
  rw [gate.checked_value (List.all_eq_true.mp gateChecks gate included)]
  exact holds gate included

/-- Both directions cover every reconstructed native base-field relation. The
source includes the independently derived clock/borrow assertions; later
primitive-history composition discharges their forward obligations. -/
theorem ArithmeticExtension.equivalent [CommRing F] [DecidableEq F] (artifact : ArithmeticExtension n m F)
    (certificate : Certificate artifact.translation) (valid : certificate.Valid)
    (gateChecks : artifact.gates.all ArithmeticGate.check = true) (values : Fin n → F) :
    Satisfies artifact.source values ↔ ∃ extended : Fin m → F,
      (∀ wire, extended (artifact.projection wire) = values wire) ∧
      (∀ gate ∈ artifact.gates, gate.expressionResidual extended = 0) := by
  constructor
  · intro holds
    exact ⟨artifact.translation.extend values,
      artifact.forward certificate.forwardOnly (Certificate.forwardOnly_valid valid) gateChecks holds⟩
  · rintro ⟨extended, projection, holds⟩
    have same : extended ∘ artifact.projection = values := funext projection
    simpa only [same] using artifact.backward certificate valid gateChecks holds

end Airbender.Compiler
