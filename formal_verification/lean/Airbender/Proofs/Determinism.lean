import Airbender.Review.Properties

namespace Airbender.Properties

/-- Shared composition rule: soundness against a single-valued reference relation
    gives observable circuit determinism, for arbitrary witness types. -/
theorem determinism_of_soundness {Input Output Witness : Type}
    {circuit : Input → Output → Witness → Prop} {spec : Input → Output → Prop}
    (sound : Soundness circuit spec)
    (unique : ∀ input left right, spec input left → spec input right → left = right) :
    Determinism circuit := by
  intro input left right wl wr hl hr
  exact unique input left right (sound input left wl hl) (sound input right wr hr)

/-- The same rule when the reference relation is single-valued only on valid
    outputs, such as bounded limb encodings. Validity must follow from the circuit
    and its explicit contracts; it is not assumed for arbitrary outputs. -/
theorem determinism_of_soundness_on {Input Output Witness : Type}
    {circuit : Input → Output → Witness → Prop} {spec : Input → Output → Prop}
    (valid : Input → Output → Prop)
    (sound : Soundness circuit spec)
    (outputs_valid : ∀ input output witness, circuit input output witness → valid input output)
    (unique : ∀ input left right, valid input left → valid input right →
      spec input left → spec input right → left = right) : Determinism circuit :=
  determinism_of_soundness (spec := fun input output => valid input output ∧ spec input output)
    (fun input output witness h => ⟨outputs_valid input output witness h,
      sound input output witness h⟩)
    (fun input left right hl hr => unique input left right hl.1 hr.1 hl.2 hr.2)

end Airbender.Properties
