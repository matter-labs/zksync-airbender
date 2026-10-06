import Clean.Circuit.Operations

namespace Airbender.Properties

/-- Every satisfying witness gives an observable transition allowed by the spec. -/
def Soundness {Input Output Witness : Type} (circuit : Input → Output → Witness → Prop)
    (spec : Input → Output → Prop) : Prop :=
  ∀ input output witness, circuit input output witness → spec input output

/-- Every permitted transition has a satisfying witness. -/
def Completeness {Input Output Witness : Type} (circuit : Input → Output → Witness → Prop)
    (spec : Input → Output → Prop) : Prop :=
  ∀ input output, spec input output → ∃ witness, circuit input output witness

/-- Observable outputs are unique for fixed inputs (including any external inputs). -/
def Determinism {Input Output Witness : Type}
    (circuit : Input → Output → Witness → Prop) : Prop :=
  ∀ input left right wl wr,
    circuit input left wl → circuit input right wr → left = right

end Airbender.Properties

namespace Airbender.Verification

/-- Interpretation of a circuit artifact. Interface assumptions are deliberately
    separate from constraints and the observable-variable mapping. -/
structure CircuitModel (Input Output Witness : Type) where
  satisfies : Witness → Prop
  represents : Input → Output → Witness → Prop

namespace CircuitModel

/-- Observables connected to an assignment satisfying the imported constraints.
    This relation contains no external interface assumptions. -/
def relation {Input Output Witness : Type} (model : CircuitModel Input Output Witness)
    (input : Input) (output : Output) (witness : Witness) : Prop :=
  model.satisfies witness ∧ model.represents input output witness

/-- Shared soundness, with explicit interface conditions on the circuit relation. -/
def SoundnessUnder {Input Output Witness : Type} (model : CircuitModel Input Output Witness)
    (assumptions : Input → Output → Witness → Prop) (spec : Input → Output → Prop) : Prop :=
  Properties.Soundness (fun i o w => assumptions i o w ∧ model.relation i o w) spec

/-- Shared observable determinism under the same interface conditions. -/
def DeterminismUnder {Input Output Witness : Type} (model : CircuitModel Input Output Witness)
    (assumptions : Input → Output → Witness → Prop) : Prop :=
  Properties.Determinism (fun i o w => assumptions i o w ∧ model.relation i o w)

end CircuitModel

/-- Lift a variable assignment into Clean's environment. The imported arithmetic
    assertions do not use external table data. -/
def environment {F : Type} (w : Nat → F) : _root_.Environment F where
  get := w
  data := fun _ _ => #[]

end Airbender.Verification
