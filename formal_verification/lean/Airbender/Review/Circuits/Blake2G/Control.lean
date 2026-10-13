import Airbender.Review.Circuits.Blake2G.Tables.Controller

namespace Airbender.Blake2G.Control

/-- Canonical decoding of the control register and the six imported offset columns.
    Input's eight-bit type is the ABI input bound; memory transport supplies it. -/
structure Mapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  inputRegister : input.register.val = (w Variables.controlReadLo).val
  execute : w Variables.execute = if input.active then 1 else 0
  outputs : output = ⟨⟨(w Variables.controlWriteLo).val, (w Variables.controlWriteHi).val⟩,
    Variables.stateOffsetColumns.map (fun column => (w column).val),
    Variables.messageOffsetColumns.map (fun column => (w column).val)⟩

def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints (setupTable controllerRows))
  represents := Mapping

end Airbender.Blake2G.Control
