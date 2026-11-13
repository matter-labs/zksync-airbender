module
public import Human.Circuits.Blake2Round.Tables.Setup
public import Human.Circuits.Blake2Round.Artifact
public import Human.Helpers.Properties
public import Human.Circuits.Blake2Round.Addresses

/-! Definitions only the proofs use, moved from `human/Human/Circuits/Blake2Round/Addresses.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Blake2Round.Addresses
open Arithmetic
/-- Pointer words and address projections of actual imported metadata.
    This describes the ports; it does not prove global memory enforcement. -/
structure Mapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  statePointer : input.statePointer = ⟨(w 3).val, (w 4).val⟩
  messagePointer : input.messagePointer = ⟨(w 101).val, (w 102).val⟩
  addresses : output = importedConstraintsIndirectPorts.map (fun port => port.address w)
/-- Pointer bounds come from surrounding register/memory interfaces; alignment
    and absence of low-limb carry follow from imported queries. -/
def InterfaceAssumptions (input : Input) (_output : Output) (_w : Nat → ZMod p) : Prop :=
  input.statePointer.Bounded ∧ input.messagePointer.Bounded
def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints setupTable)
  represents := Mapping
end Airbender.Blake2Round.Addresses
