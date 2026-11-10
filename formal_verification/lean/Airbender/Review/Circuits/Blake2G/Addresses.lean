import Airbender.Review.Circuits.Blake2G.Control

namespace Airbender.Blake2G.Addresses
open Arithmetic

structure Input where
  controller : Control.Input
  statePointer : Word
  messagePointer : Word

abbrev Output := Vector (BitVec 32) 6

/-- State ports first, then message ports, in actual JSON order. Indices from
    the controller reference select words within each 16-word ABI block. -/
def expected (input : Input) : Output :=
  let row := Control.step input.controller
  #v[input.statePointer.toBitVec + BitVec.ofNat 32 (4 * row.stateOffsets[0]),
    input.statePointer.toBitVec + BitVec.ofNat 32 (4 * row.stateOffsets[1]),
    input.statePointer.toBitVec + BitVec.ofNat 32 (4 * row.stateOffsets[2]),
    input.statePointer.toBitVec + BitVec.ofNat 32 (4 * row.stateOffsets[3]),
    input.messagePointer.toBitVec + BitVec.ofNat 32 (4 * row.messageOffsets[0]),
    input.messagePointer.toBitVec + BitVec.ofNat 32 (4 * row.messageOffsets[1])]

def spec (input : Input) (output : Output) : Prop := output = expected input

/-- Canonical ABI inputs and the address projection of imported port metadata.
    This does not assert that a global memory argument enforces those ports. -/
structure Mapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  controlRegister : input.controller.register.val = (w Variables.controlReadLo).val
  execute : w Variables.execute = if input.controller.active then 1 else 0
  statePointer : input.statePointer = ⟨(w 13).val, (w 14).val⟩
  messagePointer : input.messagePointer = ⟨(w 31).val, (w 32).val⟩
  addresses : output = importedConstraintsIndirectPorts.map (fun port => port.address w)

/-- Pointer limb bounds come from the surrounding register/memory interface.
    Alignment and selected-index bounds follow from the imported lookups. -/
def InterfaceAssumptions (input : Input) (_output : Output) (_w : Nat → ZMod p) : Prop :=
  input.statePointer.Bounded ∧ input.messagePointer.Bounded

def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints (setupTable Control.controllerRows))
  represents := Mapping

end Airbender.Blake2G.Addresses
