import Human.Circuits.Blake2Round.Tables.Setup
import Human.Circuits.Blake2Round.Artifact
import Human.Helpers.Properties

namespace Airbender.Blake2Round.Addresses
open Arithmetic

structure Input where
  statePointer : Word
  messagePointer : Word

abbrev Output := Vector (BitVec 32) 40

/-- JSON order: 24 state words, then 16 message words, at four-byte intervals. -/
def expected (input : Input) : Output := Vector.ofFn fun i =>
  if i.val < 24 then input.statePointer.toBitVec + BitVec.ofNat 32 (4 * i.val)
  else input.messagePointer.toBitVec + BitVec.ofNat 32 (4 * (i.val - 24))

def spec (input : Input) (output : Output) : Prop := output = expected input

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
