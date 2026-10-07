import Airbender.Review.Blake2G.Addresses
import Airbender.Review.Blake2G.State

namespace Airbender.Blake2G.Row
open Arithmetic

structure Input where
  controller : Control.Input
  statePointer : Word
  messagePointer : Word
  state : Vector Word 16
  message : Vector Word 16

structure Output where
  controller : Control.Output
  state : Vector Word 16
  addresses : Addresses.Output

/-- The controller lookup proves these indices are below sixteen, so the total
    `Fin.ofNat` conversion is exact. Both message reads use the selected schedule. -/
def stateInput (input : Input) (controller : Control.Output) : State.Input :=
  ⟨input.state, controller.stateOffsets.map (Fin.ofNat 16),
    input.message[Fin.ofNat 16 controller.messageOffsets[0]],
    input.message[Fin.ofNat 16 controller.messageOffsets[1]]⟩

def addressInput (input : Input) : Addresses.Input :=
  ⟨input.controller, input.statePointer, input.messagePointer⟩

/-- One row updates x12, applies Clean's G to the scheduled state/message words,
    and selects the six byte addresses described by the imported memory ports. -/
def spec (input : Input) (output : Output) : Prop :=
  Control.spec input.controller output.controller ∧
  State.spec (stateInput input output.controller) output.state ∧
  Addresses.spec (addressInput input) output.addresses

/-- Observable bindings to one witness. These name ports and values; they do
    not assume that the controller, G computation, or address arithmetic is correct. -/
structure Mapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  controller : Control.Mapping input.controller output.controller w
  statePointer : input.statePointer = ⟨(w 13).val, (w 14).val⟩
  messagePointer : input.messagePointer = ⟨(w 31).val, (w 32).val⟩
  words : WordMapping (State.mixingInput (stateInput input output.controller))
    (State.mixingOutput (stateInput input output.controller) output.state) w
  addresses : output.addresses = importedConstraintsIndirectPorts.map (fun port => port.address w)

/-- Active rows only. The memory interface supplies bounded pointers, the four
    remaining mixing-input bounds, port reads/writes, and preservation of other
    lanes. Control/selector correctness, alignment and G results are proved. -/
structure InterfaceAssumptions {p : Nat} (input : Input) (output : Output)
    (w : Nat → ZMod p) : Prop where
  active : input.controller.active = true
  pointers : input.statePointer.Bounded ∧ input.messagePointer.Bounded
  inputs : Blake2G.InterfaceAssumptions (State.mixingInput (stateInput input output.controller))
    (State.mixingOutput (stateInput input output.controller) output.state) w
  untouched : ∀ i : Fin 16,
    (∀ j : Fin 4, i ≠ (stateInput input output.controller).lanes[j]) → output.state[i] = input.state[i]

def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints (setupTable Control.controllerRows))
  represents := Mapping

end Airbender.Blake2G.Row
