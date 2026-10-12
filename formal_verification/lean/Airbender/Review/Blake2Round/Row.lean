import Airbender.Review.Blake2Round.Addresses
import Airbender.Review.Blake2Round.Schedule
import Airbender.Review.Blake2Round.Finalization

namespace Airbender.Blake2Round.Row
open Arithmetic

structure Input where
  controller : Word
  round : Fin 10
  reducedRounds : Bool
  compression : Bool
  inputIsRight : Bool
  statePointer : Word
  messagePointer : Word
  state : Vector Word 8
  extended : Vector Word 16
  message : Vector Word 16

structure Output where
  controller : Word
  state : Vector Word 8
  extended : Vector Word 16
  addresses : Addresses.Output

def preparationInput (input : Input) : Preparation.Input :=
  ⟨input.round == 0, input.compression, input.inputIsRight,
    input.state, input.extended, input.message⟩

/-- One local row prepares and schedules its inputs, applies Clean's eight-G
    round, writes both state blocks, advances x12 and computes all forty addresses.
    Port transport and the surrounding hash call sequence are separate obligations. -/
def spec (input : Input) (output : Output) : Prop :=
  let prepared := Preparation.step (preparationInput input)
  Control.spec input.controller output.controller ∧
  Mixing.spec ⟨prepared.extended, Schedule.step ⟨input.round, prepared.message⟩⟩ output.extended ∧
  Finalization.spec ⟨input.round, input.reducedRounds, input.state,
    prepared.chaining, output.extended⟩ output.state ∧
  Addresses.spec ⟨input.statePointer, input.messagePointer⟩ output.addresses

/-- Observable values are bound to the same imported row, including its actual
    read/write ports. No internal preparation or mixing result is assumed. -/
structure Mapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  controller : Control.Mapping input.controller output.controller w
  statePointer : input.statePointer = ⟨(w 3).val, (w 4).val⟩
  messagePointer : input.messagePointer = ⟨(w 101).val, (w 102).val⟩
  reduced : w 139 = if input.reducedRounds then 1 else 0
  compression : w 141 = if input.compression then 1 else 0
  inputIsRight : w 140 = if input.inputIsRight then 1 else 0
  state : input.state = Preparation.words w Variables.stateReads
  extended : input.extended = Preparation.words w Variables.extendedReads
  message : input.message = Preparation.words w Variables.messageReads
  stateOutput : output.state = Preparation.words w Finalization.stateWrites
  extendedOutput : output.extended = Preparation.words w Mixing.extendedWrites
  addresses : output.addresses = importedConstraintsIndirectPorts.map (fun port => port.address w)

/-- The caller selects one round and supplies bounded source words and pointers.
    Internal values, output bounds, pointer alignment and address carries are proved
    from the native equations and queries. Setup provenance remains external. -/
structure InterfaceAssumptions {p : Nat} (input : Input) (_output : Output)
    (w : Nat → ZMod p) : Prop where
  roundMask : Control.RoundMask w input.round
  pointers : input.statePointer.Bounded ∧ input.messagePointer.Bounded
  state : ∀ i : Fin 8, input.state[i].Bounded
  extended : ∀ i : Fin 16, input.extended[i].Bounded
  message : ∀ i : Fin 16, input.message[i].Bounded

def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints setupTable)
  represents := Mapping

end Airbender.Blake2Round.Row
