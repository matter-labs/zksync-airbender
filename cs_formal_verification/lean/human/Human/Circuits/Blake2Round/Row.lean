module
public import Human.Circuits.Blake2Round.Addresses
public import Human.Circuits.Blake2Round.Schedule
public import Human.Circuits.Blake2Round.Finalization

@[expose] public section

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

end Airbender.Blake2Round.Row
