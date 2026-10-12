import Airbender.Review.Blake2Round.Preparation
import Airbender.Review.Blake2G.Control

namespace Airbender.Blake2Round.Schedule
open Arithmetic

structure Input where
  round : Fin 10
  message : Vector Word 16

abbrev Output := Vector Word 16

/-- Reuse the same BLAKE2s SIGMA schedule as the G controller. -/
def step (input : Input) : Output :=
  Blake2G.Control.messageSchedule[input.round].map fun column =>
    input.message[Fin.ofNat 16 column]

def spec (input : Input) (output : Output) : Prop := output = step input

structure Mapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  message : input.message = Preparation.words w Variables.preparedMessage
  output : output = Preparation.words w Variables.scheduledMessage

/-- The caller selects exactly one round. The local circuit only makes each
    selector Boolean; it does not enforce this exclusive-mask ABI condition. -/
structure InterfaceAssumptions {p : Nat} (input : Input) (_output : Output)
    (w : Nat → ZMod p) : Prop where
  roundMask : Control.RoundMask w input.round

def circuitModel {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints setup)
  represents := Mapping

end Airbender.Blake2Round.Schedule
