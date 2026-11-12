module
public import Human.Circuits.Blake2Round.Preparation
public import Slop.Defs.Circuits.Blake2G.Control
public import Human.Circuits.Blake2Round.Schedule
public import Slop.Defs.Circuits.Blake2Round.Preparation

/-! Definitions only the proofs use, moved from `human/Human/Circuits/Blake2Round/Schedule.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Blake2Round.Schedule
open Arithmetic
def spec (input : Input) (output : Output) : Prop := output = step input
structure Mapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  message : input.message = Preparation.messageWords w
  output : output = Preparation.words w Variables.scheduledMessage
/-- The caller selects exactly one round. The local circuit only makes each
    selector Boolean; it does not enforce this exclusive-mask ABI condition. -/
structure InterfaceAssumptions {p : Nat} (input : Input) (_output : Output)
    (w : Nat → ZMod p) : Prop where
  roundMask : Control.RoundMask w input.round
def circuitModel {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 6)) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints setup)
  represents := Mapping
end Airbender.Blake2Round.Schedule
