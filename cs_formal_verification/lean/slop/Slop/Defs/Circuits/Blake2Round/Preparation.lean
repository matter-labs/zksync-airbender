module
public import Human.Circuits.Blake2Round.Control
public import CleanCore.Specs.BLAKE3
public import Human.Circuits.Blake2Round.Preparation
public import Slop.Defs.Circuits.Blake2Round.Control

/-! Definitions only the proofs use, moved from `human/Human/Circuits/Blake2Round/Preparation.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Blake2Round.Preparation
open Arithmetic
def spec (input : Input) (output : Output) : Prop := output = step input
def words {p : Nat} (w : Nat → ZMod p) {n : Nat} (columns : Vector (Nat × Nat) n) : Vector Word n :=
  columns.map fun pair => ⟨(w pair.1).val, (w pair.2).val⟩
/-- The selected message is not committed: `wider_tables.rs` commits the
    round/mode products and computes the permuted words directly from memory.
    Word `i` of the selection, as an expression in the message (x11) and state
    (x10) reads and the two mode columns: w 202 = compression and right node,
    w 203 = compression and left node. -/
def messageLimb {p : Nat} (w : Nat → ZMod p) (word limb : Nat) : ZMod p :=
  if word < 8 then
    (1 - w 203) * w (103 + 2 * word + limb) + w 203 * w (5 + 4 * word + limb)
  else
    (1 - w 203 - w 202) * w (103 + 2 * word + limb) +
      w 202 * w (5 + 4 * (word - 8) + limb) +
      w 203 * w (103 + 2 * (word - 8) + limb)
def messageWords {p : Nat} (w : Nat → ZMod p) : Vector Word 16 :=
  Vector.ofFn fun i => ⟨(messageLimb w i.val 0).val, (messageLimb w i.val 1).val⟩
structure Mapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  firstRound : w 142 = if input.firstRound then 1 else 0
  compression : w 141 = if input.compression then 1 else 0
  inputIsRight : w 140 = if input.inputIsRight then 1 else 0
  state : input.state = words w Variables.stateReads
  extended : input.extended = words w Variables.extendedReads
  message : input.message = words w Variables.messageReads
  chainingOutput : output.chaining = words w Variables.chainingInputs
  extendedOutput : output.extended = words w Variables.preparedState
  messageOutput : output.message = messageWords w
def circuitModel {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 6)) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints setup)
  represents := Mapping
end Airbender.Blake2Round.Preparation
