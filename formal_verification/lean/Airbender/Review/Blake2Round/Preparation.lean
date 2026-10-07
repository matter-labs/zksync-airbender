import Airbender.Review.Blake2Round.Control
import Clean.Specs.BLAKE3

namespace Airbender.Blake2Round.Preparation
open Arithmetic

structure Input where
  firstRound : Bool
  compression : Bool
  inputIsRight : Bool
  state : Vector Word 8
  extended : Vector Word 16
  message : Vector Word 16

/-- Internal words before the eight G calls, not the memory writeback. -/
structure Output where
  chaining : Vector Word 8
  extended : Vector Word 16
  message : Vector Word 16

def splitWord (value : UInt32) : Word := ⟨value.toNat % limbBase, value.toNat / limbBase⟩

/-- The common BLAKE2s/BLAKE3 IV comes from Clean. Airbender's digest parameter,
    block-length and final-block adjustments are those in `blake2s_u32/src/lib.rs`
    (`CONFIGURED_IV` and `COMPRESSION_MODE_EXTENDED_CONFIGURED_IV`). -/
def iv : Vector Word 8 := Specs.BLAKE3.iv.map splitWord
def configuredIV : Vector Word 8 := iv.set 0 (splitWord (Specs.BLAKE3.iv[0] ^^^ 0x01010020))
def compressionIV : Vector Word 8 :=
  (iv.set 4 (splitWord (Specs.BLAKE3.iv[4] ^^^ 64))).set 6
    (splitWord (Specs.BLAKE3.iv[6] ^^^ 0xffffffff))

/-- Normal mode keeps the message. Compression mode orders the chaining state
    and the first eight message words according to the left/right control.
    Only the first round initializes the extended state; normal mode preserves
    its counter/final-block lanes. Source: the circuit's `mod.rs`, preparation loops. -/
def step (input : Input) : Output :=
  let chaining := if input.compression then configuredIV else input.state
  let suffix := if input.compression then compressionIV
    else (iv.set 4 input.extended[12]).set 6 input.extended[14]
  let message := if !input.compression then input.message
    else if input.inputIsRight then input.message.take 8 ++ input.state
    else input.state ++ input.message.take 8
  ⟨chaining, if input.firstRound then chaining ++ suffix else input.extended, message⟩

def spec (input : Input) (output : Output) : Prop := output = step input

def words {p : Nat} (w : Nat → ZMod p) {n : Nat} (columns : Vector (Nat × Nat) n) : Vector Word n :=
  columns.map fun pair => ⟨(w pair.1).val, (w pair.2).val⟩

structure Mapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  firstRound : w 142 = if input.firstRound then 1 else 0
  compression : w 141 = if input.compression then 1 else 0
  inputIsRight : w 140 = if input.inputIsRight then 1 else 0
  state : input.state = words w Variables.stateReads
  extended : input.extended = words w Variables.extendedReads
  message : input.message = words w Variables.messageReads
  chainingOutput : output.chaining = words w Variables.chainingInputs
  extendedOutput : output.extended = words w Variables.preparedState
  messageOutput : output.message = words w Variables.preparedMessage

-- No round-mask exclusivity or memory-transport assumption is needed for preparation.
def circuitModel {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints setup)
  represents := Mapping

end Airbender.Blake2Round.Preparation
