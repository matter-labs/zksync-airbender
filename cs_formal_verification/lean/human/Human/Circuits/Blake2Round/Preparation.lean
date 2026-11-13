module
public import Human.Circuits.Blake2Round.Control
public import CleanCore.Specs.BLAKE3

@[expose] public section

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

-- No round-mask exclusivity or memory-transport assumption is needed for preparation.

end Airbender.Blake2Round.Preparation
