module
public import Human.Circuits.Blake2Round.Tables.Setup
public import Human.Circuits.Blake2Round.Artifact
public import Human.Helpers.Properties

@[expose] public section

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

end Airbender.Blake2Round.Addresses
