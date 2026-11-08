module
public import Human.Trace.Workers.Blake2Round.Compression
public import Human.Helpers.Delegation.RVMemory

@[expose] public section

namespace Airbender.Blake2Round.Compression
open Arithmetic

/-- RV sibling of `WordsAt`: bind a block to successful reads from actual RV RAM (`Cell.readRV`; RAM at any address,
    INCLUDING THE SHADOW RAM BELOW `ROM_END`), at four-byte intervals. Canonical word bounds are conclusions. -/
def RVWordsAt {n : Nat} (state : RV.State) (pointer : BitVec 32)
    (offset : Nat) (words : Vector Word n) : Prop :=
  ∀ i : Fin n, words[i].Bounded ∧
    (Trace.Cell.ram (pointer + BitVec.ofNat 32 (4 * (offset + i.val)))).readRV state = some words[i].toBitVec

/-- RV sibling of `WordMapping`: the compression's public pointers, initial blocks and final RAM blocks, read from
    `RV.State`s. A proved result: callers do not supply these reads or word bounds. RAM cells include READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/
structure RVWordMapping (initial after : RV.State)
    (statePointer messagePointer : BitVec 32) (input output : State)
    (message : Vector Word 16) : Prop where
  /-- The state and message pointers are the initial architectural x10/x11. -/
  pointers : (Trace.Cell.register 10).readRV initial = some statePointer ∧
    (Trace.Cell.register 11).readRV initial = some messagePointer
  /-- Eight initial chaining words at x10. -/
  inputState : RVWordsAt initial statePointer 0 input.1
  /-- Sixteen initial working words immediately after the chaining block. -/
  inputExtended : RVWordsAt initial statePointer 8 input.2
  /-- Sixteen readonly input words at x11. -/
  messageWords : RVWordsAt initial messagePointer 0 message
  /-- The final chaining/digest words in actual RAM. -/
  outputState : RVWordsAt after statePointer 0 output.1
  /-- The final working words in actual RAM. -/
  outputExtended : RVWordsAt after statePointer 8 output.2

end Airbender.Blake2Round.Compression
