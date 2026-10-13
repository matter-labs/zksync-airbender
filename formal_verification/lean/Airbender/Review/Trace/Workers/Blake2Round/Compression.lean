import Airbender.Review.Trace.Workers.Blake2Round.Call
import Batteries.Data.Fin.Fold

namespace Airbender.Blake2Round.Compression
open Arithmetic

/-- The two state blocks used by the pinned extended-BLAKE caller: eight
    chaining words and sixteen working words. Message words are readonly. -/
abbrev State := Vector Word 8 × Vector Word 16

/-- One round of the existing project reference: prepare, SIGMA-select, apply
    Clean's eight-G round, then finalize. Canonical word encoding reflects the
    Rust `u32` storage in `blake2s_u32/src/state_with_extended_control/`;
    its caller and existing preparation/SIGMA/finalization references supply
    the mode and schedule. No circuit witness is used. -/
def step (flags : Fin 8) (round : Fin 10) (state : State) (message : Vector Word 16) : State :=
  let reduced := decide (flags.val % 2 = 1)
  let prepared := Preparation.step ⟨round == 0, decide (flags.val / 4 = 1),
    decide (flags.val / 2 % 2 = 1), state.1, state.2, message⟩
  let mixed := Specs.BLAKE3.round (prepared.extended.map Word.value)
    ((Schedule.step ⟨round, prepared.message⟩).map Word.value)
  let extended := mixed.map fun value => Word.ofBitVec (BitVec.ofNat 32 value)
  let chaining := if Finalization.isFinal ⟨round, reduced, state.1, prepared.chaining, extended⟩ then
    (Vector.ofFn fun i : Fin 8 => prepared.chaining[i].value ^^^
      extended[i.val].value ^^^ extended[8 + i.val].value).map
        (fun value => Word.ofBitVec (BitVec.ofNat 32 value))
    else state.1
  (chaining, extended)

/-- The pinned request executes seven rounds when its reduced-round flag is
    set and ten otherwise. Each round consumes the same readonly message. -/
def run (flags : Fin 8) (state : State) (message : Vector Word 16) : State :=
  Fin.foldl (if flags.val % 2 = 1 then 7 else 10)
    (fun current i => step flags (Fin.ofNat 10 i.val) current message) state

/-- Bind a block to successful reads from actual Sail RAM, at four-byte
    intervals. Canonical word bounds are conclusions of this binding. -/
def WordsAt {n : Nat} (state : Reference.RiscV.Sail.State) (pointer : BitVec 32)
    (offset : Nat) (words : Vector Word n) : Prop :=
  ∀ i : Fin n, words[i].Bounded ∧
    (Trace.Cell.ram (pointer + BitVec.ofNat 32 (4 * (offset + i.val)))).read state =
      .ok words[i].toBitVec state

/-- The compression's public pointers, initial blocks and final RAM blocks.
    This is a proved result: callers do not supply these reads or word bounds. -/
structure WordMapping (initial after : Reference.RiscV.Sail.State)
    (statePointer messagePointer : BitVec 32) (input output : State)
    (message : Vector Word 16) : Prop where
  /-- The state and message pointers are the initial architectural x10/x11. -/
  pointers : (Trace.Cell.register 10).read initial = .ok statePointer initial ∧
    (Trace.Cell.register 11).read initial = .ok messagePointer initial
  /-- Eight initial chaining words at x10. -/
  inputState : WordsAt initial statePointer 0 input.1
  /-- Sixteen initial working words immediately after the chaining block. -/
  inputExtended : WordsAt initial statePointer 8 input.2
  /-- Sixteen readonly input words at x11. -/
  messageWords : WordsAt initial messagePointer 0 message
  /-- The final chaining/digest words in actual RAM. -/
  outputState : WordsAt after statePointer 0 output.1
  /-- The final working words in actual RAM. -/
  outputExtended : WordsAt after statePointer 8 output.2

end Airbender.Blake2Round.Compression
