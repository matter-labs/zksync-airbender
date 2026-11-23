module
public import Human.Circuits.Blake2Round.Execution
public import Human.Circuits.Keccak.Tables.Controller
public import Batteries.Data.Fin.Fold

@[expose] public section

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

end Airbender.Blake2Round.Compression
