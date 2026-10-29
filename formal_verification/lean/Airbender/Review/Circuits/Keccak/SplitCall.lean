import Airbender.Review.Trace.Workers.Keccak.SplitUse
import Airbender.Review.Helpers.Memory.AtomicWrites
import Clean.Specs.Keccak256

namespace Airbender.Keccak.Split.Call
open Trace Reference.RiscV.Sail Reference.Sail

/-- Inverse Pi, in the wrapper's row-major lane coordinates. -/
def piSource (lane : Fin 25) : Fin 25 :=
  ⟨(lane.val % 5 + 3 * (lane.val / 5)) % 5 + 5 * (lane.val % 5), by
    have := Nat.mod_lt lane.val (by decide : 0 < 5)
    have := Nat.mod_lt (lane.val % 5 + 3 * (lane.val / 5)) (by decide : 0 < 5)
    omega⟩

/-- Logical lanes are renamed after Pi; their physical slots stay in place. -/
def physicalSlot : Nat → Fin 25 → Fin 25
  | 0, lane => lane
  | round + 1, lane => physicalSlot round (piSource lane)

def slotCount : Kind → Nat
  | .columnParity => 6
  | .thetaRho => 7
  | .chi5 => 5

/-- Access order of a blessed split micro-call. Slot 30 is padding and is
excluded by `slotCount`. The first 25 slots use row-major lane coordinates. -/
def slots (index : Fin 361) : Vector (Fin 31) 7 :=
  let x := index.val % 5
  let round := index.val / 15
  Vector.ofFn fun position =>
    if lane : position.val < 5 then
      let logical : Fin 25 :=
        if kindAt index.val = .chi5 then
          ⟨5 * x + (position.val + 2 * x) % 5, by
            have := Nat.mod_lt index.val (by decide : 0 < 5)
            have := Nat.mod_lt (position.val + 2 * x) (by decide : 0 < 5)
            dsimp [x] at *
            omega⟩
        else ⟨x + 5 * position.val, by
          have := Nat.mod_lt index.val (by decide : 0 < 5)
          dsimp [x] at *
          omega⟩
      let physical := physicalSlot
        (if kindAt index.val = .chi5 then round + 1 else round) logical
      ⟨physical.val, by have := physical.isLt; omega⟩
    else if kindAt index.val = .columnParity ∧ position.val = 5 then
      ⟨25 + x, by have := Nat.mod_lt index.val (by decide : 0 < 5); dsimp [x]; omega⟩
    else if kindAt index.val = .thetaRho then
      ⟨25 + (if position.val = 5 then (x + 4) % 5 else (x + 1) % 5), by
        split <;> omega⟩
    else 30

def rotations : Vector (Vector (Fin 64) 5) 5 :=
  #v[#v[0, 36, 3, 41, 18], #v[1, 44, 10, 45, 2], #v[62, 6, 43, 15, 61],
    #v[28, 55, 25, 21, 56], #v[27, 20, 39, 8, 14]]

def roundConstant (round : Nat) : Nat :=
  if valid : 0 < round ∧ round ≤ 24 then
    (Specs.Keccak256.roundConstants[round - 1]'(by omega)).toNat
  else 0

/-- The three mathematical split operations. Iota is delayed until the next
column-parity phase, including the final call at round 24. -/
def result (index : Fin 361) (input : Vector Nat 7) : Vector Nat 7 :=
  let x : Fin 5 := ⟨index.val % 5, Nat.mod_lt _ (by decide)⟩
  match kindAt index.val with
  | .columnParity =>
    let first := if x.val = 0 then input[0] ^^^ roundConstant (index.val / 15) else input[0]
    #v[first, input[1], input[2], input[3], input[4],
      first ^^^ input[1] ^^^ input[2] ^^^ input[3] ^^^ input[4], input[6]]
  | .thetaRho =>
    let d := input[5] ^^^ rotLeft64 input[6] 1
    Vector.ofFn fun lane => if active : lane.val < 5 then
      rotLeft64 (input[lane] ^^^ d) (rotations[x][lane.val]'active)
    else input[lane]
  | .chi5 => Vector.ofFn fun lane => if active : lane.val < 5 then
      input[lane] ^^^
        (not64 (input[(lane.val + 1) % 5]'(by omega)) &&&
          input[(lane.val + 2) % 5]'(by omega))
    else input[lane]

def laneCell (pointer : BitVec 32) (slot : Fin 31) (high : Bool) : Cell :=
  .ram (pointer + BitVec.ofNat 32 (8 * slot.val + if high then 4 else 0))

def half (lane : Nat) (high : Bool) : BitVec 32 :=
  BitVec.ofNat 32 (if high then lane / 2 ^ 32 else lane)

def writes (index : Fin 361) (pointer : BitVec 32) (output : Vector Nat 7) :
    List (Cell × BitVec 32) :=
  [(.register 10, BitVec.ofNat 32 (bump (controlAt index.val))), (.register 11, pointer)] ++
    ((List.range (slotCount (kindAt index.val))).flatMap fun lane =>
      if valid : lane < 7 then
        [(laneCell pointer (slots index)[lane] false, half output[lane] false),
         (laneCell pointer (slots index)[lane] true, half output[lane] true)]
      else [])

/-- Complete reference effect of one blessed split call, including both
registers, every touched lane and the unchanged Sail frame. The index and
pointer are read from the reference state; no native witness value occurs. -/
def Executes (kind : Kind) (before after : State) : Prop :=
  ∃ (index : Fin 361) (pointer : BitVec 32) (input : Vector Nat 7),
    kindAt index.val = kind ∧ ArgumentsAt index.val before ∧
    (Cell.register 11).read before = .ok pointer before ∧
    (∀ lane : Fin 7, lane.val < slotCount kind →
      input[lane] < 2 ^ 64 ∧
      (laneCell pointer (slots index)[lane] false).read before =
        .ok (half input[lane] false) before ∧
      (laneCell pointer (slots index)[lane] true).read before =
        .ok (half input[lane] true) before) ∧
    AtomicWrites (writes index pointer (result index input)) before after

def Retires (kind : Kind) (before after : State) : Prop :=
  ∃ middle, Executes kind before middle ∧
    run (do SailRV32.Functions.normal_base_next_pc (); SailRV32.Functions.tick_pc ())
      middle = .ok () after

end Airbender.Keccak.Split.Call
