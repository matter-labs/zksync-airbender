import Human.Circuits.KeccakSplit.Schedule
import Clean.Specs.Keccak256
import Human.Helpers.Memory.SailHistory

namespace Airbender.Keccak.Split.Call
open Trace

/-- Inverse Pi, in the row-major lane coordinates of the state block. -/
def piSource (lane : Fin 25) : Fin 25 :=
  ⟨(lane.val % 5 + 3 * (lane.val / 5)) % 5 + 5 * (lane.val % 5), by
    have := Nat.mod_lt lane.val (by decide : 0 < 5)
    have := Nat.mod_lt (lane.val % 5 + 3 * (lane.val / 5)) (by decide : 0 < 5)
    omega⟩

/-- Pi is never executed: logical lanes are renamed and their physical slots stay. -/
def physicalSlot : Nat → Fin 25 → Fin 25
  | 0, lane => lane
  | round + 1, lane => physicalSlot round (piSource lane)

/-- Lanes accessed by one call of each worker. -/
def slotCount : Kind → Nat
  | .columnParity => 6
  | .thetaRho => 7
  | .chi5 => 5

/-- The physical 8-byte slots accessed by call `index`, in port order. Slots 0–24
    hold the state (row-major), 25–29 the column parities C[0..4]; slot 30 marks an
    unused position (excluded by `slotCount`).
    Parity call x reads column x and writes C[x]; theta+rho call x reads column x,
    C[x-1] and C[x+1]; chi call y reads row y of the state after Pi. -/
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

/-- Rho rotation of lane (x, y) is `rotations[x][y]` (FIPS 202, Table 2). -/
def rotations : Vector (Vector (Fin 64) 5) 5 :=
  #v[#v[0, 36, 3, 41, 18], #v[1, 44, 10, 45, 2], #v[62, 6, 43, 15, 61],
    #v[28, 55, 25, 21, 56], #v[27, 20, 39, 8, 14]]

/-- Clean's round constant of round `round - 1`; zero before the first round. -/
def roundConstant (round : Nat) : Nat :=
  if valid : 0 < round ∧ round ≤ 24 then
    (Specs.Keccak256.roundConstants[round - 1]'(by omega)).toNat
  else 0

/-- What one call computes on its lanes (in `slots` order):
    parity call x: iota of the previous round on lane (0,0) when x = 0, then
      C[x] = the XOR of the column's five lanes (Keccak theta's column parity);
    theta+rho call x: lane (x, y) becomes rho(lane ^ D[x]) with
      D[x] = C[x-1] ^ rotLeft64 C[x+1] 1 (Keccak theta, then rho);
    chi call: lane i becomes lane i ^ (not lane (i+1) & lane (i+2)) (Keccak chi).
    Iota is delayed to the next parity call, including the final call at round 24. -/
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
        (not64 (input[(lane.val + 1) % 5]'(by omega)) &&& input[(lane.val + 2) % 5]'(by omega))
    else input[lane]

/-- The RAM word holding the low (`high = false`) or high half of `slot`. -/
def laneCell (pointer : BitVec 32) (slot : Fin 31) (high : Bool) : Cell :=
  .ram (pointer + BitVec.ofNat 32 (8 * slot.val + if high then 4 else 0))

def half (lane : Nat) (high : Bool) : BitVec 32 :=
  BitVec.ofNat 32 (if high then lane / 2 ^ 32 else lane)

/-- Every write of call `index`: the next control in x10, x11 unchanged, both
    halves of each accessed lane. -/
def writes (index : Fin 361) (pointer : BitVec 32) (output : Vector Nat 7) :
    List (Cell × BitVec 32) :=
  [(.register 10, BitVec.ofNat 32 (bump (controlAt index.val))), (.register 11, pointer)] ++
    ((List.range (slotCount (kindAt index.val))).flatMap fun lane =>
      if valid : lane < 7 then
        [(laneCell pointer (slots index)[lane] false, half output[lane] false),
         (laneCell pointer (slots index)[lane] true, half output[lane] true)]
      else [])

end Airbender.Keccak.Split.Call
