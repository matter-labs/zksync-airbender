module
public import Human.Helpers.Delegation.SpanABI
public import Human.Trace.Workers.Blake2G.WorkVector
public import Slop.Delegation.NativeSegments
public import Slop.Keccak.CallPermutation
public import Mathlib.Tactic.IntervalCases
public import Slop.Defs.Circuits.Keccak.Rho

@[expose] public section

namespace Tests.KeccakRho
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384

def scratch : Nat := 0x0100000000000001
def initial : Nat := 0xffffffffffffffff
def mixed : Nat := initial ^^^ scratch
def state : Vector Nat 25 := Vector.replicate 25 initial
def d : Vector Nat 5 := Vector.replicate 5 scratch
def control (_ : Fin 4096) : Vector Nat 6 := #v[0, 5, 10, 15, 20, 25]
abbrev setup : Table (ZMod babyBearModulus) (fields 8) := Keccak.setupTable control
def stateControl (rho : Bool) (column : Fin 5) : Keccak.ControlState :=
  ⟨if rho then 4 else 3, column, 0⟩
def rotation (column op : Fin 5) : Fin 64 := Keccak.Proofs.Rho.rotations[column][op]
def value (rho write : Bool) (column : Fin 5) (lane : Fin 6) : Nat :=
  if h : lane.val < 5 then
    if rho then if write then rotLeft64 mixed (rotation column ⟨lane.val, h⟩) else mixed
    else if write then mixed else initial
  else scratch

def base (rho : Bool) (column : Fin 5) (v : Nat) : ZMod babyBearModulus :=
  if v = 0 ∨ v = 70 + column.val ∨ v = (if rho then 67 else 66) then 1
  else if v = 3 then (stateControl rho column).packed
  else if v = 5 then (stateControl rho column).nextPacked
  else if 7 ≤ v ∧ v < 13 then (5 * (v - 7) : Nat)
  else if h : 15 ≤ v ∧ v < 63 then
    let lane : Fin 6 := ⟨(v - 15) / 8, by omega⟩
    let limb := ((v - 15) % 8) / 4 * 2 + (v - 15) % 2
    (value rho ((v - 15) % 4 ≥ 2) column lane / 2 ^ (16 * limb) % 65536 : Nat)
  else if rho ∧ v = 80 + column.val then 1
  else if 86 ≤ v ∧ v < 90 then (8192 + 16448 * (v - 86) : Nat)
  else 0

-- Byte query `i` (operation `i / 8`, byte `i % 8`): rotation pieces of the mixed lane's limbs
-- in Rho mode, the XOR bytes of the two Theta inputs otherwise.

private theorem expected_nonzero (column : Fin 5) :
    (Specs.Keccak256.rhoPi (Specs.Keccak256.thetaXor state d))[Keccak.rhoDestinations[column][0]] ≠ 0 := by
  fin_cases column <;> decide

end Tests.KeccakRho
