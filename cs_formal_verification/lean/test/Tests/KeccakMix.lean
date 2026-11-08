module
public import Human.Helpers.Delegation.SpanABI
public import Human.Trace.Workers.Blake2G.WorkVector
public import Slop.Delegation.NativeSegments
public import Slop.Keccak.CallPermutation
public import Mathlib.Tactic.IntervalCases
import all Init.Data.Array.Basic -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)

@[expose] public section

namespace Tests.KeccakMix
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384

def parities : Vector Nat 5 :=
  #v[0xffffffffffffffff, 0x0123456789abcdef, 0x8080808080808080,
    0xaaaaaaaaaaaaaaaa, 0x5555555555555555]
def rotated (i : Fin 5) : Nat := rotLeft64 parities[i] 1
def firstWrites : Vector Nat 6 :=
  #v[parities[0] ^^^ rotated 2, parities[1], parities[2] ^^^ rotated 4,
    parities[3], parities[4], rotated 0]
def reads (second : Bool) : Vector Nat 6 :=
  if second then firstWrites else #v[parities[0], parities[1], parities[2], parities[3], parities[4], 0]
def writes (second : Bool) : Vector Nat 6 :=
  if second then
    #v[firstWrites[0], parities[1] ^^^ rotated 3, firstWrites[2], parities[3] ^^^ rotated 0,
      parities[4] ^^^ rotated 1, rotated 0]
  else firstWrites
def temps (second : Bool) : Vector Nat 3 :=
  if second then #v[rotated 1, rotated 3, 0] else #v[rotated 2, rotated 4, 0]
def aWords (second : Bool) : Vector Nat 5 :=
  if second then #v[parities[1], parities[4], parities[3], parities[1], parities[3]]
  else #v[parities[0], parities[2], parities[0], parities[4], parities[2]]
def bWords (second : Bool) : Vector Nat 5 :=
  if second then #v[0, rotated 1, 0, rotated 3, rotated 0]
  else #v[0, 0, rotated 2, 0, rotated 4]
def rotation (second : Bool) (op : Fin 5) : Bool :=
  if second then op.val = 0 || op.val = 2 else op.val = 0 || op.val = 1 || op.val = 3
def control (_ : Fin 4096) : Vector Nat 6 := #v[0, 5, 10, 15, 20, 25]
abbrev setup : Table (ZMod babyBearModulus) (fields 8) := Keccak.setupTable control
def stateControl (second : Bool) : Keccak.ControlState := ⟨if second then 2 else 1, 0, 24⟩

def base (second : Bool) (v : Nat) : ZMod babyBearModulus :=
  if v = 0 ∨ v = 70 ∨ v = (if second then 65 else 64) then 1
  else if v = 3 then (stateControl second).packed
  else if v = 5 then (stateControl second).nextPacked
  else if 7 ≤ v ∧ v < 13 then (5 * (v - 7) : Nat)
  else if h : 15 ≤ v ∧ v < 63 then
    let lane : Fin 6 := ⟨(v - 15) / 8, by omega⟩
    let limb := ((v - 15) % 8) / 4 * 2 + (v - 15) % 2
    let value := if (v - 15) % 4 < 2 then (reads second)[lane] else (writes second)[lane]
    (value / 2 ^ (16 * limb) % 65536 : Nat)
  else if 75 ≤ v ∧ v < 80 then (24 / 2 ^ (v - 75) % 2 : Nat)
  else if v = 85 then 24
  else if 86 ≤ v ∧ v < 90 then (14360 + 16448 * (v - 86) : Nat)
  else if h : 90 ≤ v ∧ v < 102 then
    let temporary : Fin 3 := ⟨(v - 90) / 4, by omega⟩
    ((temps second)[temporary] / 2 ^ (16 * ((v - 90) % 4)) % 65536 : Nat)
  else 0

-- Byte query `i` (operation `i / 8`, byte `i % 8`): rotation by one of a word's 16-bit limbs,
-- or the XOR bytes of two words.

private theorem expected_nonzero : (Specs.Keccak256.thetaD parities)[0] ≠ 0 := by decide

end Tests.KeccakMix
