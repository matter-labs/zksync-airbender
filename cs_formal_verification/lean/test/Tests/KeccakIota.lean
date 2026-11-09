module
public import Human.Helpers.Delegation.SpanABI
public import Human.Trace.Workers.Blake2G.WorkVector
public import Slop.Delegation.NativeSegments
public import Slop.Keccak.CallPermutation
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Tests.KeccakIota
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384

def referenceState : Vector Nat 25 := Vector.ofFn fun i =>
  (#v[0xffffffffffffffff, 0x0123456789abcdef, 0x8080808080808080,
    0xaaaaaaaaaaaaaaaa, 0x5555555555555555] : Vector Nat 5)[i.val % 5]
def selectedColumn (case : Fin 3) : Fin 5 := if case.val = 2 then 2 else 0
def selectedRound (case : Fin 3) : Fin 25 := if case.val = 0 then 0 else 24
def effectiveRound (case : Fin 3) : Nat :=
  if (selectedColumn case).val = 0 then (selectedRound case).val else 0
def stateControl (case : Fin 3) : Keccak.ControlState :=
  ⟨0, selectedColumn case, ⟨(selectedRound case).val, by have := (selectedRound case).isLt; omega⟩⟩
def control (_ : Fin 4096) : Vector Nat 6 := #v[0, 5, 10, 15, 20, 25]
abbrev setup : Table (ZMod babyBearModulus) (fields 8) := Keccak.setupTable control
def reads (case : Fin 3) : Vector Nat 6 := Vector.ofFn fun i =>
  if h : i.val < 5 then referenceState[5 * (selectedColumn case).val + i.val] else 0
def changed (case : Fin 3) : Nat := (reads case)[0] ^^^ Keccak.adjustedConstant (effectiveRound case)
def temps (case : Fin 3) : Vector Nat 3 :=
  #v[changed case ^^^ (reads case)[1], changed case ^^^ (reads case)[1] ^^^ (reads case)[2],
    changed case ^^^ (reads case)[1] ^^^ (reads case)[2] ^^^ (reads case)[3]]
def writes (case : Fin 3) : Vector Nat 6 :=
  #v[changed case, (reads case)[1], (reads case)[2], (reads case)[3], (reads case)[4],
    (temps case)[2] ^^^ (reads case)[4]]
def aWords (case : Fin 3) : Vector Nat 5 :=
  #v[(reads case)[0], changed case, (temps case)[0], (temps case)[1], (temps case)[2]]

def base (case : Fin 3) (v : Nat) : ZMod babyBearModulus :=
  if v = 0 ∨ v = 63 ∨ v = 70 + (selectedColumn case).val then 1
  else if v = 3 then (stateControl case).packed
  else if v = 5 then (stateControl case).nextPacked
  else if 7 ≤ v ∧ v < 13 then (5 * (v - 7) : Nat)
  else if h : 15 ≤ v ∧ v < 63 then
    let lane : Fin 6 := ⟨(v - 15) / 8, by omega⟩
    let limb := ((v - 15) % 8) / 4 * 2 + (v - 15) % 2
    let value := if (v - 15) % 4 < 2 then (reads case)[lane] else (writes case)[lane]
    (value / 2 ^ (16 * limb) % 65536 : Nat)
  else if 75 ≤ v ∧ v < 80 then ((selectedRound case).val / 2 ^ (v - 75) % 2 : Nat)
  else if v = 85 then effectiveRound case
  else if 86 ≤ v ∧ v < 90 then
    (effectiveRound case + 64 * (v - 86) + 256 * (effectiveRound case + 64 * (v - 86) + 32) : Nat)
  else if h : 90 ≤ v ∧ v < 102 then
    let temporary : Fin 3 := ⟨(v - 90) / 4, by omega⟩
    ((temps case)[temporary] / 2 ^ (16 * ((v - 90) % 4)) % 65536 : Nat)
  else 0

-- Byte query `i` (operation `i / 8`, byte `i % 8`): the Iota XOR of lane 0 with the round
-- constant, then the running XOR of the column.

private theorem round_bound (case : Fin 3) : effectiveRound case < 32 := by
  fin_cases case <;> decide

private theorem expected_nonzero :
    (Keccak.iotaState referenceState (24 : Fin 25))[0] ≠ 0 := by decide

end Tests.KeccakIota
