module
public import Human.Helpers.Delegation.SpanABI
public import Human.Trace.Workers.Blake2G.WorkVector
public import Proven.Delegation.NativeSegments
public import Proven.Keccak.CallPermutation
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Tests.KeccakChi
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384

def referenceState : Vector Nat 25 := Vector.ofFn fun i =>
  if i.val % 5 = 2 then
    (#v[0xffffffffffffffff, 0x0123456789abcdef, 0x8080808080808080,
      0xaaaaaaaaaaaaaaaa, 0x5555555555555555] : Vector Nat 5)[i.val / 5]
  else 0

def control (_ : Fin 4096) : Vector Nat 6 := #v[0, 5, 10, 15, 20, 25]
abbrev setup : Table (ZMod babyBearModulus) (fields 8) := Keccak.setupTable control
def stateLane (i : Fin 5) : Nat := referenceState[5 * i.val + 2]
def andn (a b : Nat) : Nat := (not64 a) &&& b
def temps (second : Bool) : Vector Nat 3 :=
  if second then #v[andn (stateLane 4) (stateLane 0), andn (stateLane 0) (stateLane 1), 0]
  else #v[andn (stateLane 2) (stateLane 3), andn (stateLane 3) (stateLane 4), 0]
def reads (second : Bool) : Vector Nat 6 :=
  if second then #v[stateLane 0, stateLane 3, stateLane 4, andn (stateLane 1) (stateLane 2), stateLane 1, 0xfedcba9876543210]
  else #v[stateLane 1, stateLane 2, stateLane 3, stateLane 4, 0, 0]
def writes (second : Bool) : Vector Nat 6 :=
  if second then #v[stateLane 0 ^^^ andn (stateLane 1) (stateLane 2), stateLane 3 ^^^ andn (stateLane 4) (stateLane 0),
    stateLane 4 ^^^ andn (stateLane 0) (stateLane 1), andn (stateLane 1) (stateLane 2), stateLane 1, 0xfedcba9876543210]
  else #v[stateLane 1 ^^^ andn (stateLane 2) (stateLane 3), stateLane 2 ^^^ andn (stateLane 3) (stateLane 4),
    stateLane 3, stateLane 4, andn (stateLane 1) (stateLane 2), stateLane 1]
def aWords (second : Bool) : Vector Nat 5 :=
  if second then #v[stateLane 4, stateLane 3, stateLane 0, stateLane 4, stateLane 0] else #v[stateLane 1, stateLane 2, stateLane 1, stateLane 3, stateLane 2]
def bWords (second : Bool) : Vector Nat 5 :=
  if second then #v[stateLane 0, (temps true)[0], stateLane 1, (temps true)[1], andn (stateLane 1) (stateLane 2)]
  else #v[stateLane 2, stateLane 3, (temps false)[0], stateLane 4, (temps false)[1]]
def isAndn (second : Bool) (op : Nat) : Bool :=
  if second then op = 0 || op = 2 else op = 0 || op = 1 || op = 3

def base (second : Bool) (v : Nat) : ZMod babyBearModulus :=
  if v = 0 ∨ v = 70 ∨ v = (if second then 69 else 68) then 1
  else if v = 3 then (if second then 6 else 5)
  else if v = 5 then (if second then 13 else 6)
  else if 7 ≤ v ∧ v < 13 then (5 * (v - 7) : Nat)
  else if h : 15 ≤ v ∧ v < 63 then
    let lane : Fin 6 := ⟨(v - 15) / 8, by omega⟩
    let limb := ((v - 15) % 8) / 4 * 2 + (v - 15) % 2
    let value := if (v - 15) % 4 < 2 then (reads second)[lane] else (writes second)[lane]
    (value / 2 ^ (16 * limb) % 65536 : Nat)
  else if v = 86 then 8192 else if v = 87 then 24640
  else if v = 88 then 41088 else if v = 89 then 57536
  else if h : 90 ≤ v ∧ v < 102 then
    let temporary : Fin 3 := ⟨(v - 90) / 4, by omega⟩
    ((temps second)[temporary] / 2 ^ (16 * ((v - 90) % 4)) % 65536 : Nat)
  else 0

-- Byte query `i` (operation `i / 8`, byte `i % 8`): ANDN or XOR of the operation's two words.

private theorem reference_nonzero : (Specs.Keccak256.chi referenceState)[2] ≠ 0 := by decide

end Tests.KeccakChi
