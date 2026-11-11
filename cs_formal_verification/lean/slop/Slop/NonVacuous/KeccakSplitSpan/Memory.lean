module
public import Slop.NonVacuous.KeccakSplitSpan.Parity.Honest
public import Slop.NonVacuous.KeccakSplitSpan.ThetaRho.Honest
public import Slop.NonVacuous.KeccakSplitSpan.Chi.Honest
public import Slop.NonVacuous.SequentialRun
public import Human.Circuits.KeccakSplit.Native
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! The span's memory and its rows: the 62 cells the schedule accesses (x10, x11 and both halves of state slots
    0 to 29 at the state pointer 0x400000), keyed as in `Common.lean`; a memory of current tokens; and call `k`'s
    honest row read from a memory (its worker's assignment of the words and clocks at its ports, at invocation
    clock `1 + 4 k`) with its steps in the sequential run. -/

namespace Airbender.NonVacuous.KeccakSplitSpan
open Arithmetic Trace Keccak.Split

local notation "P" => babyBearModulus

/-- The state pointer 0x400000, in x11. -/
def pointerBits : BitVec 32 := 0x400000

/-- The cell of a key. -/
def cellOf : Nat → Cell
  | 0 => .register 10
  | 1 => .register 11
  | n + 2 => Call.laneCell pointerBits ⟨n / 2 % 31, Nat.mod_lt _ (by decide)⟩ (decide (n % 2 = 1))

/-- The 62 keys: x10, x11 and both halves of slots 0 to 29. -/
def keys : List Nat := List.range 62

def cells : List Cell := keys.map cellOf

/-- A memory: the current token of every key. -/
abbrev Memory := Nat → MemoryToken P

/-- A row's assignment: its worker's honest assignment. -/
def assignment (x : RowInput) : Nat → ZMod P :=
  match kindAt x.call with
  | .columnParity => Parity.assignment x
  | .thetaRho => ThetaRho.assignment x
  | .chi5 => Chi.assignment x

namespace Memory
variable (mem : Memory) (k : Nat)

/-- Call `k`'s inputs: the words at its ports, their clocks, and the invocation clock `1 + 4 k`. -/
def input : RowInput where
  call := k
  read j := (mem (portKey k j)).word
  previous j := (mem (portKey k j)).time.1.val
  invocation := 1 + 4 * k

def row : Native.Row P := ⟨kindAt k, assignment (mem.input k)⟩

/-- The row's steps: each port's key and its write. -/
def steps : List (Nat × MemoryToken P) :=
  (portKeys k).zip ((mem.row k).ports.toList.map (mem.row k).writeToken)

end Memory

end Airbender.NonVacuous.KeccakSplitSpan
