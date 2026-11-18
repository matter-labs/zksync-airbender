module
public import Mathlib.Data.List.Sort
-- Clean's Mathlib/Lean imports for this file, re-exported so importers see what they saw through Clean
public import Init.Data.List.Find
public import Lean
public import Lean.Elab.Tactic
public import Lean.Meta
public import Lean.Meta.Tactic.Simp.RegisterCommand
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Control.Monad.Writer

/-! # Offline memory checking (Clean `Clean.Utils.OfflineMemory`, pinned b41c196): memory accesses, timestamp-sorted
access lists and their online consistency (the per-address filter and the lemmas are in
`proven/Proven/CleanCore/Utils/OfflineMemory.lean`). Deviation: the circuit gadgets are omitted. -/

@[expose] public section

namespace Airbender

/--
  A memory access consists of an address, a read value, and a write value.
  The semantics are that at this address, we read the readValue, and then write the writeValue.
-/
@[reducible]
def MemoryAccess := ℕ × ℕ × ℕ × ℕ -- (timestamp, addr, readValue, writeValue)

/--
A memory list is canonically represented in reverse order, so that the most recent access is at the head of the list.
-/
@[reducible]
def MemoryAccessList := List MemoryAccess

abbrev timestamp_ordering (x y : MemoryAccess) := match x, y with
| (t2, _a2, _r2, _w2), (t1, _a1, _r1, _w1) => t1 < t2

/--
  A memory access list is timestamp sorted if the timestamps are strictly decreasing.

  This proposition indexes proof-dependent memory operations, so Lean must unfold
  it while checking implicit arguments.
-/
@[implicit_reducible]
def MemoryAccessList.isTimestampSorted (accesses : MemoryAccessList) : Prop :=
  accesses.Pairwise timestamp_ordering

def TimestampSortedMemoryAccessList := {accesses : MemoryAccessList // accesses.isTimestampSorted}

def MemoryAccessList.lastWriteValue (accesses : MemoryAccessList) (h : accesses.isTimestampSorted) (addr : ℕ) : ℕ := match accesses with
  -- initially the memory is all zero
  | [] => 0
  | (_t, addr', _readValue, writeValue) :: rest =>
    if addr' = addr then
      -- since the list is timestamp sorted, the first operation we find for this address is the most recent one
      writeValue
    else
      MemoryAccessList.lastWriteValue rest (List.Pairwise.of_cons h) addr

def MemoryAccessList.isConsistentOnline (accesses : MemoryAccessList) (h : accesses.isTimestampSorted) : Prop := match accesses with
  | [] => True -- no memory access is trivially consistent
  | (_timestamp, addr, readValue, _writeValue) :: rest =>
    -- here we need to check that the readValue is consistent with the previous writes to the same address
    readValue = MemoryAccessList.lastWriteValue rest (List.Pairwise.of_cons h) addr
    ∧ MemoryAccessList.isConsistentOnline rest (List.Pairwise.of_cons h)

end Airbender
