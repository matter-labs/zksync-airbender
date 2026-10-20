import Human.Helpers.Context.Model

namespace Airbender.Trace

variable {Kind : Type} [CircuitLayout Kind]

/-- Offset Clean access times beyond every initialization write. Seed writes
    use their encoded addresses as distinct initial times; native accesses start
    after the largest one. This relabels time only, preserving native values and order. -/
def Data.memoryEpoch [Fact p.Prime] (trace : Data p Kind) : Nat :=
  (trace.initialMemory.map MemoryToken.address).foldr max 0 + 1

/-- Interpret every imported port transfer as a Clean access, shifting its
    native write timestamp by `memoryEpoch`. Row-list order may still be arbitrary. -/
def Data.nativeEvents [Fact p.Prime] (trace : Data p Kind) : List MemoryAccess :=
  trace.memorySteps.map fun edge =>
    ((trace.memoryEpoch + (timeOfPair edge.2.time).value,
      edge.1.address, edge.1.value, edge.2.value) : MemoryAccess)

/-- Explicit public initialization writes followed by all imported native ports.
    The witness row list may be unordered; the theorem supplies their chronology. -/
def Data.memoryEvents [Fact p.Prime] (trace : Data p Kind) : List MemoryAccess :=
  List.append (α := MemoryAccess)
    (trace.initialMemory.map fun source =>
      ((source.address, source.address, 0, source.value) : MemoryAccess))
    trace.nativeEvents

/-- One complete Clean memory history for `trace`. Its sorted accesses are
    exactly the initialization writes and imported port transfers. Online
    consistency forces each read to use the last write at that address.
    The history theorem constructs this from acceptance and public initialization. -/
def MemoryHistory [Fact p.Prime] (trace : Data p Kind)
    (history : TimestampSortedMemoryAccessList) : Prop :=
  history.val.Perm trace.memoryEvents ∧
    MemoryAccessList.isConsistentOnline history.val history.property

end Airbender.Trace
