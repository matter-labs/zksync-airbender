import Airbender.Review.Trace.Model

namespace Airbender.Trace

/-- Place all initialization writes before real accesses. This shift changes
    only Clean's chronological labels, not native addresses or values. -/
def Data.memoryEpoch [Fact p.Prime] (trace : Data p) : Nat :=
  (trace.initialMemory.map MemoryToken.address).foldr max 0 + 1

def Data.nativeEvents [Fact p.Prime] (trace : Data p) : List MemoryAccess :=
  trace.memorySteps.map fun edge =>
    ((trace.memoryEpoch + (timeOfPair edge.2.time).value,
      edge.1.address, edge.1.value, edge.2.value) : MemoryAccess)

/-- Explicit public initialization writes followed by all imported native ports.
    The witness row list may be unordered; the theorem supplies their chronology. -/
def Data.memoryEvents [Fact p.Prime] (trace : Data p) : List MemoryAccess :=
  List.append (α := MemoryAccess)
    (trace.initialMemory.map fun source =>
      ((source.address, source.address, 0, source.value) : MemoryAccess))
    trace.nativeEvents

def MemoryHistory [Fact p.Prime] (trace : Data p)
    (history : TimestampSortedMemoryAccessList) : Prop :=
  history.val.Perm trace.memoryEvents ∧
    MemoryAccessList.isConsistentOnline history.val history.property

end Airbender.Trace
