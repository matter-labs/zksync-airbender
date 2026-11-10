module
public import Human.Helpers.Context.Columns
public import Human.Helpers.Context.PCState.Model
public import Human.Helpers.Context.Timestamps
public import Human.Helpers.Decoder.Columns
public import Human.Helpers.Memory.Ports
public import Human.Helpers.Properties
public import Human.Helpers.Context.Model
public import Slop.Defs.Helpers.Memory.Ports

/-! Definitions only the proofs use, moved from `human/Human/Helpers/Context/Model.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Trace
variable {Kind : Type} [CircuitLayout Kind]
def Data.memorySteps [Fact p.Prime] (trace : Data p Kind) : List (MemoryToken p × MemoryToken p) :=
  trace.rows.flatMap Row.memorySteps
/-- A complete PC/timestamp path from `trace.initial` to `trace.terminal`.
    Its edges are exactly the imported row transitions, and its clock values
    are distinct. This is proved from matching and clock advancement. -/
def StatePath [Fact p.Prime] (trace : Data p Kind) (path : List (PCState.State p)) : Prop :=
  path.head? = some trace.initial ∧ path.getLast? = some trace.terminal ∧
    (path.zip path.tail).Perm (trace.rows.map fun row => (row.start, row.finish)) ∧
    (path.map fun state => (timeOfPair state.timestamp).value).Nodup
/-- Follow one initialized cell `source` through every native access at its
    address to a terminal token. Clocks strictly increase; adjacent edges share
    the exact address/time/value token. This forces each read to use the previous
    write. The memory-path theorem constructs this path from logical matching. -/
def MemoryPath [Fact p.Prime] (trace : Data p Kind) (source : MemoryToken p)
    (path : List (MemoryToken p)) : Prop :=
  path.head? = some source ∧
    (∃ sink ∈ trace.terminalMemory, path.getLast? = some sink ∧ sink.address = source.address) ∧
    (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
    (path.zip path.tail).Perm (trace.memorySteps.filter fun edge => edge.1.address = source.address)
/-- Clean's chronological memory semantics for one address, with its public
    initial value written first. The history contains every native access. -/
def CellHistory [Fact p.Prime] (trace : Data p Kind) (source : MemoryToken p)
    (history : TimestampSortedMemoryAccessList) : Prop :=
  List.Perm history.val ((0, source.address, 0, source.value) ::
    (trace.memorySteps.filter fun edge => edge.1.address = source.address).map transferEvent) ∧
    MemoryAccessList.isConsistentOnline history.val history.property
/-- Write times of all imported memory ports, including readonly clock refreshes. -/
def Data.accessTimes [Fact p.Prime] (trace : Data p Kind) : List Nat :=
  trace.rows.flatMap fun row => row.ports.toList.map fun port =>
    (decodeTimestamp row.assignment row.columns.initialTime).value + port.clock.offset
end Airbender.Trace
