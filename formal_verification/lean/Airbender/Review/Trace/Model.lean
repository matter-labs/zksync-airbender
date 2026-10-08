import Airbender.Review.AddSub.Artifact
import Airbender.Review.WordMemory.Artifact
import Airbender.Review.PCState.Model
import Airbender.Review.Properties

namespace Airbender.Trace

inductive Family where
  | addSub | wordMemory
  deriving DecidableEq

/-- One witness assignment for a selected native circuit family. -/
structure Row (p : Nat) where
  family : Family
  assignment : Nat → ZMod p

def Row.columns (row : Row p) : TraceColumns :=
  match row.family with
  | .addSub => AddSub.importedConstraintsTraceColumns
  | .wordMemory => WordMemory.importedConstraintsTraceColumns

def Row.ports (row : Row p) : Array MemoryPort :=
  match row.family with
  | .addSub => AddSub.importedConstraintsMemoryPorts
  | .wordMemory => WordMemory.importedConstraintsMemoryPorts

def Row.decoderColumns (row : Row p) : DecoderColumns :=
  match row.family with
  | .addSub => AddSub.importedConstraintsDecoderColumns
  | .wordMemory => WordMemory.importedConstraintsDecoderColumns

def Row.constraints [Fact p.Prime] (row : Row p) (rom : Table (ZMod p) (fields 9)) :
    List (FlatOperation (ZMod p)) :=
  match row.family with
  | .addSub => AddSub.clockConstraints
  | .wordMemory => WordMemory.clockConstraints rom

def rawPair (w : Nat → ZMod p) (columns : Vector Nat 2) : ZMod p × ZMod p :=
  (w columns[0], w columns[1])

def timeOfPair (time : ZMod p × ZMod p) : Timestamp := ⟨time.1.val, time.2.val⟩

def Row.start (row : Row p) : PCState.State p :=
  ⟨rawPair row.assignment row.columns.initialPC, rawPair row.assignment row.columns.initialTime⟩

def Row.finish (row : Row p) : PCState.State p :=
  ⟨rawPair row.assignment row.columns.finalPC, rawPair row.assignment row.columns.finalTime⟩

/-- Raw address/time/value tuple of the memory permutation. Pair coding preserves
    all field limbs; no word or timestamp range is assumed in this definition. -/
structure MemoryToken (p : Nat) where
  address : Nat
  time : ZMod p × ZMod p
  value : Nat
  deriving DecidableEq

def readToken (w : Nat → ZMod p) (port : MemoryPort) : MemoryToken p :=
  ⟨port.address.code w, rawPair w port.clock.previous, port.readCode w⟩

def writeToken (columns : TraceColumns) (w : Nat → ZMod p) (port : MemoryPort) : MemoryToken p :=
  let base := rawPair w columns.initialTime
  ⟨port.address.code w, (base.1 + port.clock.offset, base.2), port.writeCode w⟩

def Row.reads (row : Row p) : List (MemoryToken p) :=
  row.ports.toList.map (readToken row.assignment)

def Row.writes (row : Row p) : List (MemoryToken p) :=
  row.ports.toList.map (writeToken row.columns row.assignment)

/-- Each imported port transfers its previous cell to a freshly timestamped cell.
    Readonly ports preserve the value while refreshing the timestamp. -/
def Row.memorySteps (row : Row p) : List (MemoryToken p × MemoryToken p) :=
  row.ports.toList.map fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)

structure Data (p : Nat) [Fact p.Prime] where
  rows : List (Row p)
  rom : Table (ZMod p) (fields 9)
  initial : PCState.State p
  terminal : PCState.State p
  initialMemory : List (MemoryToken p)
  terminalMemory : List (MemoryToken p)

def Data.memorySteps [Fact p.Prime] (trace : Data p) : List (MemoryToken p × MemoryToken p) :=
  trace.rows.flatMap Row.memorySteps

/-- Logical native matching, with both sides built from the imported row columns.
    Cryptographic enforcement and the initial/terminal memory-image binding are
    separate obligations. This contract does not assert decoded instructions or
    any expected read value. -/
structure Accepted [Fact p.Prime] (trace : Data p) : Prop where
  constraints : ∀ row ∈ trace.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints trace.rom)
  active : ∀ row ∈ trace.rows, row.assignment row.columns.execute = 1
  states : (trace.initial :: trace.rows.map Row.finish).Perm
    (trace.terminal :: trace.rows.map Row.start)
  memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
    (trace.terminalMemory ++ trace.rows.flatMap Row.reads)

/-- Public initial clock conditions; per-row bounds/alignment must be derived. -/
structure ClockBoundary [Fact p.Prime] (trace : Data p) : Prop where
  initial : (timeOfPair trace.initial.timestamp).Bounded
  aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0
  memory : ∀ token ∈ trace.initialMemory, (timeOfPair token.time).Bounded

/-- An ordering of all native row transitions, with no repeated clock value. -/
def StatePath [Fact p.Prime] (trace : Data p) (path : List (PCState.State p)) : Prop :=
  path.head? = some trace.initial ∧ path.getLast? = some trace.terminal ∧
    (path.zip path.tail).Perm (trace.rows.map fun row => (row.start, row.finish)) ∧
    (path.map fun state => (timeOfPair state.timestamp).value).Nodup

/-- One complete history for an initialized address. Adjacent accesses share the
    exact address/time/value token, so every read uses the preceding write's value. -/
def MemoryPath [Fact p.Prime] (trace : Data p) (source : MemoryToken p)
    (path : List (MemoryToken p)) : Prop :=
  path.head? = some source ∧
    (∃ sink ∈ trace.terminalMemory, path.getLast? = some sink ∧ sink.address = source.address) ∧
    (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
    (path.zip path.tail).Perm (trace.memorySteps.filter fun edge => edge.1.address = source.address)

/-- A native read uses the newest preceding cell at its address, drawn from the
    initial image or a native write. This is a conclusion, not an interface premise. -/
def LatestRead [Fact p.Prime] (trace : Data p) (row : Row p) (port : MemoryPort) : Prop :=
  let previous := readToken row.assignment port
  let time := (port.event row.columns row.assignment).1
  let cells := trace.initialMemory ++ trace.rows.flatMap Row.writes
  previous ∈ cells ∧ (timeOfPair previous.time).value < time ∧
    ∀ cell ∈ cells, cell.address = previous.address → (timeOfPair cell.time).value < time →
      (timeOfPair cell.time).value ≤ (timeOfPair previous.time).value

/-- The native transfer as a Clean access. Times are shifted by one so an
    explicit initialization write can precede all real accesses at time zero. -/
def transferEvent (edge : MemoryToken p × MemoryToken p) : MemoryAccess :=
  ((timeOfPair edge.2.time).value + 1, edge.1.address, edge.1.value, edge.2.value)

/-- Clean's chronological memory semantics for one address, with its public
    initial value written first. The history contains every native access. -/
def CellHistory [Fact p.Prime] (trace : Data p) (source : MemoryToken p)
    (history : TimestampSortedMemoryAccessList) : Prop :=
  List.Perm history.val ((0, source.address, 0, source.value) ::
    (trace.memorySteps.filter fun edge => edge.1.address = source.address).map transferEvent) ∧
    MemoryAccessList.isConsistentOnline history.val history.property

/-- Write times of all imported memory ports, including readonly clock refreshes. -/
def Data.accessTimes [Fact p.Prime] (trace : Data p) : List Nat :=
  trace.rows.flatMap fun row => row.ports.toList.map fun port =>
    (decodeTimestamp row.assignment row.columns.initialTime).value + port.clock.offset

end Airbender.Trace
