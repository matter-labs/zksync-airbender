import Airbender.Review.AddSub.Artifact
import Airbender.Review.WordMemory.Artifact
import Airbender.Review.PCState.Model
import Airbender.Review.Properties

namespace Airbender.Trace

inductive Family where
  | addSub | wordMemory

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

def Row.reads (row : Row p) : List (MemoryToken p) :=
  row.ports.toList.map fun port =>
    ⟨port.address.code row.assignment, rawPair row.assignment port.clock.previous,
      port.readCode row.assignment⟩

def Row.writes (row : Row p) : List (MemoryToken p) :=
  row.ports.toList.map fun port =>
    let base := rawPair row.assignment row.columns.initialTime
    ⟨port.address.code row.assignment, (base.1 + port.clock.offset, base.2),
      port.writeCode row.assignment⟩

structure Data (p : Nat) [Fact p.Prime] where
  rows : List (Row p)
  rom : Table (ZMod p) (fields 9)
  initial : PCState.State p
  terminal : PCState.State p
  initialMemory : List (MemoryToken p)
  terminalMemory : List (MemoryToken p)

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

/-- Write times of all imported memory ports, including readonly clock refreshes. -/
def Data.accessTimes [Fact p.Prime] (trace : Data p) : List Nat :=
  trace.rows.flatMap fun row => row.ports.toList.map fun port =>
    (decodeTimestamp row.assignment row.columns.initialTime).value + port.clock.offset

end Airbender.Trace
