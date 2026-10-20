import Human.Circuits.AddSub.Artifact
import Human.Circuits.WordMemory.Artifact
import Human.Helpers.Context.PCState.Model
import Human.Helpers.Properties

namespace Airbender.Trace

/-- The restricted ADD/SUB + word-memory scope. `PooledFamily` extends it to six families. -/
inductive Family where
  | addSub | wordMemory
  deriving DecidableEq

/-- Connect each circuit family to its imported columns, memory ports, decoder
    placement and Clean constraints. `Kind` selects the admitted families;
    `Setup` supplies their modeled lookup tables. This registry identifies the
    artifact used by `Row`; it does not assert that the circuit implements Sail. -/
class CircuitLayout (Kind : Type) where
  /-- Imported execute, PC and clock variable IDs for the chosen family. -/
  columns : Kind → TraceColumns
  /-- Imported register/RAM access descriptors, in their native port order. -/
  ports : Kind → Array MemoryPort
  /-- Imported variables forming this family's decoder query. -/
  decoderColumns : Kind → DecoderColumns
  /-- A pooled trace keeps each family's actual modeled setup. Existing scopes
      use one nine-column table; mixed scopes may supply a table bundle. -/
  Setup : (p : Nat) → [Fact p.Prime] → Type := fun p _ => Table (ZMod p) (fields 9)
  /-- The richer imported Clean constraints, including clock lookups. -/
  constraints : {p : Nat} → [Fact p.Prime] → Kind → Setup p →
    List (FlatOperation (ZMod p))

instance : CircuitLayout Family where
  columns
    | .addSub => AddSub.importedConstraintsTraceColumns
    | .wordMemory => WordMemory.importedConstraintsTraceColumns
  ports
    | .addSub => AddSub.importedConstraintsMemoryPorts
    | .wordMemory => WordMemory.importedConstraintsMemoryPorts
  decoderColumns
    | .addSub => AddSub.importedConstraintsDecoderColumns
    | .wordMemory => WordMemory.importedConstraintsDecoderColumns
  constraints
    | .addSub, _ => AddSub.clockConstraints
    | .wordMemory, rom => WordMemory.clockConstraints rom

/-- One circuit row: `family` selects its imported artifact, and `assignment`
    maps JSON variable IDs to field values. Bounds and instruction behavior are
    proved from acceptance, public initialization and decoder membership. -/
structure Row (p : Nat) (Kind : Type := Family) where
  family : Kind
  assignment : Nat → ZMod p

variable {Kind : Type} [CircuitLayout Kind]

def Row.columns (row : Row p Kind) : TraceColumns :=
  CircuitLayout.columns row.family

def Row.ports (row : Row p Kind) : Array MemoryPort :=
  CircuitLayout.ports row.family

def Row.decoderColumns (row : Row p Kind) : DecoderColumns :=
  CircuitLayout.decoderColumns row.family

def Row.constraints [Fact p.Prime] (row : Row p Kind)
    (rom : CircuitLayout.Setup (Kind := Kind) p) :
    List (FlatOperation (ZMod p)) :=
  CircuitLayout.constraints row.family rom

def rawPair (w : Nat → ZMod p) (columns : Vector Nat 2) : ZMod p × ZMod p :=
  (w columns[0], w columns[1])

def timeOfPair (time : ZMod p × ZMod p) : Timestamp := ⟨time.1.val, time.2.val⟩

/-- Read the row's initial PC and timestamp from imported columns. The raw
    field pairs preserve the witness values; this definition imposes no ranges. -/
def Row.start (row : Row p Kind) : PCState.State p :=
  ⟨rawPair row.assignment row.columns.initialPC, rawPair row.assignment row.columns.initialTime⟩

/-- Native instruction time, read from the imported initial-clock columns. -/
def Row.clock (row : Row p Kind) : Nat :=
  (decodeTimestamp row.assignment row.columns.initialTime).value

/-- Read the row's final PC and timestamp. `Accepted.states` connects this
    endpoint to another row's start or the public terminal boundary. -/
def Row.finish (row : Row p Kind) : PCState.State p :=
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

def Row.reads (row : Row p Kind) : List (MemoryToken p) :=
  row.ports.toList.map (readToken row.assignment)

def Row.writes (row : Row p Kind) : List (MemoryToken p) :=
  row.ports.toList.map (writeToken row.columns row.assignment)

/-- Each imported port transfers its previous cell to a freshly timestamped cell.
    Readonly ports preserve the value while refreshing the timestamp. -/
def Row.memorySteps (row : Row p Kind) : List (MemoryToken p × MemoryToken p) :=
  row.ports.toList.map fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)

/-- Native trace data, before any correctness claim. `rows` may be unordered;
    the proofs recover clock order from `Accepted`. PC/state and memory tokens
    come from the imported columns. The public initialization records bind
    their starting values to Sail. -/
structure Data (p : Nat) (Kind : Type := Family) [CircuitLayout Kind] [Fact p.Prime] where
  /-- All participating active rows; list order need not be execution order. -/
  rows : List (Row p Kind)
  /-- Modeled setup table or table bundle; `rom` is the historical field name. -/
  rom : CircuitLayout.Setup (Kind := Kind) p
  /-- Starting PC and machine timestamp, bound to the public Sail state. -/
  initial : PCState.State p
  /-- Claimed final PC and machine timestamp, checked by trace soundness. -/
  terminal : PCState.State p
  /-- Seed values and prior timestamps for the public tracked cell domain. -/
  initialMemory : List (MemoryToken p)
  /-- Final tokens whose register/RAM values must match the resulting Sail state. -/
  terminalMemory : List (MemoryToken p)

def Data.memorySteps [Fact p.Prime] (trace : Data p Kind) : List (MemoryToken p × MemoryToken p) :=
  trace.rows.flatMap Row.memorySteps

/-- Check the imported constraints and logical state/memory matching for
    `trace`. Every listed row is active. Matching uses the actual imported
    tokens; no expected read, decoded instruction or execution result is given.

    Public image binding is supplied by `NativeInputs` or `PooledBootInputs`.
    Cryptographic enforcement of these permutations remains outside this claim. -/
structure Accepted [Fact p.Prime] (trace : Data p Kind) : Prop where
  /-- Every row satisfies its actual imported equations and lookups. -/
  constraints : ∀ row ∈ trace.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints trace.rom)
  /-- Each participating row's imported execute flag is one. -/
  active : ∀ row ∈ trace.rows, row.assignment row.columns.execute = 1
  /-- Row ends plus the initial state match row starts plus the terminal state. -/
  states : (trace.initial :: trace.rows.map Row.finish).Perm
    (trace.terminal :: trace.rows.map Row.start)
  /-- Native writes plus seed tokens match native reads plus final tokens. -/
  memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
    (trace.terminalMemory ++ trace.rows.flatMap Row.reads)

/-- Public starting clock conditions for `trace`. These bound only the initial
    machine clock and seed timestamps. Shared history and imported equations
    derive the clocks of individual rows and accesses. -/
structure ClockBoundary [Fact p.Prime] (trace : Data p Kind) : Prop where
  /-- Both initial machine-clock limbs are below the 19-bit base. -/
  initial : (timeOfPair trace.initial.timestamp).Bounded
  /-- The initial machine clock is a multiple of the four-tick instruction stride. -/
  aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0
  /-- Both prior-clock limbs of every seed token are below the 19-bit base. -/
  memory : ∀ token ∈ trace.initialMemory, (timeOfPair token.time).Bounded

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

/-- A native read uses the newest preceding cell at its address, drawn from the
    initial image or a native write. This is a conclusion, not an interface premise. -/
def LatestRead [Fact p.Prime] (trace : Data p Kind) (row : Row p Kind) (port : MemoryPort) : Prop :=
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
