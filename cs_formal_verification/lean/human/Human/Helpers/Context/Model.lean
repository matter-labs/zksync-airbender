module
public import Human.Helpers.Context.Columns
public import Human.Helpers.Context.PCState.Model
public import Human.Helpers.Context.Timestamps
public import Human.Helpers.Decoder.Columns
public import Human.Helpers.Memory.Ports
public import Human.Helpers.Properties

@[expose] public section

namespace Airbender.Trace

/-- The restricted ADD/SUB + word-memory scope. `PooledFamily` extends it to six families. -/
inductive Family where
  | addSub | wordMemory
  deriving DecidableEq

/-- Connect each circuit family to its imported columns, memory ports, decoder
    placement and Clean constraints. `Kind` selects the admitted families;
    `Setup` supplies their modeled lookup tables. This registry identifies the
    artifact used by `Row`; it does not assert that the circuit implements RV32. -/
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
    their starting values to the public RV state. -/
structure Data (p : Nat) (Kind : Type := Family) [CircuitLayout Kind] [Fact p.Prime] where
  /-- All participating active rows; list order need not be execution order. -/
  rows : List (Row p Kind)
  /-- Modeled setup table or table bundle; `rom` is the historical field name. -/
  rom : CircuitLayout.Setup (Kind := Kind) p
  /-- Starting PC and machine timestamp, bound to the public RV starting state. -/
  initial : PCState.State p
  /-- Claimed final PC and machine timestamp, checked by trace soundness. -/
  terminal : PCState.State p
  /-- Seed values and prior timestamps for the public tracked cell domain. -/
  initialMemory : List (MemoryToken p)
  /-- Final tokens whose register/RAM values must match the resulting RV state. -/
  terminalMemory : List (MemoryToken p)

/-- Check the imported constraints and logical state/memory matching for
    `trace`. Every listed row is active. Matching uses the actual imported
    tokens; no expected read, decoded instruction or execution result is given.

    Public image binding is supplied by `RVNativeInputs` or `RVPooledBootInputs`.
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

/-- The native transfer as a Clean access. Times are shifted by one so an
    explicit initialization write can precede all real accesses at time zero. -/
def transferEvent (edge : MemoryToken p × MemoryToken p) : MemoryAccess :=
  ((timeOfPair edge.2.time).value + 1, edge.1.address, edge.1.value, edge.2.value)

end Airbender.Trace
