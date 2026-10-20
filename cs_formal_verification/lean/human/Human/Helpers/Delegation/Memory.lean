import Human.Circuits.Bigint.Artifact
import Human.Circuits.Blake2G.Artifact
import Human.Circuits.Blake2Round.Artifact
import Human.Circuits.Keccak.Artifact
import Human.Helpers.Memory.InitialImage

namespace Airbender.Delegation
open Trace

/-- The four imported delegation layouts. Their clocks and ports share one
    memory-history proof; operation-specific arithmetic stays in each family. -/
inductive Family where
  | bigint | blakeG | blakeRound | keccak
  deriving DecidableEq

/-- Current modeled table interfaces. These are the tables already supplied
    to each imported circuit, including the shared timestamp range table. -/
structure Setup (p : Nat) where
  bigint : Table (ZMod p) (fields 3)
  blakeG : Table (ZMod p) (fields 9)
  blakeRound : Table (ZMod p) (fields 4)
  keccak : Table (ZMod p) (fields 8)

/-- One actual delegation assignment and its family. No reads, ranges or
    expected operation result are supplied by this record. -/
structure Row (p : Nat) where
  family : Family
  assignment : Nat → ZMod p

def Row.columns (row : Row p) : ClockColumns :=
  match row.family with
  | .bigint => Bigint.importedConstraintsDelegationColumns
  | .blakeG => Blake2G.importedConstraintsDelegationColumns
  | .blakeRound => Blake2Round.importedConstraintsDelegationColumns
  | .keccak => Keccak.importedConstraintsDelegationColumns

/-- All fixed-register and indirect RAM ports, in the JSON's native order. -/
def Row.ports (row : Row p) : Array MemoryPort :=
  match row.family with
  | .bigint => Bigint.importedConstraintsMemoryPorts
  | .blakeG => Blake2G.importedConstraintsMemoryPorts
  | .blakeRound => Blake2Round.importedConstraintsMemoryPorts
  | .keccak => Keccak.importedConstraintsMemoryPorts

def Row.constraints [Fact p.Prime] (row : Row p) (setup : Setup p) :
    List (FlatOperation (ZMod p)) :=
  match row.family with
  | .bigint => Bigint.clockConstraints setup.bigint
  | .blakeG => Blake2G.clockConstraints setup.blakeG
  | .blakeRound => Blake2Round.clockConstraints setup.blakeRound
  | .keccak => Keccak.clockConstraints setup.keccak

/-- A delegation has no next machine clock. Its writes use the imported
    invocation clock plus each port's offset (two for these four layouts). -/
def Row.writeToken (row : Row p) (port : MemoryPort) : MemoryToken p :=
  let base := rawPair row.assignment row.columns.invocation
  ⟨port.address.code row.assignment, (base.1 + port.clock.offset, base.2),
    port.writeCode row.assignment⟩

def Row.memorySteps (row : Row p) : List (MemoryToken p × MemoryToken p) :=
  row.ports.toList.map fun port => (readToken row.assignment port, row.writeToken port)

/-- An unordered pool of native delegation accesses and its boundary tokens.
    Shared matching keeps raw address, value and timestamp limbs intact. -/
structure MemoryData (p : Nat) where
  setup : Setup p
  rows : List (Row p)
  initial : List (MemoryToken p)
  terminal : List (MemoryToken p)

def MemoryData.steps (data : MemoryData p) := data.rows.flatMap Row.memorySteps

/-- Imported equations/queries and exact logical memory-token matching.
    This remains a logical permutation boundary, not a cryptographic proof. -/
structure MemoryAccepted [Fact p.Prime] (data : MemoryData p) : Prop where
  constraints : ∀ row ∈ data.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints data.setup)
  matching : (data.initial ++ data.steps.map Prod.snd).Perm
    (data.terminal ++ data.steps.map Prod.fst)

/-- Public initialization reads actual Sail cells, with one seed per address.
    Invocation timestamps have room for the native offset two. This permits
    the caller's `1 mod 4` invocations and `3 mod 4` writes; low-limb rollover and request binding remain
    explicit boundaries. Previous-access ranges are proved internally. -/
structure MemoryInputs (data : MemoryData p) (before : Reference.RiscV.Sail.State)
    (cells : List Cell) : Prop where
  initialization : initialImage before cells = some data.initial
  distinct : (cells.map Cell.addressCode).Nodup
  clockRoom : ∀ row ∈ data.rows,
    (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase

/-- Native access order and complete per-address paths. Every path starts at
    a public seed, ends at a declared terminal token and contains exactly that
    address's imported accesses. It therefore determines each read's predecessor. -/
structure MemoryEffects (data : MemoryData p) : Prop where
  clocks : ∀ edge ∈ data.steps,
    (timeOfPair edge.1.time).Bounded ∧ (timeOfPair edge.2.time).Bounded
  order : ∀ edge ∈ data.steps,
    (timeOfPair edge.1.time).value < (timeOfPair edge.2.time).value
  paths : ∀ source ∈ data.initial, ∃ sink ∈ data.terminal, sink.address = source.address ∧
    ∃ path : List (MemoryToken p), path.head? = some source ∧ path.getLast? = some sink ∧
      (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
      (path.zip path.tail).Perm (data.steps.filter fun edge => edge.1.address = source.address)

/-- The complete logical memory claim for a delegation pool. Addresses come
    from public initialized cells, and each native access belongs to a Clean
    latest-write/read history. Caller/operation/ABI execution is a later connection. -/
structure MemorySoundness (data : MemoryData p) : Prop where
  effects : MemoryEffects data
  addresses : ∀ row ∈ data.rows, ∀ port ∈ row.ports,
    (port.address.word row.assignment).Bounded
  histories : ∀ source ∈ data.initial, ∃ history : TimestampSortedMemoryAccessList,
    history.val.Perm ((0, source.address, 0, source.value) ::
      (data.steps.filter fun edge => edge.1.address = source.address).map transferEvent) ∧
    MemoryAccessList.isConsistentOnline history.val history.property

end Airbender.Delegation
