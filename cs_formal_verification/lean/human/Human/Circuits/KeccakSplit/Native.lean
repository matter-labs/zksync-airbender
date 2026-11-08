module
public import Human.Circuits.KeccakSplit.ColumnParity.Artifact
public import Human.Circuits.KeccakSplit.ThetaRho.Artifact
public import Human.Circuits.KeccakSplit.Chi5.Artifact
public import Human.Circuits.KeccakSplit.Tables.Setup
public import Human.Circuits.KeccakSplit.Call
public import Human.Helpers.Memory.Values

@[expose] public section

namespace Airbender.Keccak.Split.Native
open Trace

/-- One actual split-worker assignment and its worker. No read, range or
    expected result is part of this record. -/
structure Row (p : Nat) where
  kind : Kind
  assignment : Nat → ZMod p

/-- All register and RAM ports of the worker, in the JSON's native order: x10
    (control), x11 (state pointer), then the low and high word of each lane. -/
def Row.ports (row : Row p) : Array MemoryPort :=
  match row.kind with
  | .columnParity => ColumnParity.importedConstraintsMemoryPorts
  | .thetaRho => ThetaRho.importedConstraintsMemoryPorts
  | .chi5 => Chi5.importedConstraintsMemoryPorts

/-- Execute flag and invocation clock columns of the worker. -/
def Row.columns (row : Row p) : Delegation.ClockColumns :=
  match row.kind with
  | .columnParity => ColumnParity.importedConstraintsDelegationColumns
  | .thetaRho => ThetaRho.importedConstraintsDelegationColumns
  | .chi5 => Chi5.importedConstraintsDelegationColumns

/-- The worker's imported equations and queries over its exported fixed tables. -/
noncomputable def Row.constraints [Fact p.Prime] (row : Row p) : List (FlatOperation (ZMod p)) :=
  match row.kind with
  | .columnParity => ColumnParity.clockConstraints ColumnParity.setup
  | .thetaRho => ThetaRho.clockConstraints ThetaRho.setup
  | .chi5 => Chi5.clockConstraints Chi5.setup

/-- Writes use the invocation clock plus the port's offset (two). -/
def Row.writeToken (row : Row p) (port : MemoryPort) : MemoryToken p :=
  let base := rawPair row.assignment row.columns.invocation
  ⟨port.address.code row.assignment, (base.1 + port.clock.offset, base.2),
    port.writeCode row.assignment⟩

def Row.memorySteps (row : Row p) : List (MemoryToken p × MemoryToken p) :=
  row.ports.toList.map fun port => (readToken row.assignment port, row.writeToken port)

/-- An unordered pool of split-worker rows and its boundary tokens. -/
structure MemoryData (p : Nat) where
  rows : List (Row p)
  initial : List (MemoryToken p)
  terminal : List (MemoryToken p)

def MemoryData.steps (data : MemoryData p) := data.rows.flatMap Row.memorySteps

/-- Imported equations/queries of every row and exact logical memory-token
    matching. This is a logical permutation boundary, not a cryptographic proof. -/
structure MemoryAccepted [Fact p.Prime] (data : MemoryData p) : Prop where
  constraints : ∀ row ∈ data.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) row.constraints
  matching : (data.initial ++ data.steps.map Prod.snd).Perm
    (data.terminal ++ data.steps.map Prod.fst)

/-- The word read, resp. written, by port `index`. -/
def Row.readWord (row : Row p) (index : Nat) : Arithmetic.Word :=
  match row.ports[index]? with
  | some port => (readToken row.assignment port).word
  | none => ⟨0, 0⟩

def Row.writtenWord (row : Row p) (index : Nat) : Arithmetic.Word :=
  match row.ports[index]? with
  | some port => (row.writeToken port).word
  | none => ⟨0, 0⟩

/-- Lane `lane` (ports 2 + 2·lane and 3 + 2·lane, low word first) as a 64-bit
    value; positions past the worker's lanes are zero. -/
def Row.readLanes (row : Row p) : Vector Nat 7 :=
  Vector.ofFn fun lane => if lane.val < Call.slotCount row.kind then
    (row.readWord (2 + 2 * lane.val)).value + 2 ^ 32 * (row.readWord (3 + 2 * lane.val)).value
  else 0

def Row.writtenLanes (row : Row p) : Vector Nat 7 :=
  Vector.ofFn fun lane => if lane.val < Call.slotCount row.kind then
    (row.writtenWord (2 + 2 * lane.val)).value + 2 ^ 32 * (row.writtenWord (3 + 2 * lane.val)).value
  else 0

/-- What one actual worker row does: it is some call `index` of the schedule with
    its worker; it reads that call's control word from x10 and writes the next one;
    its lane writes are the call's `Call.result` on its lane reads. Which RAM slots
    the lanes address is part of `Call.ExecutesAt`. -/
def RowEffects (row : Row p) : Prop :=
  ∃ index : Fin 361, kindAt index.val = row.kind ∧
    row.readWord 0 = ⟨controlAt index.val, 0⟩ ∧
    row.writtenWord 0 = ⟨bump (controlAt index.val), 0⟩ ∧
    Call.result index row.readLanes = row.writtenLanes

end Airbender.Keccak.Split.Native
