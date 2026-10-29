import Airbender.Review.Circuits.Keccak.SplitColumnParity
import Airbender.Review.Circuits.Keccak.SplitThetaRho
import Airbender.Review.Circuits.Keccak.SplitChi5
import Airbender.Review.Circuits.Keccak.SplitColumnParityCached
import Airbender.Review.Circuits.Keccak.SplitThetaRhoCached
import Airbender.Review.Circuits.Keccak.SplitChi5Cached
import Airbender.Review.Trace.Workers.Keccak.SplitSchedule
import Airbender.Review.Helpers.Delegation.Memory

namespace Airbender.Keccak.Split.Native
open Airbender.Trace

/-- The program-independent fixed setup tables supplied to the three split
worker circuits. Their different native row widths are retained here. -/
structure Setup (p : Nat) where
  columnParity : Table (ZMod p) (fields 8)
  thetaRho : Table (ZMod p) (fields 9)
  chi5 : Table (ZMod p) (fields 11)

/-- One actual split-worker assignment and its selected compiled circuit. No
result, reference state or expected memory effect is stored in this record. -/
structure Row (p : Nat) where
  kind : Kind
  assignment : Nat → ZMod p

/-- Every native register and RAM port in JSON order. A split timestamp group
may own several ports; the importer checks that each port has one owner and
retains the group's actual previous-time limbs and borrow on each port. -/
def Row.ports (cached : Bool) (row : Row p) : Array Airbender.Trace.MemoryPort :=
  match cached, row.kind with
  | false, .columnParity => ColumnParity.importedConstraintsMemoryPorts
  | false, .thetaRho => ThetaRho.importedConstraintsMemoryPorts
  | false, .chi5 => Chi5.importedConstraintsMemoryPorts
  | true, .columnParity => ColumnParityCached.importedConstraintsMemoryPorts
  | true, .thetaRho => ThetaRhoCached.importedConstraintsMemoryPorts
  | true, .chi5 => Chi5Cached.importedConstraintsMemoryPorts

/-- Actual execute and invocation-clock columns of the selected compiled
worker. Theta/rho and chi5 retain the checked grouped previous timestamps. -/
def Row.columns (cached : Bool) (row : Row p) : Delegation.ClockColumns :=
  match cached, row.kind with
  | false, .columnParity => ColumnParity.importedConstraintsDelegationColumns
  | false, .thetaRho => ThetaRho.importedConstraintsDelegationColumns
  | false, .chi5 => Chi5.importedConstraintsDelegationColumns
  | true, .columnParity => ColumnParityCached.importedConstraintsDelegationColumns
  | true, .thetaRho => ThetaRhoCached.importedConstraintsDelegationColumns
  | true, .chi5 => Chi5Cached.importedConstraintsDelegationColumns

/-- Dispatch every split worker to the exact imported compiled equations,
fixed lookup queries and timestamp queries for its public cache mode. -/
def Row.constraints [Fact p.Prime] (cached : Bool) (setup : Setup p)
    (row : Row p) : List (FlatOperation (ZMod p)) :=
  match cached, row.kind with
  | false, .columnParity => ColumnParity.clockConstraints setup.columnParity
  | false, .thetaRho => ThetaRho.clockConstraints setup.thetaRho
  | false, .chi5 => Chi5.clockConstraints setup.chi5
  | true, .columnParity => ColumnParityCached.clockConstraints setup.columnParity
  | true, .thetaRho => ThetaRhoCached.clockConstraints setup.thetaRho
  | true, .chi5 => Chi5Cached.clockConstraints setup.chi5

/-- Preserve the full raw invocation limbs, the imported port offset and the
port's native write value. No word or timestamp range is assumed here. -/
def Row.writeToken (cached : Bool) (row : Row p) (port : MemoryPort) : MemoryToken p :=
  let base := rawPair row.assignment (row.columns cached).invocation
  ⟨port.address.code row.assignment, (base.1 + port.clock.offset, base.2),
    port.writeCode row.assignment⟩

def Row.memorySteps (cached : Bool) (row : Row p) :
    List (MemoryToken p × MemoryToken p) :=
  (row.ports cached).toList.map fun port =>
    (readToken row.assignment port, row.writeToken cached port)

/-- The three physical worker pools share a single native memory-token
boundary. `cached` chooses a complete compiled capture family, while each row
selects its worker kind. -/
structure MemoryData (p : Nat) where
  cached : Bool
  setup : Setup p
  rows : List (Row p)
  initial : List (MemoryToken p)
  terminal : List (MemoryToken p)

def MemoryData.steps (data : MemoryData p) : List (MemoryToken p × MemoryToken p) :=
  data.rows.flatMap (Row.memorySteps data.cached)

/-- The native-equation slice for every supplied split-worker row. Participation,
caller/request permutation, memory matching, setup provenance and functional
effect remain separate obligations of the full-machine target. -/
structure EquationsHold [Fact p.Prime] (cached : Bool) (setup : Setup p)
    (rows : List (Row p)) : Prop where
  rowsHold : ∀ row ∈ rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints cached setup)

/-- Imported equations, participation and exact logical memory matching for
the split worker pool. Caller/request matching and the reference effect are
separate proof obligations; this structure does not assert either result. -/
structure MemoryAccepted [Fact p.Prime] (data : MemoryData p) : Prop where
  equations : EquationsHold data.cached data.setup data.rows
  active : ∀ row ∈ data.rows, row.assignment (row.columns data.cached).execute = 1
  matching : (data.initial ++ data.steps.map Prod.snd).Perm
    (data.terminal ++ data.steps.map Prod.fst)

end Airbender.Keccak.Split.Native
