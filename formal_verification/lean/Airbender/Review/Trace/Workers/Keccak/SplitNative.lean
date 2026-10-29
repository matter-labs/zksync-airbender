import Airbender.Review.Circuits.Keccak.SplitColumnParity
import Airbender.Review.Circuits.Keccak.SplitThetaRho
import Airbender.Review.Circuits.Keccak.SplitChi5
import Airbender.Review.Circuits.Keccak.SplitColumnParityCached
import Airbender.Review.Circuits.Keccak.SplitThetaRhoCached
import Airbender.Review.Circuits.Keccak.SplitChi5Cached
import Airbender.Review.Trace.Workers.Keccak.SplitSchedule
import Airbender.Review.Helpers.Delegation.Memory

namespace Airbender.Keccak.Split.Native

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

/-- The native-equation slice for every supplied split-worker row. Participation,
caller/request permutation, grouped memory ports, setup provenance and functional
effect remain separate obligations of the full-machine target. -/
structure EquationsHold [Fact p.Prime] (cached : Bool) (setup : Setup p)
    (rows : List (Row p)) : Prop where
  rowsHold : ∀ row ∈ rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints cached setup)

end Airbender.Keccak.Split.Native
