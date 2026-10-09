import Airbender.Review.Trace.Model
import Airbender.Review.JumpBranchSlt.Artifact
import Airbender.Review.MulDiv.Artifact
import Airbender.Review.ShiftBinop.Artifact
import Airbender.Review.SubwordMemory.Artifact

namespace Airbender.Trace

/-- The already checked ISA families share one state/register/RAM relation. -/
inductive PooledFamily where
  | addSub | wordMemory | jumpBranchSlt | mulDiv | shiftBinop | subwordMemory
  deriving DecidableEq

/-- Keep the two distinct modeled table schemas. Merging their rows would
    change the enforced lookup relation. Fixed range/operation tables remain
    inside each imported artifact. -/
structure PooledSetup (p : Nat) [Fact p.Prime] where
  wordMemory : Table (ZMod p) (fields 9)
  subwordMemory : Table (ZMod p) (fields 9)

instance : CircuitLayout PooledFamily where
  columns
    | .addSub => AddSub.importedConstraintsTraceColumns
    | .wordMemory => WordMemory.importedConstraintsTraceColumns
    | .jumpBranchSlt => JumpBranchSlt.importedConstraintsTraceColumns
    | .mulDiv => MulDiv.importedConstraintsTraceColumns
    | .shiftBinop => ShiftBinop.importedConstraintsTraceColumns
    | .subwordMemory => SubwordMemory.importedConstraintsTraceColumns
  ports
    | .addSub => AddSub.importedConstraintsMemoryPorts
    | .wordMemory => WordMemory.importedConstraintsMemoryPorts
    | .jumpBranchSlt => JumpBranchSlt.importedConstraintsMemoryPorts
    | .mulDiv => MulDiv.importedConstraintsMemoryPorts
    | .shiftBinop => ShiftBinop.importedConstraintsMemoryPorts
    | .subwordMemory => SubwordMemory.importedConstraintsMemoryPorts
  decoderColumns
    | .addSub => AddSub.importedConstraintsDecoderColumns
    | .wordMemory => WordMemory.importedConstraintsDecoderColumns
    | .jumpBranchSlt => JumpBranchSlt.importedConstraintsDecoderColumns
    | .mulDiv => MulDiv.importedConstraintsDecoderColumns
    | .shiftBinop => ShiftBinop.importedConstraintsDecoderColumns
    | .subwordMemory => SubwordMemory.importedConstraintsDecoderColumns
  Setup := PooledSetup
  constraints kind setup := match kind with
    | .addSub => AddSub.clockConstraints
    | .wordMemory => WordMemory.clockConstraints setup.wordMemory
    | .jumpBranchSlt => JumpBranchSlt.clockConstraints
    | .mulDiv => MulDiv.clockConstraints
    | .shiftBinop => ShiftBinop.clockConstraints
    | .subwordMemory => SubwordMemory.clockConstraints setup.subwordMemory

abbrev PooledTrace (p : Nat) [Fact p.Prime] := Data p PooledFamily

end Airbender.Trace
