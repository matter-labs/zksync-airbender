import Airbender.Review.Trace.Model
import Airbender.Review.JumpBranchSlt.Artifact
import Airbender.Review.MulDiv.Artifact
import Airbender.Review.ShiftBinop.Artifact
import Airbender.Review.SubwordMemory.Artifact

namespace Airbender.Trace

/-- The six families admitted by the integrated claim. Their imported rows
    share one PC/timestamp path and one initialized register/RAM history. -/
inductive PooledFamily where
  | addSub | wordMemory | jumpBranchSlt | mulDiv | shiftBinop | subwordMemory
  deriving DecidableEq

/-- Keep the two distinct modeled table schemas. Merging their rows would
    change the enforced lookup relation. Fixed range/operation tables remain
    inside each imported artifact. -/
structure PooledSetup (p : Nat) [Fact p.Prime] where
  /-- Modeled nine-column word-ROM setup; bound to public cell values by the inputs. -/
  wordMemory : Table (ZMod p) (fields 9)
  /-- Modeled tagged subword setup, including ROM rows bound to public bytes. -/
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

/-- A `Data` trace using the six-family registry and its two modeled setup
    tables. `Accepted` checks constraints/matching; soundness supplies execution. -/
abbrev PooledTrace (p : Nat) [Fact p.Prime] := Data p PooledFamily

end Airbender.Trace
