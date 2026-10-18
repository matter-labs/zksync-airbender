import Airbender.Review.Helpers.Context.Model
import Airbender.Review.Circuits.JumpBranchSlt.Artifact

namespace Airbender.Trace

/-- Checked native registry for control decoding and initialized logical
    history. Original Sail control execution remains a separate connection. -/
inductive JumpBranchSltFamily where
  | jumpBranchSlt
  deriving DecidableEq

instance : CircuitLayout JumpBranchSltFamily where
  columns | .jumpBranchSlt => JumpBranchSlt.importedConstraintsTraceColumns
  ports | .jumpBranchSlt => JumpBranchSlt.importedConstraintsMemoryPorts
  decoderColumns | .jumpBranchSlt => JumpBranchSlt.importedConstraintsDecoderColumns
  constraints | .jumpBranchSlt, _ => JumpBranchSlt.importedConstraints

end Airbender.Trace
