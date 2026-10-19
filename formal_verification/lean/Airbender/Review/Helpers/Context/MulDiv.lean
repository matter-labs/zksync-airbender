import Airbender.Review.Helpers.Context.Model
import Airbender.Review.Circuits.MulDiv.Artifact

namespace Airbender.Trace

/-- Checked native registry for unsigned mul/div decoding and initialized logical
    history. Original Sail mul/div execution remains a separate connection. -/
inductive MulDivFamily where
  | mulDiv
  deriving DecidableEq

instance : CircuitLayout MulDivFamily where
  columns | .mulDiv => MulDiv.importedConstraintsTraceColumns
  ports | .mulDiv => MulDiv.importedConstraintsMemoryPorts
  decoderColumns | .mulDiv => MulDiv.importedConstraintsDecoderColumns
  constraints | .mulDiv, _ => MulDiv.importedConstraints

end Airbender.Trace
