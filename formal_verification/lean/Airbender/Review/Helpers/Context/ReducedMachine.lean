import Airbender.Review.Helpers.Context.Model
import Airbender.Review.Circuits.ReducedMachine.NativeArtifact

namespace Airbender.Trace
set_option autoImplicit false

/-- The actual regenerated monolithic v2 reduced artifact, separate from the historical JSON. -/
inductive NativeReducedFamily
  | reduced
  deriving DecidableEq

instance : CircuitLayout NativeReducedFamily where
  columns | .reduced => ReducedMachine.Native.importedConstraintsTraceColumns
  ports | .reduced => ReducedMachine.Native.importedConstraintsMemoryPorts
  decoderColumns | .reduced => ReducedMachine.Native.importedConstraintsDecoderColumns
  Setup := fun p _ => Table (ZMod p) (fields 4)
  constraints | .reduced, setup => ReducedMachine.Native.importedConstraints setup

end Airbender.Trace
