import Airbender.Review.Helpers.Context.Model
import Airbender.Review.Circuits.SubwordMemory.Artifact

namespace Airbender.Trace
set_option autoImplicit false

/-- Checked native registry for subword-memory decoding and initialized logical
    history. Packed-key normalization and original Sail execution remain separate. -/
inductive SubwordMemoryFamily where
  | subwordMemory
  deriving DecidableEq

instance : CircuitLayout SubwordMemoryFamily where
  columns | .subwordMemory => SubwordMemory.importedConstraintsTraceColumns
  ports | .subwordMemory => SubwordMemory.importedConstraintsMemoryPorts
  decoderColumns | .subwordMemory => SubwordMemory.importedConstraintsDecoderColumns
  Setup := fun _ _ => Verification.WordROM
  constraints | .subwordMemory, rom => SubwordMemory.importedConstraints rom

end Airbender.Trace
