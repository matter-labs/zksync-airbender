import Airbender.Review.Helpers.Context.Model
import Airbender.Review.Circuits.WordMemory.Artifact

namespace Airbender.Trace

/-- Separate checked native registry while initialized word-memory/Sail assembly
    is pending. The arithmetic execution registry is unchanged. -/
inductive WordMemoryFamily where
  | wordMemory
  deriving DecidableEq

instance : CircuitLayout WordMemoryFamily where
  columns | .wordMemory => WordMemory.importedConstraintsTraceColumns
  ports | .wordMemory => WordMemory.importedConstraintsMemoryPorts
  decoderColumns | .wordMemory => WordMemory.importedConstraintsDecoderColumns
  Setup := fun _ _ => Verification.WordROM
  constraints | .wordMemory, rom => WordMemory.importedConstraints rom

end Airbender.Trace
