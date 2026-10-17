import Airbender.Review.Helpers.Context.Model
import Airbender.Review.Circuits.WordMemory.Artifact

namespace Airbender.Trace

/-- Checked native registry for word-memory decoding and initialized logical
    history. Sail assembly remains pending; arithmetic execution is unchanged. -/
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
