import Human.Circuits.SubwordMemory.Decoder
import Human.Helpers.Context.Model

namespace Airbender.SubwordMemory

inductive TraceKind where
  | subwordMemory
  deriving DecidableEq

instance : Trace.CircuitLayout TraceKind where
  columns _ := importedConstraintsTraceColumns
  ports _ := importedConstraintsMemoryPorts
  decoderColumns _ := importedConstraintsDecoderColumns
  constraints _ setup := clockConstraints setup

abbrev NativeTrace (p : Nat) [Fact p.Prime] := Trace.Data p TraceKind

end Airbender.SubwordMemory
