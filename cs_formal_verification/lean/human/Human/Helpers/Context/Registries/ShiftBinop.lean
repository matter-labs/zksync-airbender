import Human.Circuits.ShiftBinop.Decoder
import Human.Helpers.Context.Model

namespace Airbender.ShiftBinop

inductive TraceKind where
  | shiftBinop
  deriving DecidableEq

instance : Trace.CircuitLayout TraceKind where
  columns _ := importedConstraintsTraceColumns
  ports _ := importedConstraintsMemoryPorts
  decoderColumns _ := importedConstraintsDecoderColumns
  constraints _ _ := clockConstraints

abbrev NativeTrace (p : Nat) [Fact p.Prime] := Trace.Data p TraceKind

end Airbender.ShiftBinop
