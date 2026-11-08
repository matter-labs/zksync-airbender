module
public import Human.Circuits.MulDiv.Decoder
public import Human.Helpers.Context.Model

@[expose] public section

namespace Airbender.MulDiv

inductive TraceKind where
  | mulDiv
  deriving DecidableEq

instance : Trace.CircuitLayout TraceKind where
  columns _ := importedConstraintsTraceColumns
  ports _ := importedConstraintsMemoryPorts
  decoderColumns _ := importedConstraintsDecoderColumns
  constraints _ _ := clockConstraints

abbrev NativeTrace (p : Nat) [Fact p.Prime] := Trace.Data p TraceKind

end Airbender.MulDiv
