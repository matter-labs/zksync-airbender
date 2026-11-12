module
public import Human.Circuits.JumpBranchSlt.Decoder
public import Human.Helpers.Context.Model

@[expose] public section

namespace Airbender.JumpBranchSlt

/-- Scope tag for traces of this family, using the shared native trace model. -/
inductive TraceKind where
  | jumpBranchSlt
  deriving DecidableEq

instance : Trace.CircuitLayout TraceKind where
  columns _ := importedConstraintsTraceColumns
  ports _ := importedConstraintsMemoryPorts
  decoderColumns _ := importedConstraintsDecoderColumns
  constraints _ _ := clockConstraints

abbrev NativeTrace (p : Nat) [Fact p.Prime] := Trace.Data p TraceKind

end Airbender.JumpBranchSlt
