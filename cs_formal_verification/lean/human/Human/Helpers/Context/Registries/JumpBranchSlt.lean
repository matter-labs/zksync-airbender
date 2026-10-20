import Human.Circuits.JumpBranchSlt.Decoder
import Human.Helpers.Context.Model

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

/-- Logical membership of every native query in the public decoded image. -/
def Decoded {p : Nat} [Fact p.Prime] (trace : NativeTrace p)
    (program : List ProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (decoderTable program).Contains #[] (decoderQuery row.assignment)

end Airbender.JumpBranchSlt
