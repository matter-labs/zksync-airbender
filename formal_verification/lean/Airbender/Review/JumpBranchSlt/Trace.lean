import Airbender.Review.JumpBranchSlt.Decoder
import Airbender.Review.Trace.Model

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

@[simp] theorem trace_columns (kind : TraceKind) :
    Trace.CircuitLayout.columns kind = importedConstraintsTraceColumns := rfl

@[simp] theorem trace_ports (kind : TraceKind) :
    Trace.CircuitLayout.ports kind = importedConstraintsMemoryPorts := rfl

@[simp] theorem trace_decoder_columns (kind : TraceKind) :
    Trace.CircuitLayout.decoderColumns kind = importedConstraintsDecoderColumns := rfl

@[simp] theorem trace_constraints [Fact p.Prime] (kind : TraceKind)
    (rom : Table (ZMod p) (fields 9)) :
    Trace.CircuitLayout.constraints kind rom = clockConstraints := rfl

abbrev NativeTrace (p : Nat) [Fact p.Prime] := Trace.Data p TraceKind

/-- Logical membership of every native query in the public decoded image. -/
def Decoded {p : Nat} [Fact p.Prime] (trace : NativeTrace p)
    (program : List ProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (decoderTable program).Contains #[] (decoderQuery row.assignment)

end Airbender.JumpBranchSlt
