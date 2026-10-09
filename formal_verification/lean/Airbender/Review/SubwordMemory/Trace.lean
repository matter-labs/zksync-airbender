import Airbender.Review.SubwordMemory.Decoder
import Airbender.Review.Trace.Model

namespace Airbender.SubwordMemory

inductive TraceKind where
  | subwordMemory
  deriving DecidableEq

instance : Trace.CircuitLayout TraceKind where
  columns _ := importedConstraintsTraceColumns
  ports _ := importedConstraintsMemoryPorts
  decoderColumns _ := importedConstraintsDecoderColumns
  constraints _ setup := clockConstraints setup

@[simp] theorem trace_columns (kind : TraceKind) :
    Trace.CircuitLayout.columns kind = importedConstraintsTraceColumns := rfl

@[simp] theorem trace_ports (kind : TraceKind) :
    Trace.CircuitLayout.ports kind = importedConstraintsMemoryPorts := rfl

@[simp] theorem trace_decoder_columns (kind : TraceKind) :
    Trace.CircuitLayout.decoderColumns kind = importedConstraintsDecoderColumns := rfl

@[simp] theorem trace_constraints [Fact p.Prime] (kind : TraceKind)
    (rom : Table (ZMod p) (fields 9)) :
    Trace.CircuitLayout.constraints kind rom = clockConstraints rom := rfl

abbrev NativeTrace (p : Nat) [Fact p.Prime] := Trace.Data p TraceKind

/-- Logical decoder membership is tied to the actual public program image. -/
def Decoded {p : Nat} [Fact p.Prime] (trace : NativeTrace p) (program : List ProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (decoderTable program).Contains #[] (decoderQuery row.assignment)

end Airbender.SubwordMemory
