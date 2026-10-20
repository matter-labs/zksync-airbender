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

/-- Logical decoder membership is tied to the actual public program image. -/
def Decoded {p : Nat} [Fact p.Prime] (trace : NativeTrace p) (program : List ProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (decoderTable program).Contains #[] (decoderQuery row.assignment)

end Airbender.SubwordMemory
