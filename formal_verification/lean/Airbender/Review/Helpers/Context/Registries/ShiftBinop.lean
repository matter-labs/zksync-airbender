import Airbender.Review.Circuits.ShiftBinop.Decoder
import Airbender.Review.Helpers.Context.Model

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

/-- Membership in the table constructed from actual public Sail bytes. -/
def Decoded {p : Nat} [Fact p.Prime] (trace : NativeTrace p)
    (program : List ProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (decoderTable program).Contains #[] (decoderQuery row.assignment)

end Airbender.ShiftBinop
