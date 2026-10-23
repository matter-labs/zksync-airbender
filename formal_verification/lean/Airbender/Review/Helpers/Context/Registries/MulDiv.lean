import Airbender.Review.Circuits.MulDiv.Decoder
import Airbender.Review.Helpers.Context.Registries.FixedFamily

namespace Airbender.MulDiv

inductive TraceKind where
  | mulDiv
  deriving DecidableEq

instance : Trace.CircuitLayout TraceKind :=
  Trace.CircuitLayout.fixedFamily importedConstraintsTraceColumns
    importedConstraintsMemoryPorts importedConstraintsDecoderColumns (@clockConstraints)

abbrev NativeTrace (p : Nat) [Fact p.Prime] := Trace.Data p TraceKind

/-- Logical membership in the table constructed from public Sail bytes. -/
def Decoded {p : Nat} [Fact p.Prime] (trace : NativeTrace p)
    (program : List ProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (decoderTable program).Contains #[] (decoderQuery row.assignment)

end Airbender.MulDiv
