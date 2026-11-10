import Airbender.Review.Helpers.Context.Model

namespace Airbender.Trace.CircuitLayout

/-- Construct a constant registry from one family's concrete imported fields.
    The existing default nine-column Setup is retained. This construction does
    not identify different family tags, artifacts or decoder projections. -/
@[reducible]
def fixedFamily {Kind : Type}
    (columns : TraceColumns) (ports : Array MemoryPort)
    (decoderColumns : DecoderColumns)
    (clockConstraints : {p : Nat} → [Fact p.Prime] → List (FlatOperation (ZMod p))) :
    CircuitLayout Kind where
  columns _ := columns
  ports _ := ports
  decoderColumns _ := decoderColumns
  constraints _ _ := clockConstraints

end Airbender.Trace.CircuitLayout
