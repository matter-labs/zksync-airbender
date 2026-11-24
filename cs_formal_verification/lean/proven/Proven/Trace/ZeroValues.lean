module
public import Proven.Trace.HistorySplit
public import Proven.Defs.Helpers.Memory.Ports

@[expose] public section

namespace Airbender.Trace.Proofs

variable {Kind : Type} [CircuitLayout Kind]

/-- The local proof obligation for x0. Reads may only be used from ports no
    later than this write; strict prior-write clocks then make induction valid. -/
def RowZeroPreserving [Fact p.Prime] (row : Row p Kind) : Prop :=
  ∀ port ∈ row.ports,
    port.address.code row.assignment = (Cell.register 0).addressCode →
    (∀ source ∈ row.ports,
      (source.event row.columns row.assignment).1 ≤ (port.event row.columns row.assignment).1 →
      source.address.code row.assignment = (Cell.register 0).addressCode →
      (readToken row.assignment source).value = 0) →
    (writeToken row.columns row.assignment port).value = 0

def ZeroPreserving [Fact p.Prime] (trace : Data p Kind) : Prop :=
  ∀ row ∈ trace.rows, RowZeroPreserving row

end Airbender.Trace.Proofs
