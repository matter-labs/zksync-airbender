import Airbender.Review.Delegation.Columns
import Airbender.Proofs.Trace.Timestamps
import Airbender.Proofs.Constraints
import Airbender.Review.Properties

namespace Airbender.Delegation.Proofs
set_option warningAsError true

structure ClockFacts {p : Nat} (columns : ClockColumns) (w : Nat → ZMod p) : Prop where
  invocation : (Trace.decodeTimestamp w columns.invocation).Bounded
  offsets : ∀ port ∈ columns.ports, port.offset < 4
  comparisons : ∀ port ∈ columns.ports,
    w port.borrow * (w port.borrow - 1) = 0 ∧
    ((w port.previous[0] - w columns.invocation[0] - port.offset +
      Trace.timestampBase * w port.borrow) : ZMod p).val < Trace.timestampBase ∧
    ((w port.previous[1] + Trace.timestampBase - w port.borrow -
      w columns.invocation[1]) : ZMod p).val < Trace.timestampBase

end Airbender.Delegation.Proofs
