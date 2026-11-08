module
public import Human.Helpers.Delegation.Columns
public import Slop.Trace.Timestamps
public import Slop.Constraints
public import Human.Helpers.Properties

@[expose] public section

namespace Airbender.Delegation.Proofs
set_option warningAsError true

structure ClockFacts {p : Nat} (columns : ClockColumns) (w : Nat → ZMod p) : Prop where
  -- No invocation bound: the new circuits range-check only (lo - execute)/4 and
  -- no invocation high limb. The per-row assumptions in BoundaryInputs carry it.
  offsets : ∀ port ∈ columns.ports, port.offset < 4
  comparisons : ∀ port ∈ columns.ports,
    w port.borrow * (w port.borrow - 1) = 0 ∧
    ((w port.previous[0] - w columns.invocation[0] - port.offset +
      Trace.timestampBase * w port.borrow) : ZMod p).val < Trace.timestampBase ∧
    ((w port.previous[1] + Trace.timestampBase - w port.borrow -
      w columns.invocation[1]) : ZMod p).val < Trace.timestampBase

end Airbender.Delegation.Proofs
