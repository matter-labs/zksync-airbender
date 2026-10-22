import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Trace.PooledNonDeterminism
import Airbender.Proofs.Trace.ExternalStream
import Airbender.Proofs.Trace.Pooled

namespace Airbender.Trace.NonDeterminism.Pooled.Proofs

variable {p : Nat} [Fact p.Prime]

theorem read_index_permutation {first second : PooledTrace p}
    (permutation : first.rows.Perm second.rows) (row : Row p PooledFamily) :
    readIndex first row = readIndex second row :=
  (permutation.filter _).length_eq

theorem consumed_length (rows : List (Row p PooledFamily)) :
    (consumed rows).length = (rows.filter isRead).length :=
  ExternalStream.Proofs.consumed_length isRead response rows

theorem native_consumption (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p) {trace : PooledTrace p}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {stream : List (BitVec 32)} (ports : StreamPorts trace stream) :
    ∃ rows, rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      ∃ rest, stream = consumed rows ++ rest :=
  ExternalStream.Proofs.native_consumption isRead response hp inverse accepted clocks ports

end Airbender.Trace.NonDeterminism.Pooled.Proofs
