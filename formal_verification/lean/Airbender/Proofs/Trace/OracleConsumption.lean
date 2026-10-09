import Airbender.Proofs.Trace.NonDeterminism
import Airbender.Proofs.Trace.ExternalStream

namespace Airbender.Trace.NonDeterminism.Proofs
open Trace.Proofs

variable {p : Nat} [Fact p.Prime]

/-- A physical reordering cannot change the external-input position. -/
theorem read_index_permutation {first second : Data p}
    (permutation : first.rows.Perm second.rows) (row : Row p) :
    readIndex first row = readIndex second row :=
  (permutation.filter _).length_eq

theorem consumed_length (rows : List (Row p)) :
    (consumed rows).length = (rows.filter isRead).length :=
  ExternalStream.Proofs.consumed_length isRead response rows

/-- Sorted native rows consume exactly a prefix of an independent stream.
    No instruction execution or fixed-stream authentication is claimed here. -/
theorem ordered_consumption {rows : List (Row p)} {stream : List (BitVec 32)}
    (ordered : rows.Pairwise (fun a b => rowClock b < rowClock a))
    (ports : ∀ row ∈ rows, isRead row = true →
      stream[(rows.filter fun earlier => isRead earlier &&
        decide (rowClock earlier < rowClock row)).length]? = some (response row)) :
    ∃ rest, stream = consumed rows ++ rest :=
  ExternalStream.Proofs.ordered_consumption isRead response rowClock ordered ports

/-- Imported clocks and logical matching derive the order. The stream boundary
    is then a chronological prefix, regardless of physical row storage order. -/
theorem native_consumption (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {stream : List (BitVec 32)} (ports : StreamPorts trace stream) :
    ∃ rows, rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => rowClock b < rowClock a) ∧
      ∃ rest, stream = consumed rows ++ rest :=
  ExternalStream.Proofs.native_consumption isRead response hp inverse accepted boundary ports

end Airbender.Trace.NonDeterminism.Proofs
