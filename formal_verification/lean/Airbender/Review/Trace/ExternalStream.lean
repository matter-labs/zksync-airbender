import Mathlib.Data.List.Basic
import Init.Data.BitVec.Lemmas

namespace Airbender.Trace.ExternalStream

/-- Position of an external read: count selected rows with an earlier native
    clock. Physical list order does not choose the stream position. -/
def index {Row : Type} (clock : Row → Nat) (read : Row → Bool)
    (rows : List Row) (row : Row) : Nat :=
  (rows.filter fun earlier => read earlier && decide (clock earlier < clock row)).length

/-- Number of selected external reads. Other instructions consume nothing. -/
def count {Row : Type} (read : Row → Bool) (rows : List Row) : Nat :=
  (rows.filter read).length

/-- Bind selected response ports to an independently supplied stream. This
    defines the external-input boundary, not authentication of a fixed oracle.
    Native constraints, decoding and instruction execution are checked separately. -/
def Ports {Row : Type} (clock : Row → Nat) (read : Row → Bool)
    (response : Row → BitVec 32) (rows : List Row) (stream : List (BitVec 32)) : Prop :=
  ∀ row ∈ rows, read row = true → stream[index clock read rows row]? = some (response row)

/-- Responses in execution order when rows have descending native clocks,
    as supplied by the shared native-history proof. -/
def consumed {Row : Type} (read : Row → Bool) (response : Row → BitVec 32)
    (rows : List Row) : List (BitVec 32) :=
  rows.reverse.filterMap fun row => if read row then some (response row) else none

end Airbender.Trace.ExternalStream
