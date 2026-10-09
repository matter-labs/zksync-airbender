import Airbender.Review.Trace.Pooled
import Airbender.Review.Trace.NonDeterminism

namespace Airbender.Trace.NonDeterminism.Pooled

variable {p : Nat} [Fact p.Prime]

/-- The imported ADD/SUB external-read selector. Other pooled families never
    consume input, even when the same numeric column contains one.
    Actual CSR decoding and mixed Sail execution are separate obligations. -/
def isRead (row : Row p PooledFamily) : Bool :=
  match row.family with
  | .addSub => NonDeterminism.isRead ⟨.addSub, row.assignment⟩
  | _ => false

/-- The external response in ADD/SUB's destination columns. It is used only
    for selected reads; the caller fixes the independent input stream. -/
def response (row : Row p PooledFamily) : BitVec 32 :=
  NonDeterminism.response ⟨.addSub, row.assignment⟩

/-- Count earlier external reads by native clock across the entire pool. -/
def readIndex (trace : PooledTrace p) (row : Row p PooledFamily) : Nat :=
  ExternalStream.index Row.clock isRead trace.rows row

/-- Total external-read count; all standard pooled rows consume zero words. -/
def readCount (trace : PooledTrace p) : Nat := ExternalStream.count isRead trace.rows

/-- Bind response ports to the independent stream using the shared clock-based
    interpretation. This supplies input values, not successful ISA execution. -/
def StreamPorts (trace : PooledTrace p) (stream : List (BitVec 32)) : Prop :=
  ∀ row ∈ trace.rows, isRead row = true →
    stream[readIndex trace row]? = some (response row)

/-- Responses in the chronological order derived from native matching. -/
def consumed (rows : List (Row p PooledFamily)) : List (BitVec 32) :=
  ExternalStream.consumed isRead response rows

end Airbender.Trace.NonDeterminism.Pooled
