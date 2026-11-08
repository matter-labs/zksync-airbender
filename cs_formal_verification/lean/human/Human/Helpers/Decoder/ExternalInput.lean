import Human.Helpers.Decoder.Instruction
import Human.Helpers.Core.ExternalStream
import Human.Helpers.Context.FamilyLayout

namespace Airbender.Trace.NonDeterminism

variable {p : Nat} [Fact p.Prime]

/-- Native selector 8 identifies external reads. Word-memory rows never consume
    this stream; actual CSR correspondence is checked by decoder soundness. -/
def isRead (row : Row p) : Bool :=
  match row.family with
  | .addSub => row.assignment 18 == 1
  | .wordMemory => false

/-- The word exposed by a native external-read row's destination columns.
    `StreamPorts` binds it to an independently supplied external stream. -/
def response (row : Row p) : BitVec 32 :=
  (Arithmetic.Word.mk (row.assignment 33).val (row.assignment 34).val).toBitVec

/-- Count earlier reads by native clock, never by witness-list position. -/
def readIndex (trace : Data p) (row : Row p) : Nat :=
  ExternalStream.index Row.clock isRead trace.rows row

/-- Number of external-read rows; standard instructions and write/hint rows
    consume no words. Soundness proves the final stream position equals this count. -/
def readCount (trace : Data p) : Nat := ExternalStream.count isRead trace.rows

/-- Bind each external-read row to `stream` at its clock-ordered read index.
    The caller supplies this stream independently of the witness. This is an
    explicit external-input boundary: native constraints permit nondeterminism
    and do not authenticate which external stream was chosen. -/
def StreamPorts (trace : Data p) (stream : List (BitVec 32)) : Prop :=
  ExternalStream.Ports Row.clock isRead response trace.rows stream

/-- Responses in execution order. Native history lists use descending clocks,
    hence the reversal; writes/hints and standard instructions consume nothing. -/
def consumed (rows : List (Row p)) : List (BitVec 32) :=
  ExternalStream.consumed isRead response rows


end Airbender.Trace.NonDeterminism
