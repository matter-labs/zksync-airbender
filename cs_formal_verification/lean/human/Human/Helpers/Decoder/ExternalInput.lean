module
public import Human.Helpers.Decoder.Program
public import Human.Helpers.Core.ExternalStream
public import Human.Helpers.Context.FamilyLayout

@[expose] public section

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

end Airbender.Trace.NonDeterminism
