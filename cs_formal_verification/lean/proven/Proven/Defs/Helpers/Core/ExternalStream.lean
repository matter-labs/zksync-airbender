module
public import Mathlib.Data.List.Basic
public import Init.Data.BitVec.Lemmas
public import Human.Helpers.Core.ExternalStream

/-! Definitions only the proofs use, moved from `human/Human/Helpers/Core/ExternalStream.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Trace.ExternalStream
/-- Responses in execution order when rows have descending native clocks,
    as supplied by the shared native-history proof. -/
def consumed {Row : Type} (read : Row → Bool) (response : Row → BitVec 32)
    (rows : List Row) : List (BitVec 32) :=
  rows.reverse.filterMap fun row => if read row then some (response row) else none
end Airbender.Trace.ExternalStream
