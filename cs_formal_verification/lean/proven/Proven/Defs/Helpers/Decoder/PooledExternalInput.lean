module
public import Human.Helpers.Decoder.PooledProgram
public import Human.Helpers.Decoder.ExternalInput
public import Human.Helpers.Decoder.PooledExternalInput
public import Proven.Defs.Helpers.Decoder.ExternalInput

/-! Definitions only the proofs use, moved from `human/Human/Helpers/Decoder/PooledExternalInput.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Trace.NonDeterminism.Pooled
variable {p : Nat} [Fact p.Prime]
/-- Count earlier external reads by native clock across the entire pool. -/
def readIndex (trace : PooledTrace p) (row : Row p PooledFamily) : Nat :=
  ExternalStream.index Row.clock isRead trace.rows row
/-- Responses in the chronological order derived from native matching. -/
def consumed (rows : List (Row p PooledFamily)) : List (BitVec 32) :=
  ExternalStream.consumed isRead response rows
end Airbender.Trace.NonDeterminism.Pooled
