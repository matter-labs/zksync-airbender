module
public import Human.Helpers.Context.Columns
public import Human.Helpers.Delegation.Columns

/-! Definitions only the proofs use, moved from `human/Human/Helpers/Delegation/Columns.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Delegation
def GroupedTimestamp.borrowValue {F : Type} [Sub F] (group : GroupedTimestamp) (w : Nat → F) : F :=
  w group.invocationHigh - w group.previous[1]
end Airbender.Delegation
