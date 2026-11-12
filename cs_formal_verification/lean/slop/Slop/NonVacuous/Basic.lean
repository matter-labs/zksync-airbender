module
public import Human.Helpers.Memory.InitialImage
public import Human.Helpers.Core.Word
public import Human.Helpers.Context.Timestamps

@[expose] public section

/-! Decidability of the small predicates the non-vacuity witnesses check on concrete data. -/

namespace Airbender

instance Arithmetic.Word.decidableBounded (word : Arithmetic.Word) : Decidable word.Bounded :=
  inferInstanceAs (Decidable (_ ∧ _))

instance Trace.Cell.decidableAligned (cell : Trace.Cell) : Decidable cell.Aligned :=
  match cell with
  | .register _ => isTrue trivial
  | .ram address => inferInstanceAs (Decidable (address.toNat % 4 = 0))

instance Trace.Timestamp.decidableBounded (time : Trace.Timestamp) : Decidable time.Bounded :=
  inferInstanceAs (Decidable (_ ∧ _))

end Airbender
