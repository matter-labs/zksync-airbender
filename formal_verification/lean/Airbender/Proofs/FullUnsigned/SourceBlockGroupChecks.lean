import Airbender.Proofs.FullUnsigned.SourceBlockScaling

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

/-- Consecutive finite checks preserve the absolute row coordinate. -/
theorem checkBlockRows_append (expected : Nat → Nat) (front back : List Block) (first : Nat) :
    checkBlockRows expected first (front ++ back) =
      (checkBlockRows expected first front &&
        checkBlockRows expected (first + (front.map Block.length).sum) back) := by
  induction front generalizing first with
  | nil => simp only [List.nil_append, checkBlockRows, List.map_nil, List.sum_nil,
      Nat.add_zero, Bool.true_and]
  | cons block rest ih =>
    simp only [List.cons_append, checkBlockRows, ih, List.map_cons, List.sum_cons,
      Nat.add_assoc, Bool.and_assoc]

end Airbender.Setup.Proofs
