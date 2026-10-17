import Tests.AddSub

namespace Tests.Timestamps
open Airbender

private def nativeRow := Tests.AddSub.row 1 123 123 0 246 0 0 0 0 0 4 0 0 0

theorem wrong_borrow_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat
      (Verification.environment (fun i => if i = 46 then 0 else nativeRow i))
      Airbender.AddSub.importedConstraints := by
  intro h
  have bad := Verification.timestamp19_bound (Verification.lookup_of_holds h
    ⟨6, by rw [Airbender.AddSub.Proofs.lookup_count]; decide⟩)
  revert bad
  decide

theorem wrong_decoder_mask_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat
      (Verification.environment (fun i => if i = 12 then 2 else nativeRow i))
      Airbender.AddSub.importedConstraints := by
  intro h
  have bad := Verification.assertion_of_holds h
    ⟨34, by rw [Airbender.AddSub.Proofs.constraint_count]; decide⟩
  revert bad
  decide

end Tests.Timestamps
