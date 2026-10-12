import Airbender.Proofs.AddSub.ArtifactChecks
import Airbender.Review.Properties
import Airbender.Proofs.BabyBear
import Airbender.Proofs.Constraints

namespace Tests.InactiveRow
open Airbender

-- This is a witness for the imported local relation, not an architectural execution.
private def row (i : Nat) : ZMod babyBearModulus :=
  if i = 19 ∨ i = 21 then 4 else if i = 33 then 123 else 0

private theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row) AddSub.importedConstraints := by
  simp [AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, row]
  refine ⟨Verification.range16_contains ?_, Verification.range16_contains ?_,
    Verification.range16_contains ?_, Verification.range16_contains ?_,
    Verification.range16_contains ?_, Verification.range16_contains ?_⟩
  all_goals norm_num [Expression.eval, Verification.environment, row, Arithmetic.limbBase,
    ZMod.val_ofNat, babyBearModulus]

/-- Execute = 0 alone does not imply PC stuttering or a zero discarded result.
    All 30 retained assertions and six imported lookups admit this row. -/
example : ∃ w : Nat → ZMod babyBearModulus,
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints ∧
    w 4 = 0 ∧ w 0 = 0 ∧ w 19 = 4 ∧ w 33 = 123 :=
  ⟨row, satisfies, rfl, rfl, rfl, rfl⟩

end Tests.InactiveRow
