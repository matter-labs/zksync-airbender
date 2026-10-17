import Tests.AddSub

namespace Tests.CircuitRows
open Airbender

theorem addi_carry_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment
      (Tests.AddSub.row 2 65535 0 1 0 1 1 0 0 0 4 0 0 0))
      Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

theorem sub_borrow_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment
      (Tests.AddSub.row 4 0 1 0 65535 65535 1 1 0 0 4 0 0 0))
      Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

theorem lui_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment
      (Tests.AddSub.row 8 0 0 4096 4096 0 0 0 0 0 4 0 0 0))
      Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

theorem auipc_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment
      (Tests.AddSub.row 16 0 0 4096 4096 0 0 0 0 0 4 0 0 0))
      Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

private def zeroRow (i : Nat) : ZMod mersenne31Modulus :=
  if i = 7 then 0 else if i = 8 then 1 else Tests.AddSub.row 1 0 0 0 0 0 0 0 0 0 4 0 0 0 i

theorem discarded_write_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment zeroRow)
      Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, zeroRow, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

end Tests.CircuitRows
