import Tests.MulDivInitializedFixture
import Airbender.Proofs.MulDiv.PC

namespace Tests.MulDivPC
open Airbender Arithmetic MulDiv Verification

/-- Actual v2 PC carry gates and inverse witnesses at the aligned RV32 boundary. -/
def wrapAssignment (i : Nat) : ZMod mersenne31Modulus :=
  if i = 0 then 65532 else if i = 1 then 65535 else
  if i = 13 ∨ i = 14 ∨ i = 62 ∨ i = 64 then 0 else
  if i = 63 ∨ i = 65 then 1 else
  Tests.MulDivInitializedFixture.assignment .mul false false i

/-- Every native equation and lookup accepts the wrapped PC witness. This is
    a checked full imported row, not a relaxed PC-only constraint fragment. -/
theorem native_wrap_constraints : FlatOperation.ConstraintsHoldFlat
    (environment wrapAssignment) MulDiv.importedConstraints := by
  simp [MulDiv.importedConstraints,FlatOperation.ConstraintsHoldFlat,Expression.eval,
    environment,wrapAssignment,Tests.MulDivInitializedFixture.assignment,
    Tests.MulDivWitness.assignment,Tests.MulDivWitness.witnessValues]
  all_goals repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) |
    (apply Tests.MulDivWitness.byte_query_contains <;> decide) | decide

/-- The same theorem used for original local retirement retains native rollover. -/
theorem native_wrap : (Word.mk (wrapAssignment 13).val (wrapAssignment 14).val).Bounded ∧
    (Word.mk (wrapAssignment 13).val (wrapAssignment 14).val).toBitVec =
      (Word.mk (wrapAssignment 0).val (wrapAssignment 1).val).toBitVec + 4 :=
  MulDiv.Proofs.native_pc_successor (by decide) native_wrap_constraints
    ⟨(ZMod.natCast_zmod_val _).symm,(ZMod.natCast_zmod_val _).symm,rfl,rfl⟩
    (by constructor <;> decide +kernel) (by decide +kernel)

theorem wrapped_value : (Word.mk (wrapAssignment 0).val (wrapAssignment 1).val).toBitVec = 0xfffffffc ∧
    (Word.mk (wrapAssignment 13).val (wrapAssignment 14).val).toBitVec = 0 := by
  decide +kernel

end Tests.MulDivPC
