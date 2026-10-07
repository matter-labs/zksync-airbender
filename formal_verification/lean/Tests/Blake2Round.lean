import Airbender.Review.Blake2Round.Theorems

namespace Tests.Blake2Round
open Airbender

/-- A row whose next round mask does not shift is rejected by the imported
    assertions, independently of which XOR setup is supplied. -/
theorem wrongControlRejected (setup : Table (ZMod babyBearModulus) (fields 4))
    (w : Nat → ZMod babyBearModulus) :
    ¬ (Blake2Round.Control.circuitModel setup).relation ⟨123, 8⟩ ⟨0, 8⟩ w := by
  intro row
  have correct := Blake2Round.Control.babyBear_soundness setup ⟨123, 8⟩ ⟨0, 8⟩ w row
  have high := congrArg Arithmetic.Word.hi correct.2
  norm_num [Blake2Round.Control.next] at high

/-- A wrong XOR output at the actual first G query cannot satisfy the artifact.
    Table provenance and cryptographic lookup enforcement are separate obligations. -/
theorem wrongFirstXorRejected (w : Nat → ZMod babyBearModulus) :
    ¬ (FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints Blake2Round.setupTable) ∧
      w 274 = 3 ∧ w 272 = 5 ∧ w 275 = 7) := by
  intro ⟨row, left, right, wrong⟩
  have member := Verification.lookup_of_holds row
    ⟨2, by rw [Blake2Round.lookup_count]; decide⟩
  have correct := Blake2Round.Proofs.xor_lookup_raw (by decide) 0 member
    (by rfl) (by simp [Blake2Round.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment])
  have xor := correct.2.2.2
  simp [Blake2Round.importedConstraints, FlatOperation.lookups, Expression.eval,
    Verification.environment] at xor
  norm_num [left, right, wrong, ZMod.val_ofNat, babyBearModulus] at xor
  exact (by decide : (7 : Nat) ≠ 3 ^^^ 5) xor

end Tests.Blake2Round
