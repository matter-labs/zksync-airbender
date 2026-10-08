import Airbender.Proofs.Keccak.Controls
import Airbender.Proofs.BabyBear

namespace Airbender.Keccak

/-- First Keccak milestone: local control well-formedness and pointer alignment
    from the actual no-cache artifact, for any supplied fixed setup.
    This does not yet claim lane-operation or permutation soundness. -/
theorem local_checks {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setup)) : LocalChecks w :=
  Proofs.local_checks hp inverse holds

theorem babyBear_local_checks {setup : Table (ZMod babyBearModulus) (fields 8)}
    {w : Nat → ZMod babyBearModulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setup)) : LocalChecks w :=
  local_checks (by decide) (by decide) holds

end Airbender.Keccak
