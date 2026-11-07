import Airbender.Proofs.Keccak.SplitThetaControlColumns

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- Both actual native control-register high limbs are zero. -/
theorem theta_control_high_limbs (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) :
    w 4 = 0 ∧ w 6 = 0 := by
  cases cached
  all_goals
    have core := Verification.holds_of_sublist holds (List.sublist_append_left _ _)
    have readHigh := Verification.assertion_of_holds core ⟨1, by change 1 < 35; decide⟩
    have writeHigh := Verification.assertion_of_holds core ⟨2, by change 2 < 35; decide⟩
    change w 4 = 0 at readHigh
    change w 6 = 0 at writeHigh
    exact ⟨readHigh, writeHigh⟩

end Airbender.Keccak.Split.Native.Proofs
