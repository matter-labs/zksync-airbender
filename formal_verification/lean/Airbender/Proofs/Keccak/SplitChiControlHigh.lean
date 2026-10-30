import Airbender.Proofs.Keccak.SplitChiPortBindings

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- Both native control-register high limbs are constrained to zero. -/
theorem chi5_control_high_limbs (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then Chi5Cached.clockConstraints chi5FixedTable else Chi5.clockConstraints chi5FixedTable)) :
    w 4 = 0 ∧ w 6 = 0 := by
  cases cached
  all_goals
    have core := Verification.holds_of_sublist holds (List.sublist_append_left _ _)
    have readHigh := Verification.assertion_of_holds core ⟨1, by change 1 < 15; decide⟩
    have writeHigh := Verification.assertion_of_holds core ⟨2, by change 2 < 15; decide⟩
    change w 4 = 0 at readHigh
    change w 6 = 0 at writeHigh
    exact ⟨readHigh, writeHigh⟩

end Airbender.Keccak.Split.Native.Proofs
