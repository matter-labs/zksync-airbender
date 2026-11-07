import Airbender.Proofs.Keccak.SplitChiControlColumns
import Airbender.Proofs.Keccak.SplitChiControlHigh

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- Exact native control tokens carry the original schedule word, without truncation. -/
theorem chi5_control_port_codes (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then Chi5Cached.clockConstraints chi5FixedTable else Chi5.clockConstraints chi5FixedTable)) :
    (chi5ControlPort cached).readCode w = Nat.pair (chi5ControllerRow cached w)[0].val 0 ∧
      (chi5ControlPort cached).writeCode w = Nat.pair (chi5ControllerRow cached w)[2].val 0 := by
  have high := chi5_control_high_limbs cached w holds
  constructor
  · have code := congrArg (fun values : Vector (ZMod babyBearModulus) 2 =>
        Nat.pair values[0].val values[1].val) (chi5_control_port_columns cached false w)
    change (chi5ControlPort cached).readCode w =
      Nat.pair (chi5ControllerRow cached w)[0].val (w 4).val at code
    simpa only [high.1, ZMod.val_zero] using code
  · have code := congrArg (fun values : Vector (ZMod babyBearModulus) 2 =>
        Nat.pair values[0].val values[1].val) (chi5_control_port_columns cached true w)
    change (chi5ControlPort cached).writeCode w =
      Nat.pair (chi5ControllerRow cached w)[2].val (w 6).val at code
    simpa only [high.2, ZMod.val_zero] using code

end Airbender.Keccak.Split.Native.Proofs
