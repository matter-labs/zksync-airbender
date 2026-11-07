import Airbender.Proofs.Keccak.SplitParityControlColumns
import Airbender.Proofs.Keccak.SplitParityIotaConstraints

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- Exact native control tokens carry the original schedule word, without truncation. -/
theorem parity_control_port_codes (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable else ColumnParity.clockConstraints columnParityFixedTable)) :
    (parityControlPort cached).readCode w = Nat.pair (parityQueryRow cached w 1)[0].val 0 ∧
      (parityControlPort cached).writeCode w = Nat.pair (parityQueryRow cached w 1)[2].val 0 := by
  have high := parity_control_high_limbs cached w holds
  constructor
  · have code := congrArg (fun values : Vector (ZMod babyBearModulus) 2 =>
        Nat.pair values[0].val values[1].val) (parity_control_port_columns cached false w)
    change (parityControlPort cached).readCode w =
      Nat.pair (parityQueryRow cached w 1)[0].val (w 4).val at code
    simpa only [high.1, ZMod.val_zero] using code
  · have code := congrArg (fun values : Vector (ZMod babyBearModulus) 2 =>
        Nat.pair values[0].val values[1].val) (parity_control_port_columns cached true w)
    change (parityControlPort cached).writeCode w =
      Nat.pair (parityQueryRow cached w 1)[2].val (w 6).val at code
    simpa only [high.2, ZMod.val_zero] using code

end Airbender.Keccak.Split.Native.Proofs
