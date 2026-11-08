import Slop.SubwordMemory.Trace
import Human.Circuits.SubwordMemory.Output
import Human.Helpers.Core.BabyBearPrime
import Slop.AddSub.Selectors
import Slop.JumpBranchSlt.Branch
import Slop.JumpBranchSlt.Jump
import Slop.MulDiv.Values
import Slop.ShiftBinop.Ports
import Slop.SubwordMemory.PortReads
import Slop.Trace.Family.Values
import Slop.Trace.Pooled
import Slop.Trace.RowContext
import Slop.Trace.CompositionCore

namespace Airbender.SubwordMemory


theorem clocks {setup : Table (ZMod babyBearModulus) (fields 9)} {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setup))
    (inputs : Trace.ClockInputs importedConstraintsTraceColumns w) :
    Trace.ClockEffects importedConstraintsTraceColumns w :=
  Proofs.clocks (by decide) (by decide) h inputs
end Airbender.SubwordMemory
