import Slop.MulDiv
import Slop.MulDiv.Soundness
import Slop.MulDiv.Product
import Slop.MulDiv.Trace
import Human.Circuits.JumpBranchSlt.Jump
import Human.Helpers.Core.BabyBearPrime
import Slop.AddSub.Selectors
import Slop.JumpBranchSlt.Branch
import Slop.JumpBranchSlt.Jump
import Slop.JumpBranchSlt.PortReads
import Slop.MulDiv.PortReads
import Slop.MulDiv.Values
import Slop.ShiftBinop.PortReads
import Slop.ShiftBinop.Ports
import Slop.SubwordMemory.Values
import Slop.Trace.CompositionCore
import Slop.Trace.Family.Values
import Slop.Trace.Pooled
import Slop.Trace.RowContext

namespace Airbender.MulDiv


theorem clocks {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) clockConstraints)
    (inputs : Trace.ClockInputs importedConstraintsTraceColumns w) :
    Trace.ClockEffects importedConstraintsTraceColumns w :=
  Proofs.clocks (by decide) (by decide) h inputs
end Airbender.MulDiv
