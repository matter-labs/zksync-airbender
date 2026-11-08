module
public import Slop.MulDiv
public import Slop.MulDiv.Soundness
public import Slop.MulDiv.Product
public import Slop.MulDiv.Trace
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Helpers.Core.BabyBearPrime
public import Slop.AddSub.Selectors
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump
public import Slop.JumpBranchSlt.PortReads
public import Slop.MulDiv.PortReads
public import Slop.MulDiv.Values
public import Slop.ShiftBinop.PortReads
public import Slop.ShiftBinop.Ports
public import Slop.SubwordMemory.Values
public import Slop.Trace.CompositionCore
public import Slop.Trace.Family.Values
public import Slop.Trace.Pooled
public import Slop.Trace.RowContext

@[expose] public section

namespace Airbender.MulDiv


theorem clocks {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) clockConstraints)
    (inputs : Trace.ClockInputs importedConstraintsTraceColumns w) :
    Trace.ClockEffects importedConstraintsTraceColumns w :=
  Proofs.clocks (by decide) (by decide) h inputs
end Airbender.MulDiv
