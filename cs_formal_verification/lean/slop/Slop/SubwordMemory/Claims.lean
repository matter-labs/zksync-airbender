module
public import Slop.SubwordMemory.Trace
public import Human.Circuits.SubwordMemory.Output
public import Human.Helpers.Core.BabyBearPrime
public import Slop.AddSub.Selectors
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump
public import Slop.MulDiv.Values
public import Slop.ShiftBinop.Ports
public import Slop.SubwordMemory.PortReads
public import Slop.Trace.Family.Values
public import Slop.Trace.Pooled
public import Slop.Trace.RowContext
public import Slop.Trace.CompositionCore

@[expose] public section

namespace Airbender.SubwordMemory


theorem clocks {setup : Table (ZMod babyBearModulus) (fields 9)} {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setup))
    (inputs : Trace.ClockInputs importedConstraintsTraceColumns w) :
    Trace.ClockEffects importedConstraintsTraceColumns w :=
  Proofs.clocks (by decide) (by decide) h inputs
end Airbender.SubwordMemory
