module
public import Slop.JumpBranchSlt.PCState
public import Slop.JumpBranchSlt.Timestamp
public import Slop.JumpBranchSlt.Trace
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Helpers.Core.BabyBearPrime
public import Slop.AddSub.Selectors
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump
public import Slop.JumpBranchSlt.PortReads
public import Slop.MulDiv.PortReads
public import Slop.MulDiv.Soundness
public import Slop.MulDiv.Values
public import Slop.ShiftBinop.PortReads
public import Slop.ShiftBinop.Ports
public import Slop.SubwordMemory.Values
public import Slop.Trace.CompositionCore
public import Slop.Trace.Family.Values
public import Slop.Trace.Pooled
public import Slop.Trace.RowContext

@[expose] public section

namespace Airbender.JumpBranchSlt


theorem final_pc_bounds {p n : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {context : PCState.Context p n} {w : Nat → ZMod p}
    (global : PCState.Interface context)
    (outgoing : PCState.Outgoing context (w Variables.finalPCLo, w Variables.finalPCHi))
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w Variables.finalPCLo).val < Arithmetic.limbBase ∧
      (w Variables.finalPCHi).val < Arithmetic.limbBase :=
  Proofs.final_pc_bounds hp global outgoing h


theorem clocks {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) clockConstraints)
    (inputs : Trace.ClockInputs importedConstraintsTraceColumns w) :
    Trace.ClockEffects importedConstraintsTraceColumns w :=
  Proofs.clocks (by decide) (by decide) h inputs


namespace Comparison

end Comparison

namespace Branch

end Branch

namespace Jump

end Jump

end Airbender.JumpBranchSlt
