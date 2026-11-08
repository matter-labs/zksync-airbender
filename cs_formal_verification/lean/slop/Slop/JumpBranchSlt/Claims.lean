import Slop.JumpBranchSlt.PCState
import Slop.JumpBranchSlt.Timestamp
import Slop.JumpBranchSlt.Trace
import Human.Circuits.JumpBranchSlt.Jump
import Human.Helpers.Core.BabyBearPrime
import Slop.AddSub.Selectors
import Slop.JumpBranchSlt.Branch
import Slop.JumpBranchSlt.Jump
import Slop.JumpBranchSlt.PortReads
import Slop.MulDiv.PortReads
import Slop.MulDiv.Soundness
import Slop.MulDiv.Values
import Slop.ShiftBinop.PortReads
import Slop.ShiftBinop.Ports
import Slop.SubwordMemory.Values
import Slop.Trace.CompositionCore
import Slop.Trace.Family.Values
import Slop.Trace.Pooled
import Slop.Trace.RowContext

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
