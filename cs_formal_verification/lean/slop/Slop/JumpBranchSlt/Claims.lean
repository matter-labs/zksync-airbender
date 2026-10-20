import Slop.Final.Circuits.JumpBranchSlt.Theorems
import Slop.Final.Trace.Families.JumpBranchSlt.Theorems
import Slop.JumpBranchSlt.RowClaims
import Slop.JumpBranchSlt.TraceSoundness
import Slop.JumpBranchSlt.BranchSoundness
import Slop.JumpBranchSlt.JumpSoundness
import Slop.JumpBranchSlt.PCState
import Slop.JumpBranchSlt.Timestamp
import Slop.JumpBranchSlt.Trace
import Slop.JumpBranchSlt.Decoder
import Slop.JumpBranchSlt.Composition
import Slop.BabyBear

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


theorem fetched {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {w : Nat → ZMod p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (member : (decoderTable program).Contains #[] (decoderQuery w)) : Fetched w before :=
  Proofs.fetched hp image h member

namespace Comparison

end Comparison

namespace Branch

end Branch

namespace Jump

end Jump

end Airbender.JumpBranchSlt
