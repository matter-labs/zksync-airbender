import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Circuits.JumpBranchSlt.Theorems
import Airbender.Review.Trace.Families.JumpBranchSlt.Theorems
import Airbender.Proofs.JumpBranchSlt.RowClaims
import Airbender.Proofs.JumpBranchSlt.TraceSoundness
import Airbender.Proofs.JumpBranchSlt.BranchSoundness
import Airbender.Proofs.JumpBranchSlt.JumpSoundness
import Airbender.Proofs.JumpBranchSlt.PCState
import Airbender.Proofs.JumpBranchSlt.Timestamp
import Airbender.Proofs.JumpBranchSlt.Trace
import Airbender.Proofs.JumpBranchSlt.Decoder
import Airbender.Proofs.JumpBranchSlt.Composition
import Airbender.Proofs.BabyBear

namespace Airbender.JumpBranchSlt


theorem final_pc_bounds {p n : Nat} [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
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


theorem fetched {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p Arithmetic.limbBase)
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
