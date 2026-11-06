import Slop.Final.Circuits.MulDiv.Theorems
import Slop.Final.Trace.Families.MulDiv.Theorems
import Slop.MulDiv
import Slop.MulDiv.Soundness
import Slop.MulDiv.Product
import Slop.MulDiv.Trace
import Slop.MulDiv.Decoder
import Slop.MulDiv.Composition
import Slop.BabyBear
import Slop.MulDiv.TraceSoundness
import Slop.MulDiv.RowClaims

namespace Airbender.MulDiv


theorem fetched {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {w : Nat → ZMod p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program)
    (configuration : Reference.RiscV.Sail.Configured before)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (member : (decoderTable program).Contains #[] (decoderQuery w)) : Fetched w before :=
  Proofs.fetched hp image (by find_configured) h member


theorem clocks {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) clockConstraints)
    (inputs : Trace.ClockInputs importedConstraintsTraceColumns w) :
    Trace.ClockEffects importedConstraintsTraceColumns w :=
  Proofs.clocks (by decide) (by decide) h inputs
end Airbender.MulDiv
