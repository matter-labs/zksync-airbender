import Airbender.Review.Circuits.MulDiv.Theorems
import Airbender.Review.Trace.Families.MulDiv.Theorems
import Airbender.Proofs.MulDiv
import Airbender.Proofs.MulDiv.Soundness
import Airbender.Proofs.MulDiv.Product
import Airbender.Proofs.MulDiv.Trace
import Airbender.Proofs.MulDiv.Decoder
import Airbender.Proofs.MulDiv.Composition
import Airbender.Proofs.BabyBear
import Airbender.Proofs.MulDiv.TraceSoundness
import Airbender.Proofs.MulDiv.RowClaims

namespace Airbender.MulDiv


theorem fetched {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {w : Nat → ZMod p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (member : (decoderTable program).Contains #[] (decoderQuery w)) : Fetched w before :=
  Proofs.fetched hp image h member


theorem clocks {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) clockConstraints)
    (inputs : Trace.ClockInputs importedConstraintsTraceColumns w) :
    Trace.ClockEffects importedConstraintsTraceColumns w :=
  Proofs.clocks (by decide) (by decide) h inputs
end Airbender.MulDiv
