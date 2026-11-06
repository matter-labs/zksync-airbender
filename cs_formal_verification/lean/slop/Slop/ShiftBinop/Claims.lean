import Slop.Final.Circuits.ShiftBinop.Theorems
import Slop.Final.Trace.Families.ShiftBinop.Theorems
import Slop.ShiftBinop
import Slop.ShiftBinop.RowClaims
import Slop.ShiftBinop.TraceSoundness
import Slop.ShiftBinop.Shifts
import Slop.ShiftBinop.Trace
import Slop.ShiftBinop.Decoder
import Slop.ShiftBinop.Composition
import Slop.BabyBear

namespace Airbender.ShiftBinop


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

end Airbender.ShiftBinop
