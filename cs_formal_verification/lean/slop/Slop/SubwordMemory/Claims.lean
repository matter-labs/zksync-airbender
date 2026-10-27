import Slop.Final.Circuits.SubwordMemory.Theorems
import Slop.Final.Trace.Families.SubwordMemory.Theorems
import Slop.SubwordMemory.RowClaims
import Slop.SubwordMemory.TraceSoundness
import Slop.BabyBear
import Slop.SubwordMemory.Trace
import Slop.SubwordMemory.Composition

namespace Airbender.SubwordMemory
open _root_.Sail.ArchSem
theorem fetched {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (member : (decoderTable program).Contains #[] (decoderQuery w)) : Fetched w before :=
  Proofs.fetched hp image h member


theorem clocks {setup : Table (ZMod babyBearModulus) (fields 9)} {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setup))
    (inputs : Trace.ClockInputs importedConstraintsTraceColumns w) :
    Trace.ClockEffects importedConstraintsTraceColumns w :=
  Proofs.clocks (by decide) (by decide) h inputs
end Airbender.SubwordMemory
