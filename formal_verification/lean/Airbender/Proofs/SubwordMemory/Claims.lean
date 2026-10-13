import Airbender.Review.Circuits.SubwordMemory.Theorems
import Airbender.Review.Trace.Families.SubwordMemory.Theorems
import Airbender.Proofs.SubwordMemory.RowClaims
import Airbender.Proofs.SubwordMemory.TraceSoundness
import Airbender.Proofs.BabyBear
import Airbender.Proofs.SubwordMemory.Trace
import Airbender.Proofs.SubwordMemory.Composition

namespace Airbender.SubwordMemory
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]
omit [MemoryPlatform SailRV32.exception] in
theorem fetched {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (member : (decoderTable program).Contains #[] (decoderQuery w)) : Fetched w before :=
  Proofs.fetched hp image h member

omit [MemoryPlatform SailRV32.exception] in

theorem clocks {setup : Table (ZMod babyBearModulus) (fields 9)} {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setup))
    (inputs : Trace.ClockInputs importedConstraintsTraceColumns w) :
    Trace.ClockEffects importedConstraintsTraceColumns w :=
  Proofs.clocks (by decide) (by decide) h inputs
end Airbender.SubwordMemory
