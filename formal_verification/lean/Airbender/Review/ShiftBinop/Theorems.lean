import Airbender.Proofs.ShiftBinop
import Airbender.Proofs.ShiftBinop.Soundness
import Airbender.Proofs.ShiftBinop.Shifts
import Airbender.Proofs.ShiftBinop.Trace
import Airbender.Proofs.ShiftBinop.Decoder
import Airbender.Proofs.BabyBear

namespace Airbender.ShiftBinop

/-- Public bytes are decoded by original Sail and bind the native decoder query
    and both selectors. Register reads are proved separately from memory history. -/
theorem fetched {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {w : Nat → ZMod p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (member : (decoderTable program).Contains #[] (decoderQuery w)) : Fetched w before :=
  Proofs.fetched hp image h member

/-- Native four-tick advancement and all strict prior-write comparisons.
    The shared history engine derives these clock inputs from matching. -/
theorem clocks {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) clockConstraints)
    (inputs : Trace.ClockInputs importedConstraintsTraceColumns w) :
    Trace.ClockEffects importedConstraintsTraceColumns w :=
  Proofs.clocks (by decide) (by decide) h inputs

/-- XOR/OR/AND, SLL/SRL/SRA (including immediate forms), and REV8, against Sail execution and
    native register/PC effects. Lookups force all operand/result bytes. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.soundness hp inverse

theorem babyBear_soundness :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide) (by decide)

end Airbender.ShiftBinop
