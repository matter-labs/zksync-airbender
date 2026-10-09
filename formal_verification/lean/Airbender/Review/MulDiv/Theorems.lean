import Airbender.Proofs.MulDiv
import Airbender.Proofs.MulDiv.Soundness
import Airbender.Proofs.MulDiv.Product
import Airbender.Proofs.MulDiv.Trace
import Airbender.Proofs.BabyBear

namespace Airbender.MulDiv

/-- Imported clock equations and eight native queries enforce four-tick
    advancement and strict prior-write order, including aliased registers. -/
theorem clocks {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) clockConstraints)
    (inputs : Trace.ClockInputs importedConstraintsTraceColumns w) :
    Trace.ClockEffects importedConstraintsTraceColumns w :=
  Proofs.clocks (by decide) (by decide) h inputs
/-- MUL/MULHU/DIVU/REMU, including zero divisor, proved against original Sail execution plus
    native register/PC effects. Decoder/state interfaces remain explicit. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.soundness hp inverse

theorem babyBear_soundness :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide) (by decide)

end Airbender.MulDiv
