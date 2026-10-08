import Airbender.Proofs.Trace.Rows
import Airbender.Proofs.BabyBear

namespace Airbender.Trace

/-- Native clock queries and equations enforce the shared clock effects.
    Source clock bounds remain a state/memory-history obligation. -/
theorem addSub_clocks {w : Nat → ZMod babyBearModulus}
    (row : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.clockConstraints)
    (inputs : ClockInputs AddSub.importedConstraintsTraceColumns w) :
    ClockEffects AddSub.importedConstraintsTraceColumns w :=
  Proofs.addSub_clock (by decide) (by decide) row inputs

theorem wordMemory_clocks (rom : Table (ZMod babyBearModulus) (fields 9))
    {w : Nat → ZMod babyBearModulus}
    (row : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (WordMemory.clockConstraints rom))
    (inputs : ClockInputs WordMemory.importedConstraintsTraceColumns w) :
    ClockEffects WordMemory.importedConstraintsTraceColumns w :=
  Proofs.wordMemory_clock (by decide) (by decide) rom row inputs

end Airbender.Trace
