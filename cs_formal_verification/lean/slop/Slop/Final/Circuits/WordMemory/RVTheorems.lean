import Human.Circuits.WordMemory.RVTheorems
import Slop.BabyBear
import Slop.WordMemory.RVTraceSoundness

namespace Airbender.WordMemory

/-- Every accepted LW/SW row computes its effective address and is one `RV.step` of our spec from the row's RV
    pre-state. -/
theorem rv_soundness : RVSoundnessClaim := Proofs.rv_trace_soundness

theorem babyBear_rv_soundness : BabyBearRVSoundnessClaim := Proofs.babyBear_rv_trace_soundness

end Airbender.WordMemory
