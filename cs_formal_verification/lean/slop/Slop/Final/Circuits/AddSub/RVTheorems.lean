import Human.Circuits.AddSub.RVTheorems
import Slop.BabyBear
import Slop.AddSub.RVTraceSoundness

namespace Airbender.AddSub

/-- Every accepted ADD/ADDI/SUB/LUI/AUIPC row is one `RV.step` of our spec from the row's RV pre-state. -/
theorem rv_soundness : RVSoundnessClaim := Proofs.rv_trace_soundness

theorem babyBear_rv_soundness : BabyBearRVSoundnessClaim := Proofs.babyBear_rv_trace_soundness

end Airbender.AddSub
