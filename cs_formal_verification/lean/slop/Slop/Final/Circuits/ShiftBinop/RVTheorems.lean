import Human.Circuits.ShiftBinop.RVTheorems
import Slop.BabyBear
import Slop.ShiftBinop.RVTraceSoundness

namespace Airbender.ShiftBinop

/-- Every accepted XOR/OR/AND, SLL/SRL/SRA (register or immediate) or REV8 row is one `RV.step` of our spec from
    the row's RV pre-state. -/
theorem rv_soundness : RVSoundnessClaim := Proofs.rv_trace_soundness

theorem babyBear_rv_soundness : BabyBearRVSoundnessClaim := Proofs.babyBear_rv_trace_soundness

end Airbender.ShiftBinop
