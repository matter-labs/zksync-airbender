module
public import Human.Circuits.MulDiv.RVTheorems
public import Slop.MulDiv.RVTraceSoundness
public import Slop.Trace.RVPooledLawsProof

@[expose] public section

namespace Airbender.MulDiv

/-- Every accepted MUL/MULHU/DIVU/REMU row is one `RV.step` of our spec from the row's RV pre-state. -/
theorem rv_soundness : RVSoundnessClaim := Proofs.rv_trace_soundness Trace.Proofs.rvPooledLaws

theorem babyBear_rv_soundness : BabyBearRVSoundnessClaim := Proofs.babyBear_rv_trace_soundness Trace.Proofs.rvPooledLaws

end Airbender.MulDiv
