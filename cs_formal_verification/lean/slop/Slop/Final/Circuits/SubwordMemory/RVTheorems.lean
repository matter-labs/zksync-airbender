module
public import Human.Circuits.SubwordMemory.RVTheorems
public import Slop.SubwordMemory.RVTraceSoundness
public import Slop.Trace.RVPooledLawsProof

@[expose] public section

namespace Airbender.SubwordMemory

/-- Every accepted LB/LBU/LH/LHU/SB/SH row computes its aligned cell address and is one `RV.step` of our spec from
    the row's RV pre-state. -/
theorem rv_soundness : RVSoundnessClaim := Proofs.rv_trace_soundness Trace.Proofs.rvPooledLaws

theorem babyBear_rv_soundness : BabyBearRVSoundnessClaim := Proofs.babyBear_rv_trace_soundness Trace.Proofs.rvPooledLaws

end Airbender.SubwordMemory
