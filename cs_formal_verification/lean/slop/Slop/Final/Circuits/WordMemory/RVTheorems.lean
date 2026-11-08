module
public import Human.Circuits.WordMemory.RVTheorems
public import Slop.WordMemory.RVTraceSoundness
public import Slop.Trace.RVPooledLawsProof

@[expose] public section

namespace Airbender.WordMemory

/-- Every accepted LW/SW row computes its effective address and is one `RV.step` of our spec from the row's RV
    pre-state. -/
theorem rv_soundness : RVSoundnessClaim := Proofs.rv_trace_soundness Trace.Proofs.rvPooledLaws

theorem babyBear_rv_soundness : BabyBearRVSoundnessClaim := Proofs.babyBear_rv_trace_soundness Trace.Proofs.rvPooledLaws

end Airbender.WordMemory
