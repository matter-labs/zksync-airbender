module
public import Human.Circuits.SubwordMemory.RVTheorems
public import Slop.SubwordMemory.RVTraceSoundness
public import Slop.Trace.RVPooledLawsProof
public import Slop.Final.Generic.Circuits.SubwordMemory.RVTheorems
public import Slop.Field.BabyBearInstance

@[expose] public section

namespace Airbender.SubwordMemory

/-- Every accepted LB/LBU/LH/LHU/SB/SH row computes its aligned cell address and is one `RV.step` of our spec from
    the row's RV pre-state. -/
private theorem rv_soundness_generic : RVSoundnessClaimGeneric := Proofs.rv_trace_soundness Trace.Proofs.rvPooledLaws

theorem rv_soundness : RVSoundnessClaim := by babybear_instance rv_soundness_generic

end Airbender.SubwordMemory
