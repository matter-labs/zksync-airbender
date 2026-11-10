module
public import Slop.AddSub.RVTraceSoundness
public import Slop.Trace.RVPooledLawsProof
public import Slop.Final.Generic.Circuits.AddSub.RVTheorems
public import Slop.Field.BabyBearInstance

@[expose] public section

namespace Airbender.AddSub

/-- Every accepted ADD/ADDI/SUB/LUI/AUIPC row is one `RV.step` of our spec from the row's RV pre-state. -/
private theorem rv_soundness_generic : RVSoundnessClaimGeneric := Proofs.rv_trace_soundness Trace.Proofs.rvPooledLaws

theorem rv_soundness : RVSoundnessClaim := by babybear_instance rv_soundness_generic

end Airbender.AddSub
