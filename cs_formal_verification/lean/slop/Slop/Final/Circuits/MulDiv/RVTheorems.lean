module
public import Human.Circuits.MulDiv.RVTheorems
public import Slop.MulDiv.RVTraceSoundness
public import Slop.Trace.RVPooledLawsProof
public import Slop.Final.Generic.Circuits.MulDiv.RVTheorems
public import Slop.Field.BabyBearInstance

@[expose] public section

namespace Airbender.MulDiv

/-- Every accepted MUL/MULHU/DIVU/REMU row is one `RV.step` of our spec from the row's RV pre-state. -/
private theorem rv_soundness_generic : RVSoundnessClaimGeneric := Proofs.rv_trace_soundness Trace.Proofs.rvPooledLaws

theorem rv_soundness : RVSoundnessClaim := by babybear_instance rv_soundness_generic

end Airbender.MulDiv
