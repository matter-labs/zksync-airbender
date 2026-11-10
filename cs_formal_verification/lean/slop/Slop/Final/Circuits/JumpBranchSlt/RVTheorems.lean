module
public import Human.Circuits.JumpBranchSlt.RVTheorems
public import Slop.JumpBranchSlt.RVTraceSoundness
public import Slop.Trace.RVPooledLawsProof
public import Slop.Final.Generic.Circuits.JumpBranchSlt.RVTheorems
public import Slop.Field.BabyBearInstance

@[expose] public section

namespace Airbender.JumpBranchSlt

/-- Every accepted SLT/SLTI/SLTU/SLTIU row is one `RV.step` of our spec from the row's RV pre-state. -/
private theorem Comparison.rv_soundness_generic : Comparison.RVSoundnessClaimGeneric := Proofs.rv_comparison_trace_soundness Trace.Proofs.rvPooledLaws

theorem Comparison.rv_soundness : Comparison.RVSoundnessClaim := by babybear_instance Comparison.rv_soundness_generic

/-- Every accepted branch row is one `RV.step` of our spec from the row's RV pre-state. -/
private theorem Branch.rv_soundness_generic : Branch.RVSoundnessClaimGeneric := Proofs.rv_branch_trace_soundness Trace.Proofs.rvPooledLaws

theorem Branch.rv_soundness : Branch.RVSoundnessClaim := by babybear_instance Branch.rv_soundness_generic

/-- Every accepted JAL/JALR row is one `RV.step` of our spec from the row's RV pre-state. -/
private theorem Jump.rv_soundness_generic : Jump.RVSoundnessClaimGeneric := Proofs.rv_jump_trace_soundness Trace.Proofs.rvPooledLaws

theorem Jump.rv_soundness : Jump.RVSoundnessClaim := by babybear_instance Jump.rv_soundness_generic

end Airbender.JumpBranchSlt
