import Human.Circuits.JumpBranchSlt.RVTheorems
import Slop.JumpBranchSlt.RVTraceSoundness

namespace Airbender.JumpBranchSlt

/-- Every accepted SLT/SLTI/SLTU/SLTIU row is one `RV.step` of our spec from the row's RV pre-state. -/
theorem Comparison.rv_soundness : Comparison.RVSoundnessClaim := Proofs.rv_comparison_trace_soundness

theorem Comparison.babyBear_rv_soundness : Comparison.BabyBearRVSoundnessClaim :=
  Proofs.babyBear_rv_comparison_trace_soundness

/-- Every accepted branch row is one `RV.step` of our spec from the row's RV pre-state. -/
theorem Branch.rv_soundness : Branch.RVSoundnessClaim := Proofs.rv_branch_trace_soundness

theorem Branch.babyBear_rv_soundness : Branch.BabyBearRVSoundnessClaim := Proofs.babyBear_rv_branch_trace_soundness

/-- Every accepted JAL/JALR row is one `RV.step` of our spec from the row's RV pre-state. -/
theorem Jump.rv_soundness : Jump.RVSoundnessClaim := Proofs.rv_jump_trace_soundness

theorem Jump.babyBear_rv_soundness : Jump.BabyBearRVSoundnessClaim := Proofs.babyBear_rv_jump_trace_soundness

end Airbender.JumpBranchSlt
