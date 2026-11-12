module
public import Human.Circuits.JumpBranchSlt.RVTheorems
public import Proven.JumpBranchSlt.RVTraceSoundness
public import Proven.Trace.RVPooledLawsProof
public import Proven.Final.Generic.Circuits.JumpBranchSlt.RVTheorems
public import Proven.Field.BabyBearInstance
public import Proven.Defs.Circuits.JumpBranchSlt.RVModel
public import Proven.JumpBranchSlt.RVNonVacuous

@[expose] public section

namespace Airbender.JumpBranchSlt

/-- Every accepted SLT/SLTI/SLTU/SLTIU row is one `RV.step` of our spec from the row's RV pre-state. -/
private theorem Comparison.rv_soundness_generic : Comparison.RVSoundnessClaimGeneric := Proofs.rv_comparison_trace_soundness Trace.Proofs.rvPooledLaws

theorem Comparison.rv_soundness : Comparison.RVSoundnessClaim := by
  intro trace initial cells program assumptions input output w ⟨⟨accepted, decoded, member⟩, ⟨words, state, instruction⟩⟩
  exact Comparison.rv_soundness_generic (p := babyBearModulus) (by decide) (by decide) trace initial cells program assumptions input output w
    ⟨⟨accepted, decoded, member⟩, ⟨words, state, instruction⟩⟩

/-- Every accepted branch row is one `RV.step` of our spec from the row's RV pre-state. -/
private theorem Branch.rv_soundness_generic : Branch.RVSoundnessClaimGeneric := Proofs.rv_branch_trace_soundness Trace.Proofs.rvPooledLaws

theorem Branch.rv_soundness : Branch.RVSoundnessClaim := by
  intro trace initial cells program assumptions input output w ⟨⟨accepted, decoded, member⟩, ⟨words, state, instruction⟩⟩
  exact Branch.rv_soundness_generic (p := babyBearModulus) (by decide) (by decide) trace initial cells program assumptions input output w
    ⟨⟨accepted, decoded, member⟩, ⟨words, state, instruction⟩⟩

/-- Every accepted JAL/JALR row is one `RV.step` of our spec from the row's RV pre-state. -/
private theorem Jump.rv_soundness_generic : Jump.RVSoundnessClaimGeneric := Proofs.rv_jump_trace_soundness Trace.Proofs.rvPooledLaws

theorem Jump.rv_soundness : Jump.RVSoundnessClaim := by
  intro trace initial cells program assumptions input output w ⟨⟨accepted, decoded, member⟩, ⟨words, state, instruction⟩⟩
  exact Jump.rv_soundness_generic (p := babyBearModulus) (by decide) (by decide) trace initial cells program assumptions input output w
    ⟨⟨accepted, decoded, member⟩, ⟨words, state, instruction⟩⟩

/-- The assumptions hold for an accepted row of this family. -/
theorem Comparison.rv_satisfiable : Comparison.RVSatisfiableClaim := Comparison.NonVacuous.satisfiable

/-- The assumptions hold for an accepted row of this family. -/
theorem Branch.rv_satisfiable : Branch.RVSatisfiableClaim := Branch.NonVacuous.satisfiable

/-- The assumptions hold for an accepted row of this family. -/
theorem Jump.rv_satisfiable : Jump.RVSatisfiableClaim := Jump.NonVacuous.satisfiable

end Airbender.JumpBranchSlt
