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

/-- The claim, and its assumptions can be met (`Comparison.NonVacuous.satisfiable`: an SLTU row). -/
theorem Comparison.rv_soundness : Comparison.RVSoundnessClaim := by
  refine ⟨?_, Comparison.NonVacuous.satisfiable⟩
  intro trace initial cells program assumptions input output w ⟨⟨accepted, decoded, member⟩, ⟨words, state, instruction⟩⟩
  exact Comparison.rv_soundness_generic (p := babyBearModulus) (by decide) (by decide) trace initial cells program assumptions input output w
    ⟨⟨accepted, decoded, member⟩, ⟨words, state, instruction⟩⟩

/-- Every accepted branch row is one `RV.step` of our spec from the row's RV pre-state. -/
private theorem Branch.rv_soundness_generic : Branch.RVSoundnessClaimGeneric := Proofs.rv_branch_trace_soundness Trace.Proofs.rvPooledLaws

/-- The claim, and its assumptions can be met (`Branch.NonVacuous.satisfiable`: a BEQ row). -/
theorem Branch.rv_soundness : Branch.RVSoundnessClaim := by
  refine ⟨?_, Branch.NonVacuous.satisfiable⟩
  intro trace initial cells program assumptions input output w ⟨⟨accepted, decoded, member⟩, ⟨words, state, instruction⟩⟩
  exact Branch.rv_soundness_generic (p := babyBearModulus) (by decide) (by decide) trace initial cells program assumptions input output w
    ⟨⟨accepted, decoded, member⟩, ⟨words, state, instruction⟩⟩

/-- Every accepted JAL/JALR row is one `RV.step` of our spec from the row's RV pre-state. -/
private theorem Jump.rv_soundness_generic : Jump.RVSoundnessClaimGeneric := Proofs.rv_jump_trace_soundness Trace.Proofs.rvPooledLaws

/-- The claim, and its assumptions can be met (`Jump.NonVacuous.satisfiable`: a JALR row). -/
theorem Jump.rv_soundness : Jump.RVSoundnessClaim := by
  refine ⟨?_, Jump.NonVacuous.satisfiable⟩
  intro trace initial cells program assumptions input output w ⟨⟨accepted, decoded, member⟩, ⟨words, state, instruction⟩⟩
  exact Jump.rv_soundness_generic (p := babyBearModulus) (by decide) (by decide) trace initial cells program assumptions input output w
    ⟨⟨accepted, decoded, member⟩, ⟨words, state, instruction⟩⟩

end Airbender.JumpBranchSlt
