module
public import Human.Circuits.WordMemory.RVTheorems
public import Proven.WordMemory.RVTraceSoundness
public import Proven.Trace.RVPooledLawsProof
public import Proven.Final.Generic.Circuits.WordMemory.RVTheorems
public import Proven.Field.BabyBearInstance
public import Proven.Defs.Circuits.WordMemory.RVModel
public import Proven.WordMemory.RVNonVacuous

@[expose] public section

namespace Airbender.WordMemory

/-- Every accepted LW/SW row computes its effective address and is one `RV.step` of our spec from the row's RV
    pre-state. -/
private theorem rv_soundness_generic : RVSoundnessClaimGeneric := Proofs.rv_trace_soundness Trace.Proofs.rvPooledLaws

theorem rv_soundness : RVSoundnessClaim := by
  intro trace initial cells program assumptions input output w ⟨⟨accepted, decoded, member⟩, ⟨words, state, instruction⟩⟩
  exact rv_soundness_generic (p := babyBearModulus) (by decide) (by decide) trace initial cells program assumptions input output w
    ⟨⟨accepted, decoded, member⟩, ⟨words, state, instruction⟩⟩

/-- The assumptions hold for an accepted row of this family. -/
theorem rv_satisfiable : RVSatisfiableClaim := NonVacuous.satisfiable

end Airbender.WordMemory
