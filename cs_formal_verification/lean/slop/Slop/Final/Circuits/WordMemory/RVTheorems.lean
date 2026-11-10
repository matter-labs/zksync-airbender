module
public import Human.Circuits.WordMemory.RVTheorems
public import Slop.WordMemory.RVTraceSoundness
public import Slop.Trace.RVPooledLawsProof
public import Slop.Final.Generic.Circuits.WordMemory.RVTheorems
public import Slop.Field.BabyBearInstance
public import Slop.Defs.Circuits.WordMemory.RVModel

@[expose] public section

namespace Airbender.WordMemory

/-- Every accepted LW/SW row computes its effective address and is one `RV.step` of our spec from the row's RV
    pre-state. -/
private theorem rv_soundness_generic : RVSoundnessClaimGeneric := Proofs.rv_trace_soundness Trace.Proofs.rvPooledLaws

theorem rv_soundness : RVSoundnessClaim := by
  intro trace initial cells program assumptions input output w ⟨⟨accepted, decoded, member⟩, ⟨words, state, instruction⟩⟩
  exact rv_soundness_generic (p := babyBearModulus) (by decide) (by decide) trace initial cells program assumptions input output w
    ⟨⟨accepted, decoded, member⟩, ⟨words, state, instruction⟩⟩

end Airbender.WordMemory
