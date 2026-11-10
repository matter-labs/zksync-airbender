module
public import Human.Circuits.ShiftBinop.RVTheorems
public import Slop.ShiftBinop.RVTraceSoundness
public import Slop.ShiftBinop.RVNonVacuous
public import Slop.Trace.RVPooledLawsProof
public import Slop.Final.Generic.Circuits.ShiftBinop.RVTheorems
public import Slop.Field.BabyBearInstance
public import Slop.Defs.Circuits.ShiftBinop.RVModel

@[expose] public section

namespace Airbender.ShiftBinop

/-- Every accepted XOR/OR/AND, SLL/SRL/SRA (register or immediate) or REV8 row is one `RV.step` of our spec from
    the row's RV pre-state. -/
private theorem rv_soundness_generic : RVSoundnessClaimGeneric := Proofs.rv_trace_soundness Trace.Proofs.rvPooledLaws

theorem rv_soundness : RVSoundnessClaim := by
  refine ⟨?_, Witness.satisfiable⟩
  intro trace initial cells program assumptions input output w ⟨⟨accepted, decoded, member⟩, ⟨words, state, instruction⟩⟩
  exact rv_soundness_generic (p := babyBearModulus) (by decide) (by decide) trace initial cells program assumptions input output w
    ⟨⟨accepted, decoded, member⟩, ⟨words, state, instruction⟩⟩

end Airbender.ShiftBinop
