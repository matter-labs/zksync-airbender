module
public import Human.Circuits.ShiftBinop.RVTheorems
public import Slop.ShiftBinop.RVTraceSoundness
public import Slop.Trace.RVPooledLawsProof

@[expose] public section

namespace Airbender.ShiftBinop

/-- Every accepted XOR/OR/AND, SLL/SRL/SRA (register or immediate) or REV8 row is one `RV.step` of our spec from
    the row's RV pre-state. -/
theorem rv_soundness : RVSoundnessClaim := Proofs.rv_trace_soundness Trace.Proofs.rvPooledLaws

theorem babyBear_rv_soundness : BabyBearRVSoundnessClaim := Proofs.babyBear_rv_trace_soundness Trace.Proofs.rvPooledLaws

end Airbender.ShiftBinop
