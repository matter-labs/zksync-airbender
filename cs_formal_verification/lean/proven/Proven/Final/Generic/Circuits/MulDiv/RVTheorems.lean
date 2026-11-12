module
public import Human.Circuits.MulDiv.RVTheorems
public import Proven.Defs.Circuits.MulDiv.RVModel

/-! The generic-prime forms of the claims of `human/Human/Circuits/MulDiv/RVTheorems.lean`, as stated before they were stated at BabyBear
(each premise set forces `p = babyBearModulus`). The proven proofs prove these and instantiate them. -/

@[expose] public section
namespace Airbender.MulDiv
open Trace
def RVSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 536870912 ≤ p) (_inverse : (-3840 : ZMod p) * 524288 = 1) (trace : PooledTrace p) (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

end Airbender.MulDiv
