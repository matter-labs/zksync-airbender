module
public import Human.Circuits.JumpBranchSlt.RVTheorems
public import Proven.Defs.Circuits.JumpBranchSlt.RVModel

/-! The generic-prime forms of the claims of `human/Human/Circuits/JumpBranchSlt/RVTheorems.lean`, as stated before they were stated at BabyBear
(each premise set forces `p = babyBearModulus`). The proven proofs prove these and instantiate them. -/

@[expose] public section
namespace Airbender.JumpBranchSlt
namespace Comparison
def RVSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 536870912 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (trace : Trace.PooledTrace p) (initial : RV.State) (cells : List Trace.Cell) (program : List Trace.RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

end Comparison
namespace Branch
def RVSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 536870912 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (trace : Trace.PooledTrace p) (initial : RV.State) (cells : List Trace.Cell) (program : List Trace.RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧ RV.Same s' (input.before.setPC output.pc.toBitVec)

end Branch
namespace Jump
def RVSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 536870912 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (trace : Trace.PooledTrace p) (initial : RV.State) (cells : List Trace.Cell) (program : List Trace.RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

end Jump
end Airbender.JumpBranchSlt
