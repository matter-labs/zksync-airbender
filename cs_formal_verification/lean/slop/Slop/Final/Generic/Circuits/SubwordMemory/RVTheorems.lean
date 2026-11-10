module
public import Human.Circuits.SubwordMemory.RVTheorems
public import Slop.Defs.Circuits.SubwordMemory.RVModel

/-! The generic-prime forms of the claims of `human/Human/Circuits/SubwordMemory/RVTheorems.lean`, as stated before they were stated at BabyBear
(each premise set forces `p = babyBearModulus`). The slop proofs prove these and instantiate them. -/

@[expose] public section
namespace Airbender.SubwordMemory
open Trace
def RVSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 536870912 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (trace : PooledTrace p) (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      output.cell.toBitVec.toNat = (input.source.toBitVec + input.immediate.toBitVec).toNat / 4 * 4 ∧
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' (if input.store then
            (input.before.store output.cell.toBitVec output.data.toBitVec 4).setPC output.pc.toBitVec
          else (input.before.setReg input.rd output.data.toBitVec).setPC output.pc.toBitVec)

end Airbender.SubwordMemory
