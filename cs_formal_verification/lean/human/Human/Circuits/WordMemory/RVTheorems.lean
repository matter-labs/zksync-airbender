module
public import Human.Circuits.WordMemory.RVModel
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! RV32 claims for LW/SW, stated against our spec (`RV.step`, `Human/ISA/RV32.lean`), not Sail: the row's pre-state
    is `input.before : RV.State`. `RV.step` has no next state for a misaligned access or a store into ROM, so the
    claims imply that the access is aligned and, for SW, in RAM. Proven in
    `slop/Slop/Final/Circuits/WordMemory/RVTheorems.lean` (checked in `test/Checks/Claims.lean`). -/

namespace Airbender.WordMemory
open Trace

/-- Every accepted LW/SW row computes the effective address `rs1 + immediate`, and is one step of our spec: from the
    row's pre-state (`input.before`), the step exists and gives the row's post-state: SW stores the row's word at the
    row's address, LW writes the row's word to `rd`; PC := the row's final PC; nothing else changed. -/
def RVSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1) (trace : PooledTrace p) (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      output.address.toBitVec = input.source.toBitVec + input.immediate.toBitVec ∧
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' (if input.store then
            (input.before.store output.address.toBitVec output.data.toBitVec 4).setPC output.pc.toBitVec
          else (input.before.setReg input.rd output.data.toBitVec).setPC output.pc.toBitVec)

def BabyBearRVSoundnessClaim : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      output.address.toBitVec = input.source.toBitVec + input.immediate.toBitVec ∧
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' (if input.store then
            (input.before.store output.address.toBitVec output.data.toBitVec 4).setPC output.pc.toBitVec
          else (input.before.setReg input.rd output.data.toBitVec).setPC output.pc.toBitVec)

end Airbender.WordMemory
