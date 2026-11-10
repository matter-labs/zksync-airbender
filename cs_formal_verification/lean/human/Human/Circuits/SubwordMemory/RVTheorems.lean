module
public import Human.Circuits.SubwordMemory.RVModel
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! RV32 claims for LB/LBU/LH/LHU/SB/SH, stated against our spec (`RV.step`, `Human/ISA/RV32.lean`), not Sail: the
    row's pre-state is `input.before : RV.State`. `RV.step` has no next state for a misaligned halfword or a store
    into ROM, so the claims imply that the access is aligned and, for SB/SH, in RAM. Loads may read ROM or RAM. Proven
    in `slop/Slop/Final/Circuits/SubwordMemory/RVTheorems.lean` (checked in `test/Checks/Claims.lean`). -/

namespace Airbender.SubwordMemory
open Trace

/-- Every accepted subword row computes the aligned cell `(rs1 + immediate) / 4 * 4`, and is one step of our spec:
    from the row's pre-state (`input.before`), the step exists and gives the row's post-state: SB/SH store the
    circuit's merged word at the cell (the old word with the stored byte or halfword replaced), loads write the
    circuit's extended byte or halfword to `rd`; PC := the row's final PC; nothing else changed. -/
def RVSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 536870912 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (trace : PooledTrace p) (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      output.cell.toBitVec.toNat = (input.source.toBitVec + input.immediate.toBitVec).toNat / 4 * 4 ∧
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' (if input.store then
            (input.before.store output.cell.toBitVec output.data.toBitVec 4).setPC output.pc.toBitVec
          else (input.before.setReg input.rd output.data.toBitVec).setPC output.pc.toBitVec)

def BabyBearRVSoundnessClaim : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      output.cell.toBitVec.toNat = (input.source.toBitVec + input.immediate.toBitVec).toNat / 4 * 4 ∧
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' (if input.store then
            (input.before.store output.cell.toBitVec output.data.toBitVec 4).setPC output.pc.toBitVec
          else (input.before.setReg input.rd output.data.toBitVec).setPC output.pc.toBitVec)

end Airbender.SubwordMemory
