module
public import Human.Circuits.ShiftBinop.RVModel
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! RV32 claims for XOR/OR/AND, SLL/SRL/SRA (register and immediate forms) and REV8, stated against our spec
    (`RV.step`, `Human/ISA/RV32.lean`), not Sail: the row's pre-state is `input.before : RV.State`. `RV.alu` shifts by
    the low five bits of the amount. Proven in `slop/Slop/Final/Circuits/ShiftBinop/RVTheorems.lean` (checked in
    `test/Checks/Claims.lean`). -/

namespace Airbender.ShiftBinop
open Trace

/-- Every accepted shift/binop row is one step of our spec: from the row's pre-state (`input.before`), the step
    exists and gives the row's post-state: `rd` := the row's result, PC := the row's final PC, nothing else changed. -/
def RVSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1) (trace : PooledTrace p) (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

def BabyBearRVSoundnessClaim : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

end Airbender.ShiftBinop
