module
public import Human.Circuits.JumpBranchSlt.RVModel
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! RV32 claims for the comparison, branch and jump rows, stated against our spec (`RV.step`, `Human/ISA/RV32.lean`),
    not Sail: the row's pre-state is `input.before : RV.State`. `RV.Same` (`ISA/State.lean`) compares two `RV.State`s.
    Proven in `slop/Slop/Final/Circuits/JumpBranchSlt/RVTheorems.lean` (checked in `test/Checks/Claims.lean`).
    PC in ROM and 4-byte aligned is the decoder table's guard (`rvProgramEntryWith`). The step exists, so a taken
    branch or a jump lands on a 4-byte aligned target (`RV.State.jumpAligned`): the circuit's bit-1 check enforces it. -/

namespace Airbender.JumpBranchSlt

namespace Comparison

/-- Every accepted SLT/SLTI/SLTU/SLTIU row is one step of our spec from the row's pre-state: `rd` := the row's result,
    PC := the row's final PC, nothing else changed. -/
def RVSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 536870912 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (trace : Trace.PooledTrace p) (initial : RV.State) (cells : List Trace.Cell) (program : List Trace.RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

def BabyBearRVSoundnessClaim : Prop :=
  ∀ (trace : Trace.PooledTrace babyBearModulus) (initial : RV.State) (cells : List Trace.Cell) (program : List Trace.RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

end Comparison

namespace Branch

/-- Every accepted BEQ/BNE/BLT/BGE/BLTU/BGEU row is one step of our spec from the row's pre-state: PC := the row's
    final PC (the taken target or PC + 4), nothing else changed (the row's destination goes to x0). -/
def RVSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 536870912 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (trace : Trace.PooledTrace p) (initial : RV.State) (cells : List Trace.Cell) (program : List Trace.RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧ RV.Same s' (input.before.setPC output.pc.toBitVec)

def BabyBearRVSoundnessClaim : Prop :=
  ∀ (trace : Trace.PooledTrace babyBearModulus) (initial : RV.State) (cells : List Trace.Cell) (program : List Trace.RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧ RV.Same s' (input.before.setPC output.pc.toBitVec)

end Branch

namespace Jump

/-- Every accepted JAL/JALR row is one step of our spec from the row's pre-state: `rd` := the row's link value
    (x0: discarded), PC := the row's final PC (the jump target), nothing else changed. -/
def RVSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 536870912 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (trace : Trace.PooledTrace p) (initial : RV.State) (cells : List Trace.Cell) (program : List Trace.RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

def BabyBearRVSoundnessClaim : Prop :=
  ∀ (trace : Trace.PooledTrace babyBearModulus) (initial : RV.State) (cells : List Trace.Cell) (program : List Trace.RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

end Jump

end Airbender.JumpBranchSlt
