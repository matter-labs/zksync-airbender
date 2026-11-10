module
public import Human.Circuits.MulDiv.RVModel
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! RV32 claims for MUL/MULHU/DIVU/REMU, stated against our spec (`RV.step`, `Human/ISA/RV32.lean`), not Sail:
    the row's pre-state is `input.before : RV.State`. `RV.alu` gives DIVU by zero = all ones and REMU by zero = the
    dividend. Proven in `slop/Slop/Final/Circuits/MulDiv/RVTheorems.lean` (checked in `test/Checks/Claims.lean`). -/

namespace Airbender.MulDiv
open Trace

/-- Every accepted MUL/MULHU/DIVU/REMU row is one step of our spec: from the row's pre-state (`input.before`), the
    step exists and gives the row's post-state: `rd` := the row's result, PC := the row's final PC, nothing else
    changed. -/
def RVSoundnessClaim : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

end Airbender.MulDiv
