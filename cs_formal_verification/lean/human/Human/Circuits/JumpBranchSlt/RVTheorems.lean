module
public import Human.Circuits.JumpBranchSlt.RVModel

@[expose] public section

/-! Row soundness and non-vacuity for the RV32 specification. -/

namespace Airbender.JumpBranchSlt

namespace Comparison

/-- SLT, SLTI, SLTU and SLTIU rows take one step of our RV32 spec (`RV.step`). -/
def RVSoundnessClaim : Prop :=
  ∀ trace initial cells program,
    RVInterfaceAssumptions trace initial cells program →
    Properties.Soundness (rvModel trace initial cells program).relation rvSpec

/-- The soundness assumptions hold for a trace with a row of this family. -/
def RVSatisfiableClaim : Prop :=
  ∃ trace initial cells program input output w,
    RVInterfaceAssumptions trace initial cells program ∧
      (rvModel trace initial cells program).relation input output w

end Comparison

namespace Branch

/-- BEQ, BNE, BLT, BGE, BLTU and BGEU rows take one step of our RV32 spec (`RV.step`). -/
def RVSoundnessClaim : Prop :=
  ∀ trace initial cells program,
    RVInterfaceAssumptions trace initial cells program →
    Properties.Soundness (rvModel trace initial cells program).relation rvSpec

/-- The soundness assumptions hold for a trace with a row of this family. -/
def RVSatisfiableClaim : Prop :=
  ∃ trace initial cells program input output w,
    RVInterfaceAssumptions trace initial cells program ∧
      (rvModel trace initial cells program).relation input output w

end Branch

namespace Jump

/-- JAL and JALR rows take one step of our RV32 spec (`RV.step`). -/
def RVSoundnessClaim : Prop :=
  ∀ trace initial cells program,
    RVInterfaceAssumptions trace initial cells program →
    Properties.Soundness (rvModel trace initial cells program).relation rvSpec

/-- The soundness assumptions hold for a trace with a row of this family. -/
def RVSatisfiableClaim : Prop :=
  ∃ trace initial cells program input output w,
    RVInterfaceAssumptions trace initial cells program ∧
      (rvModel trace initial cells program).relation input output w

end Jump

end Airbender.JumpBranchSlt
