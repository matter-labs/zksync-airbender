module
public import Human.Circuits.ShiftBinop.RVModel

@[expose] public section

/-! Row soundness and non-vacuity for the RV32 specification. -/

namespace Airbender.ShiftBinop

/-- XOR, OR, AND, SLL, SRL, SRA, their immediate forms, and REV8 take one step of our RV32 spec (`RV.step`). -/
def RVSoundnessClaim : Prop :=
  ∀ trace initial cells program,
    RVInterfaceAssumptions trace initial cells program →
    Properties.Soundness (rvModel trace initial cells program).relation rvSpec

/-- The soundness assumptions hold for a trace with a row of this family. -/
def RVSatisfiableClaim : Prop :=
  ∃ trace initial cells program input output w,
    RVInterfaceAssumptions trace initial cells program ∧
      (rvModel trace initial cells program).relation input output w

end Airbender.ShiftBinop
