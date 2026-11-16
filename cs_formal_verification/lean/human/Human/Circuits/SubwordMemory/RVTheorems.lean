module
public import Human.Circuits.SubwordMemory.RVModel

@[expose] public section

/-! Row soundness and non-vacuity for the RV32 specification. -/

namespace Airbender.SubwordMemory

/-- LB, LBU, LH, LHU, SB and SH rows take one step of our RV32 spec (`RV.step`).
    The row cell is the aligned four-byte cell that contains the effective address.
    A misaligned halfword access or a store to ROM has no step. -/
def RVSoundnessClaim : Prop :=
  ∀ trace initial cells program,
    RVInterfaceAssumptions trace initial cells program →
    Properties.Soundness (rvModel trace initial cells program).relation rvSpec

/-- The soundness assumptions hold for a trace with a row of this family. -/
def RVSatisfiableClaim : Prop :=
  ∃ trace initial cells program input output w,
    RVInterfaceAssumptions trace initial cells program ∧
      (rvModel trace initial cells program).relation input output w

end Airbender.SubwordMemory
