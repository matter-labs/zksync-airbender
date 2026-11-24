module
public import Human.Circuits.WordMemory.RVModel

@[expose] public section

/-! Row soundness and non-vacuity for the RV32 specification. -/

namespace Airbender.WordMemory

/-- LW and SW rows take one step of our RV32 spec (`RV.step`).
    The effective address equals the source plus the immediate, modulo `2 ^ 32`, and is aligned to four bytes.
    A misaligned access or a store to ROM has no step. -/
def RVSoundnessClaim : Prop :=
  ∀ trace initial cells program,
    RVInterfaceAssumptions trace initial cells program →
    Properties.Soundness (rvModel trace initial cells program).relation rvSpec

/-- The soundness assumptions hold for a trace with a row of this family. -/
def RVSatisfiableClaim : Prop :=
  ∃ trace initial cells program input output w,
    RVInterfaceAssumptions trace initial cells program ∧
      (rvModel trace initial cells program).relation input output w

end Airbender.WordMemory
