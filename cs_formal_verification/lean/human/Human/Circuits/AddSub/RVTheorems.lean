module
public import Human.Circuits.AddSub.RVModel

@[expose] public section

/-! Row soundness and non-vacuity for the RV32 specification. -/

namespace Airbender.AddSub

/-- Every accepted row of this family is one step of the RV32 specification. -/
def RVSoundnessClaim : Prop :=
  ∀ trace initial cells program,
    RVInterfaceAssumptions trace initial cells program →
    Properties.Soundness (rvModel trace initial cells program).relation rvSpec

/-- The soundness assumptions hold for a trace with a row of this family. -/
def RVSatisfiableClaim : Prop :=
  ∃ trace initial cells program input output w,
    RVInterfaceAssumptions trace initial cells program ∧
      (rvModel trace initial cells program).relation input output w

end Airbender.AddSub
