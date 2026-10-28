import Airbender.Review.Helpers.Memory.ROM

namespace Airbender.Trace.ROM

/-- Public text words in the initial Sail memory, at the same byte addresses
used by native decoder setup. This is parametric in the program and assumes no
instruction result or witness value. The setup's padded extent is a separate
public value. -/
def ProgramImage (before : Reference.RiscV.Sail.State)
    (text : List (BitVec 32)) : Prop :=
  ∀ index : Fin text.length,
    (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 (4 * index.val)).run before =
      .ok (text.get index) before

end Airbender.Trace.ROM
