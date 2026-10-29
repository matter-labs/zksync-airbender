import Airbender.Review.Helpers.Memory.ROM

namespace Airbender.Trace.ROM

/-- Every public program word is read from the supplied initial Sail state at
its native byte PC. The caller separately binds the remaining padded ROM cells
and the native setup; this predicate supplies no witness value or result. -/
def TextImage (before : Reference.RiscV.Sail.State)
    (text : List (BitVec 32)) : Prop :=
  ∀ index : Fin text.length,
    (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 (4 * index.val)).run before =
      .ok text[index.val] before

end Airbender.Trace.ROM
