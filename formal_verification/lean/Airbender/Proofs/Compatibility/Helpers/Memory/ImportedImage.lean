import Airbender.Review.Helpers.Memory.ROM
import Airbender.Data.Program.Native

namespace Airbender.Trace.ROM

/-- Public starting bytes for the complete selected image. This binds an
    independent public input, rather than specifying any witness load result. -/
def ImportedImage (before : Reference.RiscV.Sail.State) : Prop :=
  ∀ index : Fin nativeProgramData.image_words,
    (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 (4 * index.val)).run before =
      .ok (BitVec.ofNat 32 ((nativeProgramData.image.get? index.val).getD 0)) before

end Airbender.Trace.ROM
