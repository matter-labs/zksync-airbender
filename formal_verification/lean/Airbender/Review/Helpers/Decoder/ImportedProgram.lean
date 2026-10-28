import Airbender.Review.Helpers.Decoder.Program
import Airbender.Data.Program.Native

namespace Airbender.Trace.NativeDecoder

/-- Successful pinned Sail decoding of the actual selected text. Unsupported
    instructions are absent from a family's active semantic query set. This is
    a specification projection of imported bytes, independent of the witness. -/
def selectedEntry {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (index : Fin ROM.nativeProgramData.text_words) : Option (ProgramEntry Kind) := do
  let bits := BitVec.ofNat 32 ((ROM.nativeProgramData.text.get? index.val).getD 0)
  let instruction ← match SailRV32.Functions.encdec_backwards bits with
    | .pure instruction => some instruction
    | .impure _ _ => none
  let data ← projection instruction
  pure ⟨BitVec.ofNat 32 (4 * index.val), bits, instruction, data⟩

def selectedProgram {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind)) : List (ProgramEntry Kind) :=
  (List.finRange ROM.nativeProgramData.text_words).filterMap (selectedEntry projection)

/-- Public byte-image binding for this exported program. Registers and other
    Sail configuration remain arbitrary; the retained corpus is never silently
    substituted into the generalized execution theorems. -/
def SelectedBytes (before : Reference.RiscV.Sail.State) : Prop :=
  ∀ index : Fin ROM.nativeProgramData.text_words,
    (Cell.ram (BitVec.ofNat 32 (4 * index.val))).read before =
      .ok (BitVec.ofNat 32 ((ROM.nativeProgramData.text.get? index.val).getD 0)) before

end Airbender.Trace.NativeDecoder
