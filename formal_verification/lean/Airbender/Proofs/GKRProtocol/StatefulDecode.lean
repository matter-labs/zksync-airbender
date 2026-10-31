import Airbender.Review.Helpers.Decoder.ProgramRows
import Airbender.Proofs.Sail.DecoderFrame

namespace Airbender.Trace.NativeDecoder.ProgramRows.Proofs
open Reference.Sail
set_option warningAsError true

/-- Public decoding returns the actual Sail instruction and preserves the
initial state. Reading misa adds no decoder-result or state-frame premise. -/
theorem decode_word_sound {initial : Reference.RiscV.Sail.State} {bits : BitVec 32}
    {instruction : SailRV32.instruction}
    (decoded : decodeWord initial bits = some instruction) :
    run (SailRV32.Functions.encdec_backwards bits) initial = .ok instruction initial := by
  cases executed : run (SailRV32.Functions.encdec_backwards bits) initial with
  | error error after => simp [decodeWord, executed] at decoded
  | ok actual after =>
    have same : actual = instruction := by simpa only [decodeWord, executed, Option.some.injEq] using decoded
    subst actual
    have unchanged := (decoded_misa_frame bits executed).1
    subst after
    rfl

end Airbender.Trace.NativeDecoder.ProgramRows.Proofs
