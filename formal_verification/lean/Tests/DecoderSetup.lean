import Airbender.Review.Helpers.Decoder.Program

namespace Tests.DecoderSetup
open Airbender Trace

/-- V2 U-type funct3 retains the actual low three immediate-encoding bits. -/
theorem upper_funct3 : decoderFields (.UTYPE (7, .Regidx 1, .LUI)) =
    some ⟨.addSub, 0, 0, 1, ⟨28672, 0⟩, 8, 7⟩ := rfl

theorem negative_immediate : decoderFields (.ITYPE (0xfff, .Regidx 1, .Regidx 2, .ADDI)) =
    some ⟨.addSub, 1, 0, 2, ⟨65535, 65535⟩, 2, 0⟩ := rfl

theorem x0_retains_sub : decoderFields (.RTYPE (.Regidx 2, .Regidx 1, .Regidx 0, .SUB)) =
    some ⟨.addSub, 1, 2, 0, ⟨0, 0⟩, 4, 0⟩ := rfl

end Tests.DecoderSetup
