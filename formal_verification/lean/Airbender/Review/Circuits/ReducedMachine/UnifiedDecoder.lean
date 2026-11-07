import Airbender.Review.Circuits.ReducedMachine.SupportedDecoder
import Airbender.Review.Circuits.ReducedMachine.WordMemoryDecoder

namespace Airbender.ReducedMachine.Native
set_option autoImplicit false

/-- Seven checked profiles in one original projection. Keep the existing
    six-profile SupportedMode/projection/interfaces unchanged. -/
abbrev UnifiedMode := Sum SupportedMode WordMemoryMode

def unifiedDecoderFields (instruction : SailRV32.instruction) : Option (Trace.DecoderData UnifiedMode) :=
  match supportedDecoderFields instruction with
  | some data => some (data.mapFamily Sum.inl)
  | none => (wordMemoryDecoderFields instruction).map (Trace.DecoderData.mapFamily Sum.inr)

abbrev UnifiedProgramEntry := Trace.ProgramEntry UnifiedMode
abbrev unifiedDecoderSetupImage := Trace.sparseDecoderSetupImageRunWith unifiedDecoderFields

end Airbender.ReducedMachine.Native
