import Airbender.Review.Circuits.ReducedMachine.ArithmeticDecoder

namespace Airbender.ReducedMachine.Native

/-- The currently checked original shift and arithmetic profiles, in one public
    projection. Other combined instructions remain unsupported. -/
abbrev SupportedMode := Sum ShiftMode ArithmeticMode

def supportedDecoderFields (instruction : SailRV32.instruction) : Option (Trace.DecoderData SupportedMode) :=
  match shiftDecoderFields instruction with
  | some data => some (data.mapFamily Sum.inl)
  | none => (arithmeticDecoderFields instruction).map (Trace.DecoderData.mapFamily Sum.inr)

abbrev SupportedProgramEntry := Trace.ProgramEntry SupportedMode
abbrev supportedDecoderSetupImage := Trace.sparseDecoderSetupImageRunWith supportedDecoderFields

end Airbender.ReducedMachine.Native
