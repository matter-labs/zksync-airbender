import Airbender.Review.Circuits.ReducedMachine.ArithmeticDecoder
import Airbender.Review.Circuits.ReducedMachine.BitwiseDecoder
import Airbender.Review.Circuits.ReducedMachine.ComparisonDecoder
import Airbender.Review.Circuits.ReducedMachine.BranchDecoder
import Airbender.Review.Circuits.ReducedMachine.JumpDecoder

namespace Airbender.ReducedMachine.Native

/-- The currently checked original shift, arithmetic, bitwise, comparison, branch and jump profiles, in one public
    projection. Other combined instructions remain unsupported. -/
abbrev SupportedMode := Sum ShiftMode (Sum ArithmeticMode (Sum BitwiseMode (Sum ComparisonMode (Sum BranchMode JumpMode))))

def supportedDecoderFields (instruction : SailRV32.instruction) : Option (Trace.DecoderData SupportedMode) :=
  match shiftDecoderFields instruction with
  | some data => some (data.mapFamily Sum.inl)
  | none =>
    match arithmeticDecoderFields instruction with
    | some data => some (data.mapFamily (Sum.inr ∘ Sum.inl))
    | none =>
      match bitwiseDecoderFields instruction with
      | some data => some (data.mapFamily (Sum.inr ∘ Sum.inr ∘ Sum.inl))
      | none =>
        match comparisonDecoderFields instruction with
        | some data => some (data.mapFamily (Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl))
        | none =>
          match branchDecoderFields instruction with
          | some data => some (data.mapFamily (Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl))
          | none => (jumpDecoderFields instruction).map
              (Trace.DecoderData.mapFamily (Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr))

abbrev SupportedProgramEntry := Trace.ProgramEntry SupportedMode
abbrev supportedDecoderSetupImage := Trace.sparseDecoderSetupImageRunWith supportedDecoderFields

end Airbender.ReducedMachine.Native
