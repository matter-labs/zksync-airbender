import Airbender.Review.Helpers.Decoder.StatefulSetup
import Airbender.Review.Circuits.MulDiv.Model

namespace Airbender.MulDiv
open Arithmetic

/-- Actual unsigned v2 funct3 tags, independent of the packed two-bit mask. -/
def Operation.funct3 : Operation → Nat
  | .mul => 0 | .mulhu => 3 | .divu => 5 | .remu => 7

/-- Native v2 family-decoder metadata for the original four unsigned Sail
    constructors. Keep original x0 operations and the separate destination flag. -/
def decoderFields : SailRV32.instruction → Option (Trace.DecoderData Operation)
  | .MUL (.Regidx rs2,.Regidx rs1,.Regidx rd,⟨.Low,.Signed,.Signed⟩) =>
    some ⟨.mul,rs1,rs2,rd,⟨0,0⟩,2,0⟩
  | .MUL (.Regidx rs2,.Regidx rs1,.Regidx rd,⟨.High,.Unsigned,.Unsigned⟩) =>
    some ⟨.mulhu,rs1,rs2,rd,⟨0,0⟩,0,3⟩
  | .DIV (.Regidx rs2,.Regidx rs1,.Regidx rd,true) =>
    some ⟨.divu,rs1,rs2,rd,⟨0,0⟩,3,5⟩
  | .REM (.Regidx rs2,.Regidx rs1,.Regidx rd,true) =>
    some ⟨.remu,rs1,rs2,rd,⟨0,0⟩,1,7⟩
  | _ => none

abbrev ProgramEntry := Trace.ProgramEntry Operation
abbrev sparseDecoderSetupImage := Trace.sparseDecoderSetupImageRunWith decoderFields
abbrev decoderQuery {p : Nat} (w : Nat → ZMod p) :=
  Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w

/-- Original public bytes/decoding bound to every actual native query column. -/
def Fetched {p : Nat} (w : Nat → ZMod p) (before : Reference.RiscV.Sail.State) : Prop :=
  ∃ entry : ProgramEntry, entry.SourceWith before decoderFields ∧ decoderQuery w = entry.query

end Airbender.MulDiv
