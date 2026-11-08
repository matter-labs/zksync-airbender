import Human.Circuits.ShiftBinop.Artifact
import Human.Helpers.Decoder.Program

namespace Airbender.ShiftBinop
open Arithmetic

/-- `binary_shifts_family/decoder.rs` splits a binary immediate into two
    byte-valued columns. This is native metadata, not instruction semantics. -/
def binaryImmediate (bits : BitVec 32) : Word :=
  ⟨bits.toNat % 256, bits.toNat / 256 % 256⟩

def instructionFields (operation : Operation) (rs1 rs2 rd : BitVec 5) (immediate : Word) :
    Option (Trace.DecoderData Unit) :=
  if rd = 0 then none else some ⟨(), rs1, rs2, rd, immediate,
    if operation.isShift then 1 else 2, operation.tag⟩

abbrev decoderQuery {p : Nat} (w : Nat → ZMod p) :=
  Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w

end Airbender.ShiftBinop
