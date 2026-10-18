import Airbender.Review.Helpers.Decoder.SparseSetup
import Airbender.Review.Circuits.JumpBranchSlt.Artifact

namespace Airbender.JumpBranchSlt
open Arithmetic

namespace Branch
def funct3 (opcode : SailRV32.bop) : Nat :=
  match opcode with
  | .BEQ => 0 | .BNE => 1 | .BLT => 4 | .BGE => 5 | .BLTU => 6 | .BGEU => 7

end Branch

/-- Native v2 signed/unsigned control metadata. Retain original x0 operations,
    separate SLT/SLTI masks, branch mask 16 and raw JAL encoding funct3 bits. -/
def decoderFields : SailRV32.instruction → Option (Trace.DecoderData Unit)
  | .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLT) =>
    some ⟨(), rs1, rs2, rd, ⟨0, 0⟩, 4, 2⟩
  | .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLTU) =>
    some ⟨(), rs1, rs2, rd, ⟨0, 0⟩, 4, 3⟩
  | .ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTI) =>
    some ⟨(), rs1, 0, rd,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 8, 2⟩
  | .ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTIU) =>
    some ⟨(), rs1, 0, rd,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 8, 3⟩
  | .BTYPE (imm, .Regidx rs2, .Regidx rs1, op) =>
    some ⟨(), rs1, rs2, 0,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 16, Branch.funct3 op⟩
  | .JAL (imm, .Regidx rd) =>
    some ⟨(), 0, 0, rd, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),
      1, imm.toNat / 4096 % 8⟩
  | .JALR (imm, .Regidx rs1, .Regidx rd) =>
    some ⟨(), rs1, 0, rd, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),
      2, 0⟩
  | _ => none

abbrev ProgramEntry := Trace.ProgramEntry Unit
abbrev sparseDecoderSetupImage := Trace.sparseDecoderSetupImageWith decoderFields
abbrev decoderQuery {p : Nat} (w : Nat → ZMod p) :=
  Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w

/-- Original public Sail bytes/decoding and every native query column. This
    supplies no register reads or instruction-execution/terminal result. -/
def Fetched {p : Nat} (w : Nat → ZMod p) (before : Reference.RiscV.Sail.State) : Prop :=
  ∃ entry : ProgramEntry, entry.SourceWith before decoderFields ∧ decoderQuery w = entry.query

end Airbender.JumpBranchSlt
