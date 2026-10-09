import Airbender.Review.Trace.Program
import Airbender.Review.JumpBranchSlt.Artifact

namespace Airbender.JumpBranchSlt
open Arithmetic

/-- Native metadata from `cs/src/gkr_circuits/jump_branch_slt_family/decoder.rs`.
    Instruction behavior remains the original Sail specification. Comparison
    writes to x0 are preprocessed to ADD/SUB NOPs, outside this family's table. -/
def decoderFields : SailRV32.instruction → Option (Trace.DecoderData Unit)
  | .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLT) =>
    if rd = 0 then none else some ⟨(), rs1, rs2, rd, ⟨0, 0⟩, 4, 2⟩
  | .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLTU) =>
    if rd = 0 then none else some ⟨(), rs1, rs2, rd, ⟨0, 0⟩, 4, 3⟩
  | .ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTI) =>
    if rd = 0 then none else some ⟨(), rs1, 0, rd,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 4, 2⟩
  | .ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTIU) =>
    if rd = 0 then none else some ⟨(), rs1, 0, rd,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 4, 3⟩
  | .BTYPE (imm, .Regidx rs2, .Regidx rs1, op) =>
    some ⟨(), rs1, rs2, 0,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 24, Branch.funct3 op⟩
  | .JAL (imm, .Regidx rd) =>
    some ⟨(), 0, 0, rd, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),
      if rd = 0 then 17 else 1, 0⟩
  | .JALR (imm, .Regidx rs1, .Regidx rd) =>
    some ⟨(), rs1, 0, rd, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),
      if rd = 0 then 18 else 2, 0⟩
  | _ => none

abbrev ProgramEntry := Trace.ProgramEntry Unit
abbrev programImage := Trace.programImageWith decoderFields
abbrev decoderTable {p : Nat} [Fact p.Prime] (program : List ProgramEntry) :=
  Trace.decoderTable (p := p) program ()
abbrev decoderQuery {p : Nat} (w : Nat → ZMod p) :=
  Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w

/-- Public bytes are decoded by Sail. Logical native membership fixes every
    query column; the artifact's Boolean equations recover all five selector bits.
    This does not assume register reads or discharge global history matching. -/
def Fetched {p : Nat} (w : Nat → ZMod p) (before : Reference.RiscV.Sail.State) : Prop :=
  ∃ entry : ProgramEntry, entry.SourceWith before decoderFields ∧
    decoderQuery w = entry.query ∧ entry.data.immediate.Bounded ∧ entry.data.funct3 < 8 ∧
    ∀ i : Fin 5,
      w importedConstraintsDecoderColumns.flags[i] = if entry.data.mask.testBit i.val then 1 else 0

end Airbender.JumpBranchSlt
