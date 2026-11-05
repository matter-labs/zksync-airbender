import Human.Helpers.Decoder.RVProgram
import Human.Circuits.JumpBranchSlt.Artifact

namespace Airbender.JumpBranchSlt
open Arithmetic

/-- The branch condition's funct3 (as `Branch.funct3` on the encoding). -/
def Branch.rvFunct3 : RV.Cond → Nat
  | .eq => 0 | .ne => 1 | .lt => 4 | .ge => 5 | .ltu => 6 | .geu => 7

/-- Native metadata from `cs/src/gkr_circuits/jump_branch_slt_family/decoder.rs`, on `RV.Instr` (as `decoderFields`).
    Comparison writes to x0 are preprocessed to ADD/SUB NOPs, outside this family's table. -/
def rvDecoderFields : RV.Instr → Option (Trace.DecoderData Unit)
  | .op .slt rd rs1 rs2 => if rd = 0 then none else some ⟨(), rs1, rs2, rd, ⟨0, 0⟩, 4, 2⟩
  | .op .sltu rd rs1 rs2 => if rd = 0 then none else some ⟨(), rs1, rs2, rd, ⟨0, 0⟩, 4, 3⟩
  | .opImm .slt rd rs1 imm => if rd = 0 then none else some ⟨(), rs1, 0, rd, Word.ofBitVec imm, 4, 2⟩
  | .opImm .sltu rd rs1 imm => if rd = 0 then none else some ⟨(), rs1, 0, rd, Word.ofBitVec imm, 4, 3⟩
  | .branch cond rs1 rs2 offset => some ⟨(), rs1, rs2, 0, Word.ofBitVec offset, 24, Branch.rvFunct3 cond⟩
  | .jal rd offset => some ⟨(), 0, 0, rd, Word.ofBitVec offset, if rd = 0 then 17 else 1, 0⟩
  | .jalr rd rs1 offset => some ⟨(), rs1, 0, rd, Word.ofBitVec offset, if rd = 0 then 18 else 2, 0⟩
  | _ => none

abbrev RVProgramEntry := Trace.RVProgramEntry Unit
abbrev rvDecoderTable {p : Nat} [Fact p.Prime] (program : List RVProgramEntry) :=
  Trace.rvDecoderTable (p := p) program ()

end Airbender.JumpBranchSlt
