module
public import Human.Helpers.Decoder.RVProgram
public import Human.Circuits.SubwordMemory.Artifact

@[expose] public section

namespace Airbender.SubwordMemory
open Arithmetic

/-- Native metadata from `mem_subword_only/decoder.rs` (store, byte and sign-extension bits), on `RV.Instr` (as
    `decoderFields`). Loads to x0 are routed outside this family. -/
def rvDecoderFields : RV.Instr → Option (Trace.DecoderData Unit)
  | .load 1 true rd rs1 imm => if rd = 0 then none else some ⟨(), rs1, 0, rd, Word.ofBitVec imm, 6, 0⟩   -- lb
  | .load 1 false rd rs1 imm => if rd = 0 then none else some ⟨(), rs1, 0, rd, Word.ofBitVec imm, 2, 0⟩  -- lbu
  | .load 2 true rd rs1 imm => if rd = 0 then none else some ⟨(), rs1, 0, rd, Word.ofBitVec imm, 4, 0⟩   -- lh
  | .load 2 false rd rs1 imm => if rd = 0 then none else some ⟨(), rs1, 0, rd, Word.ofBitVec imm, 0, 0⟩  -- lhu
  | .store 1 rs2 rs1 imm => some ⟨(), rs1, rs2, 0, Word.ofBitVec imm, 3, 0⟩                             -- sb
  | .store 2 rs2 rs1 imm => some ⟨(), rs1, rs2, 0, Word.ofBitVec imm, 1, 0⟩                             -- sh
  | _ => none

abbrev RVProgramEntry := Trace.RVProgramEntry Unit
abbrev rvDecoderTable {p : Nat} [Fact p.Prime] (program : List RVProgramEntry) :=
  Trace.rvDecoderTable (p := p) program ()

end Airbender.SubwordMemory
