import Human.Circuits.UnifiedReduced.Decoder
import Human.Circuits.JumpBranchSlt.RVDecoder
import Human.Circuits.ShiftBinop.RVDecoder

/-! The unified program table on `RV.Instr`: `Mixed.decoderFields` (standard `decoderFields` and the TRIADD/XORROT
    `customDecoderFields`) restated in `RV.decode`'s vocabulary (immediates already sign-extended or shifted), plus the
    reduced machine's x0 preprocessing. Same Rust decoder: `cs/src/gkr_circuits/unified_reduced_machine/decoder.rs`. -/

namespace Airbender.UnifiedReduced
open Arithmetic Trace

/-- Rust's preprocessing for the reduced machine (`pure_from_imm` in
    `riscv_transpiler/src/ir/simple_instruction_set.rs`, `ReducedMachineDecoderConfig`): a pure instruction that the
    reduced machine decodes and that writes x0 becomes `Nop`. These are OP without the M extension (which the reduced
    machine rejects), OP-IMM, LUI, AUIPC, `rev8`, LW (subword loads are rejected), `mop.rr.N` and `mop.r.N`. -/
def rvNopWrite : RV.Instr → Bool
  | .op .mul _ _ _ | .op .mulhu _ _ _ | .op .divu _ _ _ | .op .remu _ _ _ => false
  | .op _ rd _ _ | .opImm _ rd _ _ | .lui rd _ | .auipc rd _ | .rev8 rd _ | .load 4 true rd _ _
  | .mop _ rd _ _ | .xorRot _ rd _ => rd = 0
  | _ => false

/-- The `Nop` row: ADD with zero registers and immediate (`add_sub_family/decoder.rs`). -/
def rvNopFields : DecoderData UnifiedFamily := ⟨.machine, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩

/-- ADD/SUB/ADDI/LUI/AUIPC and LW/SW (`add_sub_family`, `mem_word_only` decoders; the destination is not x0), with the
    unified LW/SW bits 17/18 (as `arithmeticFields`). LUI is ADD of x0 and the immediate. -/
def rvWordFields : RV.Instr → Option (DecoderData UnifiedFamily)
  | .op .add rd rs1 rs2 => some ⟨.machine, rs1, rs2, rd, ⟨0, 0⟩, 1, 0⟩
  | .op .sub rd rs1 rs2 => some ⟨.machine, rs1, rs2, rd, ⟨0, 0⟩, 2, 0⟩
  | .opImm .add rd rs1 imm => some ⟨.machine, rs1, 0, rd, Word.ofBitVec imm, 1, 0⟩
  | .lui rd imm => some ⟨.machine, 0, 0, rd, Word.ofBitVec imm, 1, 0⟩
  | .auipc rd imm => some ⟨.machine, 0, 0, rd, Word.ofBitVec imm, 4, 0⟩
  | .load 4 true rd rs1 imm => some ⟨.machine, rs1, 0, rd, Word.ofBitVec imm, 131072, 0⟩
  | .store 4 rs2 rs1 imm => some ⟨.machine, rs1, rs2, 0, Word.ofBitVec imm, 262144, 0⟩
  | _ => none

/-- TRIADD (`mop.rr.4`) reads the old destination through its third port (bit 9); XORROT (`mop.r.N`, N = 16, 12, 8,
    7) reads it as rs2 on the binary selector (bit 16) with the XorRotate table ID (as `customDecoderFields`). -/
def rvCustomFields : RV.Instr → Option (DecoderData UnifiedFamily)
  | .mop .triAdd rd rs1 rs2 => some ⟨.machine, rs1, rs2, rd, ⟨0, 0⟩, 512, 0⟩
  | .xorRot n rd rs1 => (customRotationTag n).map fun tag => ⟨.machine, rs1, rd, rd, ⟨0, 0⟩, 65536, tag⟩
  | _ => none

/-- Native metadata of an instruction of the unified table: x0 preprocessing first, then the family decoders in
    Rust's order (add/sub and word memory, jump/branch/comparison on bits 10–14, shift/binary on bits 15–16 with the
    Wide table IDs), then TRIADD/XORROT. Other instructions (M extension, subword memory, the other `mop.rr.N`, CSRs)
    are not admitted: a program containing them has no table. -/
def rvDecoderFields (i : RV.Instr) : Option (DecoderData UnifiedFamily) :=
  if rvNopWrite i then some rvNopFields else
    rvWordFields i <|> (JumpBranchSlt.rvDecoderFields i).map jumpFields <|>
      (ShiftBinop.rvDecoderFields i).map binaryFields <|> rvCustomFields i

abbrev RVProgramEntry := Trace.RVProgramEntry Trace.UnifiedFamily

abbrev rvDecoderTable {p : Nat} [Fact p.Prime] (program : List RVProgramEntry) :=
  Trace.rvDecoderTable (p := p) program .machine

/-- Every row's native query belongs to the RV program table (a logical lookup boundary, as `Decoded`). -/
def RVDecoded [Fact p.Prime] (trace : Trace.UnifiedTrace p) (program : List RVProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (rvDecoderTable program).Contains #[] row.decoderQuery

end Airbender.UnifiedReduced
