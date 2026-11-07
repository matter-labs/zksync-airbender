import Human.Helpers.Decoder.Program
import Human.ISA.RV32

/-! The public program table in RV32 terms. An entry is a ROM word: its PC, its four bytes and the native decoder
    metadata of `RV.decode` of those bytes. There is no instruction field: the instruction is `RV.decode entry.bits`.
    The metadata projections are functions of `RV.Instr` (this file: ADD/SUB/ADDI/LUI/AUIPC and LW/SW; the other
    families in `Circuits/*/RVDecoder.lean`), following the same Rust decoders as the Sail-typed `decoderFields`. -/

noncomputable section

namespace Airbender.Trace
open Arithmetic

/-- One public instruction entry: `pc` locates its four `bits` bytes, `data` is the native metadata of
    `RV.decode bits`. Public-image construction binds these fields together; the record alone guarantees nothing. -/
structure RVProgramEntry (Kind : Type := Family) where
  pc : BitVec 32
  bits : BitVec 32
  data : DecoderData Kind

/-- Change only the circuit registry tag. -/
def RVProgramEntry.mapFamily {Kind Target : Type} (f : Kind → Target)
    (entry : RVProgramEntry Kind) : RVProgramEntry Target :=
  ⟨entry.pc, entry.bits, entry.data.mapFamily f⟩

/-- Rust's nine-column decoder row (as `ProgramEntry.query`); omitted funct3 is zero. -/
def RVProgramEntry.query {Kind : Type} {p : Nat} (entry : RVProgramEntry Kind) : Vector (ZMod p) 9 :=
  let pc := Word.ofBitVec entry.pc
  #v[pc.lo, pc.hi, entry.data.rs1.toNat, entry.data.rs2.toNat, entry.data.rd.toNat,
    entry.data.immediate.lo, entry.data.immediate.hi, entry.data.funct3, entry.data.mask]

/-- A family table made from successful public-image construction (as `decoderTable`). -/
def rvDecoderTable {Kind : Type} [DecidableEq Kind] {p : Nat} [Fact p.Prime]
    (program : List (RVProgramEntry Kind)) (family : Kind) : Table (ZMod p) (fields 9) := .fromStatic {
  name := "Airbender.NativeDecoder"
  length := (program.filter fun entry => entry.data.family == family).length
  row i := ((program.filter fun entry => entry.data.family == family).get i).query
  index query := (program.filter fun entry => entry.data.family == family).toArray.findIdx
    (fun entry => entry.query == query)
  Spec query := ∃ entry ∈ program, entry.data.family = family ∧ query = entry.query
  contains_iff := by
    intro query
    constructor
    · rintro ⟨i, rfl⟩
      have member := List.get_mem (program.filter fun entry => entry.data.family == family) i
      obtain ⟨member, selected⟩ := List.mem_filter.mp member
      exact ⟨_, member, by simpa using selected, rfl⟩
    · rintro ⟨entry, member, selected, equal⟩
      have filtered : entry ∈ program.filter (fun entry => entry.data.family == family) := by
        simp [member, selected]
      obtain ⟨i, index⟩ := List.mem_iff_get.mp filtered
      exact ⟨i, equal.trans (congrArg RVProgramEntry.query index).symm⟩
}

/-- The public encoding is read from our spec's ROM image (`RV.read` of `rom`), decoded by `RV.decode`, then projected to
    native metadata. The fetch guard is the ROM bound and alignment of `RV.step` (`RV.ROM_END`). -/
noncomputable abbrev rvProgramEntryWith {Kind : Type}
    (projection : RV.Instr → Option (DecoderData Kind))
    (before : RV.State) (pc : BitVec 32) :
    Option (RVProgramEntry Kind) := do
  if ¬(pc.toNat < RV.ROM_END ∧ pc.toNat % 4 = 0) then none else
  let bits := RV.read before.rom pc 4
  let i ← RV.decode bits
  let data ← projection i
  pure ⟨pc, bits, data⟩

/-- Entries for the public `addresses`; an undecodable or unsupported word makes it fail. -/
noncomputable abbrev rvProgramImageWith {Kind : Type}
    (projection : RV.Instr → Option (DecoderData Kind))
    (before : RV.State) (addresses : List (BitVec 32)) :
    Option (List (RVProgramEntry Kind)) := addresses.mapM (rvProgramEntryWith projection before)

/-- Native metadata of ADD/SUB/ADDI/LUI/AUIPC and LW/SW (`add_sub_family/decoder.rs`, `mem_word_only/decoder.rs`),
    as `decoderFields`. Immediates are `RV.decode`'s (already sign-extended or shifted). Every pure instruction
    (ALU, M, `rev8`, load) writing x0 becomes a native NOP row, as Rust's preprocessing does (`pure_from_imm` in
    `riscv_transpiler/src/ir/simple_instruction_set.rs`; the family decoders reject rd = x0). -/
def rvDecoderFields : RV.Instr → Option DecoderData
  | .op .add rd rs1 rs2 => some (arithmeticFields rs1 rs2 rd 0 1)
  | .op .sub rd rs1 rs2 => some (arithmeticFields rs1 rs2 rd 0 2)
  | .opImm .add rd rs1 imm => some (arithmeticFields rs1 0 rd imm 1)
  | .lui rd imm => some (arithmeticFields 0 0 rd imm 1)
  | .auipc rd imm => some (arithmeticFields 0 0 rd imm 4)
  | .load 4 true rd rs1 imm =>
    if rd = 0 then some (arithmeticFields 0 0 0 0 1)
    else some ⟨.wordMemory, rs1, 0, rd, Word.ofBitVec imm, 0, 0⟩
  | .store 4 rs2 rs1 imm => some ⟨.wordMemory, rs1, rs2, 0, Word.ofBitVec imm, 1, 0⟩
  | .op _ rd _ _ | .opImm _ rd _ _ | .rev8 rd _ | .load _ _ rd _ _ =>
    if rd = 0 then some (arithmeticFields 0 0 0 0 1) else none
  | _ => none

end Airbender.Trace
