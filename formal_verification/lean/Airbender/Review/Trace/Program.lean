import Airbender.Review.Trace.InitialImage

namespace Airbender.Trace
open Arithmetic

/-- Native decoder fields, not instruction behavior. The preprocessing follows
    `cs/src/gkr_circuits/{add_sub_family,mem_word_only}/decoder.rs`. -/
structure DecoderData where
  family : Family
  rs1 : BitVec 5
  rs2 : BitVec 5
  rd : BitVec 5
  immediate : Word
  mask : Nat

def arithmeticFields (rs1 rs2 rd : BitVec 5) (immediate : BitVec 32)
    (mask : Nat) : DecoderData :=
  if rd = 0 then ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1⟩
  else ⟨.addSub, rs1, rs2, rd, Word.ofBitVec immediate, mask⟩

/-- Match actual Sail instruction constructors. Discarded arithmetic/LW writes
    become native NOP rows; the original instruction is retained in ProgramEntry.
    Proving its successful Sail execution remains a separate obligation. -/
def decoderFields : SailRV32.instruction → Option DecoderData
  | .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD) =>
    some (arithmeticFields rs1 rs2 rd 0 1)
  | .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SUB) =>
    some (arithmeticFields rs1 rs2 rd 0 2)
  | .ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI) =>
    some (arithmeticFields rs1 0 rd (SailRV32.Functions.sign_extend (m := 32) imm) 1)
  | .UTYPE (imm, .Regidx rd, .LUI) =>
    some (arithmeticFields 0 0 rd (imm ++ BitVec.ofNat 12 0) 1)
  | .UTYPE (imm, .Regidx rd, .AUIPC) =>
    some (arithmeticFields 0 0 rd (imm ++ BitVec.ofNat 12 0) 4)
  | .LOAD (imm, .Regidx rs1, .Regidx rd, false, 4) =>
    if rd = 0 then some (arithmeticFields 0 0 0 0 1)
    else some ⟨.wordMemory, rs1, 0, rd,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 0⟩
  | .STORE (imm, .Regidx rs2, .Regidx rs1, 4) =>
    some ⟨.wordMemory, rs1, rs2, 0,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 1⟩
  | _ => none

structure ProgramEntry where
  pc : BitVec 32
  bits : BitVec 32
  instruction : SailRV32.instruction
  data : DecoderData

/-- Public bytes and the pinned upstream decoder construct the table input.
    Unreadable, undecodable or unsupported instructions fail the construction.
    Addresses and state are external inputs, independent of the witness. -/
abbrev programEntryWith (projection : SailRV32.instruction → Option DecoderData)
    (before : Reference.RiscV.Sail.State) (pc : BitVec 32) :
    Option ProgramEntry := do
  let bits ← match (Cell.ram pc).read before with
    | .ok bits _ => some bits
    | .error _ _ => none
  -- Base-ISA decoding is a pure result of the original generated Sail term.
  -- Reject effects rather than silently depending on the initial CSR state.
  let instruction ← match SailRV32.Functions.encdec_backwards bits with
    | .pure instruction => some instruction
    | .impure _ _ => none
  let data ← projection instruction
  pure ⟨pc, bits, instruction, data⟩

abbrev programImageWith (projection : SailRV32.instruction → Option DecoderData)
    (before : Reference.RiscV.Sail.State) (addresses : List (BitVec 32)) :
    Option (List ProgramEntry) := addresses.mapM (programEntryWith projection before)

abbrev programEntry := programEntryWith decoderFields
abbrev programImage := programImageWith decoderFields

/-- Rust's nine-column decoder row; omitted funct3 is represented by zero.
    This remains a modeled setup, not an extracted Rust table. -/
def ProgramEntry.query {p : Nat} (entry : ProgramEntry) : Vector (ZMod p) 9 :=
  let pc := Word.ofBitVec entry.pc
  #v[pc.lo, pc.hi, entry.data.rs1.toNat, entry.data.rs2.toNat, entry.data.rd.toNat,
    entry.data.immediate.lo, entry.data.immediate.hi, 0, entry.data.mask]

/-- A family table made from successful public-image construction. Padding is
    unnecessary for logical membership of active rows. -/
def decoderTable {p : Nat} [Fact p.Prime] (program : List ProgramEntry)
    (family : Family) : Table (ZMod p) (fields 9) := .fromStatic {
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
      exact ⟨i, equal.trans (congrArg ProgramEntry.query index).symm⟩
}

/-- The active native decoder query, using only imported column descriptors.
    The missing funct3 column is zero; selector bits are packed as in Rust. -/
def Row.decoderQuery (row : Row p) : Vector (ZMod p) 9 :=
  let c := row.decoderColumns
  #v[row.start.pc.1, row.start.pc.2, row.assignment c.rs1, row.assignment c.rs2,
    row.assignment c.rd, row.assignment c.immediate[0], row.assignment c.immediate[1],
    c.funct3.map row.assignment |>.getD 0,
    ∑ i : Fin c.flags.size, (2 ^ i.val : Nat) * row.assignment c.flags[i]]

def Row.decoderImmediate (row : Row p) : Word :=
  ⟨(row.assignment row.decoderColumns.immediate[0]).val,
    (row.assignment row.decoderColumns.immediate[1]).val⟩

/-- Logical native decoder membership. Cryptographic enforcement and Rust setup
    fidelity are retained trust boundaries; decoded instructions are derived. -/
def Decoded [Fact p.Prime] (trace : Data p) (program : List ProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (decoderTable program row.family).Contains #[] row.decoderQuery

/-- Evidence derived from public-image construction, never a premise asserting
    an expected decoder result. The original instruction remains visible. -/
structure ProgramEntry.Source (before : Reference.RiscV.Sail.State) (entry : ProgramEntry)
    (projection : SailRV32.instruction → Option DecoderData := decoderFields) : Prop where
  bytes : (Cell.ram entry.pc).read before = .ok entry.bits before
  decoded : ∀ state, Reference.Sail.run (SailRV32.Functions.encdec_backwards entry.bits) state =
    .ok entry.instruction state
  fields : projection entry.instruction = some entry.data

/-- The imported query agrees with an actual fetched/decoded public instruction
    at this row's PC, including its indices, immediate and each selector bit. -/
def Row.Fetched (row : Row p) (before : Reference.RiscV.Sail.State)
    (projection : SailRV32.instruction → Option DecoderData := decoderFields) : Prop :=
  ∃ entry : ProgramEntry, entry.Source before projection ∧ entry.data.family = row.family ∧
    row.decoderQuery = entry.query ∧ row.start.word.toBitVec = entry.pc ∧
    ∀ i : Fin row.decoderColumns.flags.size,
      row.assignment row.decoderColumns.flags[i] = if entry.data.mask.testBit i.val then 1 else 0

end Airbender.Trace
