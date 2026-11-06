import Human.Helpers.Memory.InitialImage
import Human.Helpers.Core.Configuration

-- The full Sail model compiles its decoder (`encdec_backwards`) as noncomputable (sail/regen.sh,
-- `proof` variant): these definitions are specifications, read by proofs, never executed.
noncomputable section

namespace Airbender.Trace
open Arithmetic

/-- Native decoder fields, not instruction behavior. The preprocessing follows
    `cs/src/gkr_circuits/{add_sub_family,mem_word_only}/decoder.rs`. -/
structure DecoderData (Kind : Type := Family) where
  /-- Circuit family selected by native instruction preprocessing. -/
  family : Kind
  rs1 : BitVec 5
  rs2 : BitVec 5
  rd : BitVec 5
  /-- Native immediate limbs, including sign extension or other family preprocessing. -/
  immediate : Word
  /-- Packed selector bits used by the native decoder lookup. -/
  mask : Nat
  /-- Family-specific operation tag; zero when no such column is used. -/
  funct3 : Nat := 0

def arithmeticFields (rs1 rs2 rd : BitVec 5) (immediate : BitVec 32)
    (mask : Nat) : DecoderData :=
  if rd = 0 then ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩
  else ⟨.addSub, rs1, rs2, rd, Word.ofBitVec immediate, mask, 0⟩

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
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 0, 0⟩
  | .STORE (imm, .Regidx rs2, .Regidx rs1, 4) =>
    some ⟨.wordMemory, rs1, rs2, 0,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 1, 0⟩
  | _ => none

/-- One public instruction entry: `pc` locates its four `bits` bytes,
    `instruction` is the original Sail decoder result, and `data` is its native
    circuit metadata. Public-image construction binds these fields together;
    the record alone supplies no correctness guarantee. -/
structure ProgramEntry (Kind : Type := Family) where
  pc : BitVec 32
  bits : BitVec 32
  instruction : SailRV32.instruction
  data : DecoderData Kind

/-- Change only the circuit registry tag; native metadata and Sail instruction
    are retained verbatim. -/
def DecoderData.mapFamily {Kind Target : Type} (f : Kind → Target)
    (data : DecoderData Kind) : DecoderData Target :=
  ⟨f data.family, data.rs1, data.rs2, data.rd, data.immediate, data.mask, data.funct3⟩

def ProgramEntry.mapFamily {Kind Target : Type} (f : Kind → Target)
    (entry : ProgramEntry Kind) : ProgramEntry Target :=
  ⟨entry.pc, entry.bits, entry.instruction, entry.data.mapFamily f⟩

/-- Public bytes and the pinned upstream decoder construct the table input.
    Unreadable, undecodable or unsupported instructions fail the construction.
    Addresses and state are external inputs, independent of the witness. -/
noncomputable abbrev programEntryWith {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (before : Reference.RiscV.Sail.State) (pc : BitVec 32) :
    Option (ProgramEntry Kind) := do
  let bits ← match (Cell.ram pc).read before with
    | .ok bits _ => some bits
    | .error _ _ => none
  -- The original Sail decoder on the Airbender configuration: a pure function of the word.
  let instruction ← Reference.RiscV.Sail.decodeOnReset bits
  let data ← projection instruction
  pure ⟨pc, bits, instruction, data⟩

/-- Construct entries for the public `addresses`. A missing byte, undecodable or unsupported
    instruction makes it fail. -/
noncomputable abbrev programImageWith {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (before : Reference.RiscV.Sail.State) (addresses : List (BitVec 32)) :
    Option (List (ProgramEntry Kind)) := addresses.mapM (programEntryWith projection before)

noncomputable abbrev programEntry := programEntryWith decoderFields
noncomputable abbrev programImage := programImageWith decoderFields

/-- Rust's nine-column decoder row; omitted funct3 is represented by zero.
    This remains a modeled setup, not an extracted Rust table. -/
def ProgramEntry.query {Kind : Type} {p : Nat} (entry : ProgramEntry Kind) : Vector (ZMod p) 9 :=
  let pc := Word.ofBitVec entry.pc
  #v[pc.lo, pc.hi, entry.data.rs1.toNat, entry.data.rs2.toNat, entry.data.rd.toNat,
    entry.data.immediate.lo, entry.data.immediate.hi, entry.data.funct3, entry.data.mask]

/-- A family table made from successful public-image construction. Padding is
    unnecessary for logical membership of active rows. -/
def decoderTable {Kind : Type} [DecidableEq Kind] {p : Nat} [Fact p.Prime]
    (program : List (ProgramEntry Kind)) (family : Kind) : Table (ZMod p) (fields 9) := .fromStatic {
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
def nativeDecoderQuery {p : Nat} (columns : TraceColumns) (c : DecoderColumns)
    (w : Nat → ZMod p) : Vector (ZMod p) 9 :=
  #v[w columns.initialPC[0], w columns.initialPC[1], w c.rs1, w c.rs2,
    w c.rd, w c.immediate[0], w c.immediate[1], c.funct3.map w |>.getD 0,
    ∑ i : Fin c.flags.size, (2 ^ i.val : Nat) * w c.flags[i]]

noncomputable abbrev Row.decoderQuery {Kind : Type} [CircuitLayout Kind] (row : Row p Kind) : Vector (ZMod p) 9 :=
  nativeDecoderQuery row.columns row.decoderColumns row.assignment

def Row.decoderImmediate {Kind : Type} [CircuitLayout Kind] (row : Row p Kind) : Word :=
  ⟨(row.assignment row.decoderColumns.immediate[0]).val,
    (row.assignment row.decoderColumns.immediate[1]).val⟩

/-- Each native row's imported decoder query belongs to its family's modeled
    program table. `program` must separately be bound to public bytes by image
    construction. Together these let the proofs recover its original Sail
    instruction and selector choices. Lookup-argument enforcement remains external. -/
def Decoded [Fact p.Prime] (trace : Data p) (program : List ProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (decoderTable program row.family).Contains #[] row.decoderQuery

/-- Record how `entry` comes from the Sail state `before`: read its actual
    bytes, run original Sail decoding, then project native metadata. Public-image
    construction proves this evidence for its entries; execution uses it again
    after showing that writes preserve the public code/configuration. -/
structure ProgramEntry.SourceWith {Kind : Type} (before : Reference.RiscV.Sail.State)
    (entry : ProgramEntry Kind) (projection : SailRV32.instruction → Option (DecoderData Kind)) : Prop where
  /-- The entry's encoding is read from the actual public byte memory. -/
  bytes : (Cell.ram entry.pc).read before = .ok entry.bits before
  /-- The pinned Sail decoder returns this original instruction without changing the state. -/
  decoded : Reference.Sail.run (SailRV32.Functions.encdec_backwards entry.bits) before =
    .ok entry.instruction before
  /-- The native metadata projection of that instruction matches the entry. -/
  fields : projection entry.instruction = some entry.data

noncomputable abbrev ProgramEntry.Source (before : Reference.RiscV.Sail.State) (entry : ProgramEntry)
    (projection : SailRV32.instruction → Option DecoderData := decoderFields) :=
  entry.SourceWith before projection

/-- The imported query agrees with an actual fetched/decoded public instruction
    at this row's PC, including its indices, immediate and each selector bit. -/
def Row.Fetched (row : Row p) (before : Reference.RiscV.Sail.State)
    (projection : SailRV32.instruction → Option DecoderData := decoderFields) : Prop :=
  ∃ entry : ProgramEntry, entry.Source before projection ∧ entry.data.family = row.family ∧
    row.decoderQuery = entry.query ∧ row.start.word.toBitVec = entry.pc ∧
    ∀ i : Fin row.decoderColumns.flags.size,
      row.assignment row.decoderColumns.flags[i] = if entry.data.mask.testBit i.val then 1 else 0

end Airbender.Trace
