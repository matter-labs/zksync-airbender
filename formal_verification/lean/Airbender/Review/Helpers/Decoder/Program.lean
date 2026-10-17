import Airbender.Review.Helpers.Memory.InitialImage

namespace Airbender.Trace
open Arithmetic

/-- Native decoder fields, not instruction behavior. The preprocessing follows
    the pinned v2 ADD/SUB decoder and bytecode preprocessor. -/
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
    (mask : Nat) (funct3 : Nat := 0) : DecoderData :=
  ⟨.addSub, rs1, rs2, rd, Word.ofBitVec immediate, mask, funct3⟩

/-- Native v2 metadata for the selected original Sail arithmetic constructors.
    Keep original x0 opcodes/operands and raw funct3 bits (including U-type bits).
    Unsupported instructions fail this selected-profile constructor. -/
def decoderFields : SailRV32.instruction → Option DecoderData
  | .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD) =>
    some (arithmeticFields rs1 rs2 rd 0 1)
  | .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SUB) =>
    some (arithmeticFields rs1 rs2 rd 0 4)
  | .ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI) =>
    some (arithmeticFields rs1 0 rd (SailRV32.Functions.sign_extend (m := 32) imm) 2)
  | .UTYPE (imm, .Regidx rd, .LUI) =>
    some (arithmeticFields 0 0 rd (imm ++ BitVec.ofNat 12 0) 8 (imm.toNat % 8))
  | .UTYPE (imm, .Regidx rd, .AUIPC) =>
    some (arithmeticFields 0 0 rd (imm ++ BitVec.ofNat 12 0) 16 (imm.toNat % 8))
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
abbrev programEntryWith {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (before : Reference.RiscV.Sail.State) (pc : BitVec 32) :
    Option (ProgramEntry Kind) := do
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

/-- Construct entries for the public `addresses` using pure Sail decoding.
    A missing byte, effectful decoder or unsupported instruction makes it fail. -/
abbrev programImageWith {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (before : Reference.RiscV.Sail.State) (addresses : List (BitVec 32)) :
    Option (List (ProgramEntry Kind)) := addresses.mapM (programEntryWith projection before)

abbrev programEntry := programEntryWith decoderFields
abbrev programImage := programImageWith decoderFields

/-- The native v2 ten-column row, including the separately encoded zero flag. -/
def ProgramEntry.query {Kind : Type} {p : Nat} (entry : ProgramEntry Kind) : Vector (ZMod p) 10 :=
  let pc := Word.ofBitVec entry.pc
  #v[pc.lo, pc.hi, entry.data.rs1.toNat, entry.data.rs2.toNat, entry.data.rd.toNat,
    if entry.data.rd = 0 then 1 else 0, entry.data.immediate.lo, entry.data.immediate.hi,
    entry.data.funct3, entry.data.mask]

def Row.decoderImmediate {Kind : Type} [CircuitLayout Kind] (row : Row p Kind) : Word :=
  ⟨(row.assignment row.decoderColumns.immediate[0]).val,
    (row.assignment row.decoderColumns.immediate[1]).val⟩

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

abbrev ProgramEntry.Source (before : Reference.RiscV.Sail.State) (entry : ProgramEntry)
    (projection : SailRV32.instruction → Option DecoderData := decoderFields) :=
  entry.SourceWith before projection

end Airbender.Trace
