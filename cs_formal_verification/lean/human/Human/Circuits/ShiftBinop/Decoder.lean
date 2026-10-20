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

/-- Actual Sail constructors projected to the imported native decoder query.
    Discarded destinations belong to ADD/SUB; illegal RV32 shift payloads fail. -/
def decoderFields : SailRV32.instruction → Option (Trace.DecoderData Unit)
  | .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .XOR) => instructionFields .xor rs1 rs2 rd ⟨0, 0⟩
  | .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .OR) => instructionFields .or rs1 rs2 rd ⟨0, 0⟩
  | .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .AND) => instructionFields .and rs1 rs2 rd ⟨0, 0⟩
  | .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLL) => instructionFields .sll rs1 rs2 rd ⟨0, 0⟩
  | .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SRL) => instructionFields .srl rs1 rs2 rd ⟨0, 0⟩
  | .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SRA) => instructionFields .sra rs1 rs2 rd ⟨0, 0⟩
  | .ITYPE (imm, .Regidx rs1, .Regidx rd, .XORI) =>
    instructionFields .xor rs1 0 rd (binaryImmediate (SailRV32.Functions.sign_extend (m := 32) imm))
  | .ITYPE (imm, .Regidx rs1, .Regidx rd, .ORI) =>
    instructionFields .or rs1 0 rd (binaryImmediate (SailRV32.Functions.sign_extend (m := 32) imm))
  | .ITYPE (imm, .Regidx rs1, .Regidx rd, .ANDI) =>
    instructionFields .and rs1 0 rd (binaryImmediate (SailRV32.Functions.sign_extend (m := 32) imm))
  | .SHIFTIOP (amount, .Regidx rs1, .Regidx rd, .SLLI) =>
    if amount.toNat < 32 then instructionFields .sll rs1 0 rd ⟨amount.toNat, 0⟩ else none
  | .SHIFTIOP (amount, .Regidx rs1, .Regidx rd, .SRLI) =>
    if amount.toNat < 32 then instructionFields .srl rs1 0 rd ⟨amount.toNat, 0⟩ else none
  | .SHIFTIOP (amount, .Regidx rs1, .Regidx rd, .SRAI) =>
    if amount.toNat < 32 then instructionFields .sra rs1 0 rd ⟨amount.toNat, 0⟩ else none
  | .REV8 (.Regidx rs1, .Regidx rd) => instructionFields .rev8 rs1 0 rd ⟨0, 0⟩
  | _ => none

abbrev ProgramEntry := Trace.ProgramEntry Unit
abbrev programImage := Trace.programImageRunWith decoderFields
abbrev decoderTable {p : Nat} [Fact p.Prime] (program : List ProgramEntry) :=
  Trace.decoderTable (p := p) program ()
abbrev decoderQuery {p : Nat} (w : Nat → ZMod p) :=
  Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w

/-- Source evidence is derived from the public constructor and membership.
    It supplies no native read or expected instruction result. -/
def Fetched {p : Nat} (w : Nat → ZMod p) (before : Reference.RiscV.Sail.State) : Prop :=
  ∃ entry : ProgramEntry, entry.SourceWith before decoderFields ∧
    decoderQuery w = entry.query ∧
    ∀ i : Fin 2,
      w importedConstraintsDecoderColumns.flags[i] = if entry.data.mask.testBit i.val then 1 else 0

end Airbender.ShiftBinop
