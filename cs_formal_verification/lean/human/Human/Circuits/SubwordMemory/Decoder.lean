import Human.Circuits.SubwordMemory.Artifact
import Human.Helpers.Decoder.Program

namespace Airbender.SubwordMemory
open Arithmetic

/-- Native metadata from `mem_subword_only/decoder.rs`: store, byte and
    sign-extension bits. This selects fields; Sail supplies instruction behavior.
    Native loads to x0 are routed outside this family. -/
def decoderFields : SailRV32.instruction → Option (Trace.DecoderData Unit)
  | .LOAD (imm, .Regidx rs1, .Regidx rd, false, 1) =>
    if rd = 0 then none else some ⟨(), rs1, 0, rd,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 6, 0⟩
  | .LOAD (imm, .Regidx rs1, .Regidx rd, true, 1) =>
    if rd = 0 then none else some ⟨(), rs1, 0, rd,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 2, 0⟩
  | .LOAD (imm, .Regidx rs1, .Regidx rd, false, 2) =>
    if rd = 0 then none else some ⟨(), rs1, 0, rd,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 4, 0⟩
  | .LOAD (imm, .Regidx rs1, .Regidx rd, true, 2) =>
    if rd = 0 then none else some ⟨(), rs1, 0, rd,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 0, 0⟩
  | .STORE (imm, .Regidx rs2, .Regidx rs1, 1) =>
    some ⟨(), rs1, rs2, 0, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 3, 0⟩
  | .STORE (imm, .Regidx rs2, .Regidx rs1, 2) =>
    some ⟨(), rs1, rs2, 0, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 1, 0⟩
  | _ => none

abbrev ProgramEntry := Trace.ProgramEntry Unit
abbrev programImage := Trace.programImageRunWith decoderFields
abbrev decoderTable {p : Nat} [Fact p.Prime] (program : List ProgramEntry) :=
  Trace.decoderTable (p := p) program ()
abbrev decoderQuery {p : Nat} (w : Nat → ZMod p) :=
  Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w

/-- Source evidence comes from the public bytes and original Sail decoder.
    It identifies fields and selectors, without supplying native reads/results. -/
def Fetched {p : Nat} (w : Nat → ZMod p) (before : Reference.RiscV.Sail.State) : Prop :=
  ∃ entry : ProgramEntry, entry.SourceWith before decoderFields ∧
    decoderQuery w = entry.query ∧
    ∀ i : Fin 3,
      w importedConstraintsDecoderColumns.flags[i] = if entry.data.mask.testBit i.val then 1 else 0

end Airbender.SubwordMemory
