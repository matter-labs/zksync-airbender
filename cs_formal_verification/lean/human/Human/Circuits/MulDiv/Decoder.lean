import Human.Helpers.Decoder.Program
import Human.Circuits.MulDiv.Artifact

namespace Airbender.MulDiv
open Arithmetic

/-- Native metadata from `cs/src/gkr_circuits/mul_div/decoder.rs`.
    x0 destinations are routed to ADD/SUB preprocessing. This projection
    selects fields only; instruction behavior is the original Sail clause. -/
def decoderFields : SailRV32.instruction → Option (Trace.DecoderData Unit)
  | .MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, ⟨.Low, .Signed, .Signed⟩) =>
    if rd = 0 then none else some ⟨(), rs1, rs2, rd, ⟨0, 0⟩, 1, 0⟩
  | .MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, ⟨.High, .Unsigned, .Unsigned⟩) =>
    if rd = 0 then none else some ⟨(), rs1, rs2, rd, ⟨0, 0⟩, 2, 0⟩
  | .DIV (.Regidx rs2, .Regidx rs1, .Regidx rd, true) =>
    if rd = 0 then none else some ⟨(), rs1, rs2, rd, ⟨0, 0⟩, 4, 0⟩
  | .REM (.Regidx rs2, .Regidx rs1, .Regidx rd, true) =>
    if rd = 0 then none else some ⟨(), rs1, rs2, rd, ⟨0, 0⟩, 8, 0⟩
  | _ => none

abbrev ProgramEntry := Trace.ProgramEntry Unit
noncomputable abbrev programImage := Trace.programImageWith decoderFields
abbrev decoderTable {p : Nat} [Fact p.Prime] (program : List ProgramEntry) :=
  Trace.decoderTable (p := p) program ()
abbrev decoderQuery {p : Nat} (w : Nat → ZMod p) :=
  Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w

/-- A public instruction fetched and decoded by Sail, bound to every native
    query column and selector. Successful register reads are not presumed. -/
def Fetched {p : Nat} (w : Nat → ZMod p) (before : Reference.RiscV.Sail.State) : Prop :=
  ∃ entry : ProgramEntry, entry.SourceWith before decoderFields ∧
    decoderQuery w = entry.query ∧
    ∀ i : Fin 4,
      w importedConstraintsDecoderColumns.flags[i] = if entry.data.mask.testBit i.val then 1 else 0

end Airbender.MulDiv
