import Human.Helpers.Decoder.RVProgram
import Human.Circuits.MulDiv.Artifact

namespace Airbender.MulDiv

/-- Native metadata from `cs/src/gkr_circuits/mul_div/decoder.rs`, on `RV.Instr` (as `decoderFields`). x0
    destinations are routed to ADD/SUB preprocessing. -/
def rvDecoderFields : RV.Instr → Option (Trace.DecoderData Unit)
  | .op .mul rd rs1 rs2 => if rd = 0 then none else some ⟨(), rs1, rs2, rd, ⟨0, 0⟩, 1, 0⟩
  | .op .mulhu rd rs1 rs2 => if rd = 0 then none else some ⟨(), rs1, rs2, rd, ⟨0, 0⟩, 2, 0⟩
  | .op .divu rd rs1 rs2 => if rd = 0 then none else some ⟨(), rs1, rs2, rd, ⟨0, 0⟩, 4, 0⟩
  | .op .remu rd rs1 rs2 => if rd = 0 then none else some ⟨(), rs1, rs2, rd, ⟨0, 0⟩, 8, 0⟩
  | _ => none

abbrev RVProgramEntry := Trace.RVProgramEntry Unit
abbrev rvDecoderTable {p : Nat} [Fact p.Prime] (program : List RVProgramEntry) :=
  Trace.rvDecoderTable (p := p) program ()

end Airbender.MulDiv
