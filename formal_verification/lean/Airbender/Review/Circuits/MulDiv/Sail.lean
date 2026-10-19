import Airbender.Review.Circuits.MulDiv.Decoder
import Airbender.Review.Helpers.Core.Sail

namespace Airbender.MulDiv

/-- Original pinned Sail constructors, retaining unsigned flags and x0 writes. -/
def instruction (operation : Operation) (rs1 rs2 rd : BitVec 5) : SailRV32.instruction :=
  match operation with
  | .mul => .MUL (.Regidx rs2,.Regidx rs1,.Regidx rd,⟨.Low,.Signed,.Signed⟩)
  | .mulhu => .MUL (.Regidx rs2,.Regidx rs1,.Regidx rd,⟨.High,.Unsigned,.Unsigned⟩)
  | .divu => .DIV (.Regidx rs2,.Regidx rs1,.Regidx rd,true)
  | .remu => .REM (.Regidx rs2,.Regidx rs1,.Regidx rd,true)

/-- Dispatch only; instruction behavior comes from the original generated clauses. -/
def clause (operation : Operation) (rs1 rs2 rd : BitVec 5) : SailRV32.SailM SailRV32.ExecutionResult :=
  match operation with
  | .mul => SailRV32.Functions.execute_MUL (.Regidx rs2) (.Regidx rs1) (.Regidx rd) ⟨.Low,.Signed,.Signed⟩
  | .mulhu => SailRV32.Functions.execute_MUL (.Regidx rs2) (.Regidx rs1) (.Regidx rd) ⟨.High,.Unsigned,.Unsigned⟩
  | .divu => SailRV32.Functions.execute_DIV (.Regidx rs2) (.Regidx rs1) (.Regidx rd) true
  | .remu => SailRV32.Functions.execute_REM (.Regidx rs2) (.Regidx rs1) (.Regidx rd) true

end Airbender.MulDiv
