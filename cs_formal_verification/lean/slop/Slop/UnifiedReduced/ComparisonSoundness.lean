import Slop.UnifiedReduced.ControlContext
import Slop.JumpBranchSlt.PC
import Slop.JumpBranchSlt.Signed

namespace Airbender.UnifiedReduced.Control.Comparison.Proofs
open Arithmetic Reference.RiscV Trace Trace.Proofs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 2800000

private def immediate (op : JumpBranchSlt.Comparison.Opcode) : Bool :=
  match op with | .slti | .sltiu => true | _ => false

end Airbender.UnifiedReduced.Control.Comparison.Proofs
