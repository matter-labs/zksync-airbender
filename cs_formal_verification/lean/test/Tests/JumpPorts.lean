import Slop.JumpBranchSlt.PortReads
import Tests.Jump

namespace Tests.JumpPorts
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 32768

-- The source and destination are both x1. Its old value is five, whereas
-- the link written by JALR is four. Native memory must retain that old read.
private def assignment (i : Nat) : ZMod babyBearModulus :=
  if i = 28 then 5 else Tests.Jump.row true false false i

private theorem constraints :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment)
      JumpBranchSlt.importedConstraints :=
  (JumpBranchSlt.Completeness.imported_congr (by decide)).mp (Tests.Jump.satisfies true false false)

end Tests.JumpPorts
