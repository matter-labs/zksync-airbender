import Human.Circuits.AddSub.Modular
import Human.Helpers.Core.BabyBearPrime
import Slop.AddSub.Selectors
import Slop.JumpBranchSlt.Branch
import Slop.JumpBranchSlt.Jump
import Slop.MulDiv.Values
import Slop.ShiftBinop.Ports
import Slop.SubwordMemory.Values
import Slop.Trace.Family.Values
import Slop.Trace.Pooled
import Slop.Trace.RowContext

namespace Tests.Discarded
open Airbender
open Airbender.Reference.RiscV

private def row : Nat → ZMod babyBearModulus
  | 0 => 65532
  | 4 | 10 | 20 => 1
  | 21 => 4
  | _ => 0

private theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row) AddSub.importedConstraints := by
  simp [AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, row]
  repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains; decide)

end Tests.Discarded
