import Airbender.Review.Circuits.JumpBranchSlt.Model
import Airbender.Review.Helpers.Core.Word

namespace Airbender.JumpBranchSlt
open Arithmetic

/-- The six original branch conditions, indexed by their native funct3.
    Public original decoding excludes the other tags. Sail execution is separate. -/
def branchCondition (tag : Nat) (left right : Word) : Bool :=
  match tag with
  | 0 => decide (left.toBitVec = right.toBitVec)
  | 1 => decide (left.toBitVec ≠ right.toBitVec)
  | 4 => decide (left.toBitVec.toInt < right.toBitVec.toInt)
  | 5 => decide (¬left.toBitVec.toInt < right.toBitVec.toInt)
  | 6 => decide (left.value < right.value)
  | 7 => decide (¬left.value < right.value)
  | _ => false

end Airbender.JumpBranchSlt
