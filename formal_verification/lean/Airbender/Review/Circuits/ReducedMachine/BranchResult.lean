import Airbender.Review.Circuits.ReducedMachine.BranchDecoder

namespace Airbender.ReducedMachine.Native
open Arithmetic
set_option autoImplicit false

/-- Actual native numerical branch observations. These words are native reads,
    not yet original pre-row Sail GPR observations or retained clause execution. -/
def BranchNumericalEffects (w : Nat → ZMod mersenne31Modulus) : Prop :=
  w 67 = 0 ∧
  w 66 = (if branchCondition (w 11).val (sourceWord w) (operandWord w) then 1 else 0) ∧
  (branchTargetWord w).Bounded ∧
  (branchTargetWord w).toBitVec = (initialPCWord w).toBitVec + (branchOffsetWord w).toBitVec ∧
  (finalPCWord w).Bounded ∧
  (finalPCWord w).toBitVec = (if branchCondition (w 11).val (sourceWord w) (operandWord w) then
    (initialPCWord w).toBitVec + (branchOffsetWord w).toBitVec else (initialPCWord w).toBitVec + 4) ∧
  (finalPCWord w).toBitVec.toNat % 4 = 0

end Airbender.ReducedMachine.Native
