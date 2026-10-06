import Airbender.Review.AddSub.Theorems
import Airbender.Proofs.Constraints

namespace Tests.Modular
open Airbender
open Airbender.AddSub

-- ADDMOD(p-1, 1) = 0, with an actual satisfying local assignment at the reduction boundary.
private def row : Nat → ZMod babyBearModulus
  | 4 | 13 | 39 | 40 => 1
  | 19 | 21 => 4
  | 26 => 30720
  | 29 => 1
  | 37 => 65535
  | 38 => 34815
  | 41 => 1069547521
  | _ => 0

private def input : AddSub.Modular.Input :=
  ⟨.add, BitVec.ofNat 32 (babyBearModulus - 1), 1, 0⟩

private theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row) importedConstraints := by
  norm_num [importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, row, babyBearModulus]
  repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, row, Arithmetic.limbBase,
         ZMod.val_ofNat, babyBearModulus])
    | decide

example : AddSub.Modular.spec input ⟨0, 0⟩ := by
  apply AddSub.Modular.soundness input ⟨0, 0⟩ row
  refine ⟨?_, satisfies, ?_⟩
  · constructor
    · rfl
    · intro k lower upper
      interval_cases k <;> rfl
  · constructor
    · norm_num [row, input, babyBearModulus, BitVec.toNat_ofNat]
    · rfl
    · simp [input]
    · rfl
    · rfl

end Tests.Modular
