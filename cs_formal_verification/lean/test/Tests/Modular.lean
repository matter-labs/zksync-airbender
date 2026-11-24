module
public import Proven.Constraints
public import Human.Helpers.Core.BabyBearPrime
public import Proven.AddSub.Selectors
public import Proven.JumpBranchSlt.Branch
public import Proven.JumpBranchSlt.Jump
public import Proven.MulDiv.Values
public import Proven.SubwordMemory.Values
public import Proven.Trace.RowContext

@[expose] public section

namespace Tests.Modular
open Airbender
open Airbender.AddSub
open Airbender.Reference.RiscV

-- ADDMOD(p-1, 1) = 0, with an actual satisfying assignment at the reduction boundary.
private def row : Nat → ZMod babyBearModulus
  | 4 | 13 | 39 | 40 => 1
  | 7 => 3
  | 19 | 21 => 4
  | 26 => 30720
  | 29 => 1
  | 37 => 65535
  | 38 => 34815
  | 41 => 1069547521
  | _ => 0

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

-- FMAMOD x1,x1,x2 reads x1 before overwriting it: 11 + 11*3/R mod p.
private def fmaRow : Nat → ZMod babyBearModulus
  | 4 | 7 | 16 | 40 => 1
  | 19 | 21 => 4
  | 25 | 31 => 11
  | 29 => 3
  | 33 => 65532
  | 34 => 14399
  | 37 => 65531
  | 38 => 49215
  | 41 => 943718396
  | _ => 0

private theorem fmaSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment fmaRow) importedConstraints := by
  simp [importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, fmaRow]
  repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains; decide)

private def zeroRow : Nat → ZMod babyBearModulus
  | 4 | 10 => 1
  | 19 | 21 => 4
  | _ => 0

private theorem zeroSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment zeroRow) importedConstraints := by
  simp [importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, zeroRow]
  repeat' apply And.intro
  all_goals
    apply Verification.range16_contains
    decide

end Tests.Modular
