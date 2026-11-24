module
public import Human.Helpers.Core.BabyBearPrime
public import Proven.AddSub.Selectors
public import Proven.JumpBranchSlt.Branch
public import Proven.JumpBranchSlt.Jump
public import Proven.MulDiv.Values
public import Proven.SubwordMemory.Values
public import Proven.Trace.RowContext

@[expose] public section

namespace Tests.NonDeterminism
open Airbender
open Airbender.Reference.RiscV
set_option warningAsError true

private def row : Nat → ZMod babyBearModulus
  | 0 => 65535
  | 4 | 10 | 20 => 1
  | 19 => 3
  | 21 => 4
  | _ => 0

private theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row) AddSub.importedConstraints := by
  simp [AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, row]
  repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains
       decide)

def readRow : Nat → ZMod babyBearModulus
  | 0 => 65535
  | 4 | 7 | 18 | 20 => 1
  | 19 => 3
  | 21 => 4
  | 33 => 22136
  | 34 => 4660
  | _ => 0

theorem read_constraints :
    FlatOperation.ConstraintsHoldFlat (Verification.environment readRow) AddSub.importedConstraints := by
  simp [AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, readRow]
  repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains; decide)

end Tests.NonDeterminism
