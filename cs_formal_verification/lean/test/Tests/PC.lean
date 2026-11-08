module
public import Human.Helpers.Core.BabyBearPrime
public import Slop.AddSub.Selectors
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump
public import Slop.MulDiv.Values
public import Slop.ShiftBinop.Ports
public import Slop.SubwordMemory.Values
public import Slop.Trace.Family.Values
public import Slop.Trace.Pooled
public import Slop.Trace.RowContext

@[expose] public section

namespace Tests.PC
open Airbender
open Airbender.Reference.RiscV

-- Active ADD x1,x1,x1, with a PC carry across the 16-bit boundary.
def row (i : Nat) : ZMod babyBearModulus :=
  if i = 0 then 65535 else if i = 4 ∨ i = 7 ∨ i = 10 ∨ i = 20 then 1
  else if i = 19 then 3 else if i = 21 then 4
  else if i = 25 ∨ i = 29 then 123 else if i = 41 then 1447027789
  else if i = 33 then 246 else 0

theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row) AddSub.importedConstraints := by
  simp [AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, row]
  repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains
       decide)

example : (⟨3, 1⟩ : Arithmetic.Word).value = (⟨65535, 0⟩ : Arithmetic.Word).value + 4 :=
  (AddSub.Proofs.pc_successor (by decide) (by decide) satisfies
    (by constructor <;> decide)
    ⟨by decide, by decide⟩).1

end Tests.PC
