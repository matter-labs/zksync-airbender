module
public import Human.Compiler.NativeSetups.Claims
public import Proven.Setup.Native.Common

@[expose] public section

/- Column formulas of the native add/sub setup, in the form that the kernel evaluates fast: the decoder rows of the
   setup fixture program (slots 0, 1 and 3), the sentinel `p - 1` in every other row. -/

namespace Airbender.Compiler.NativeFixedRows.AddSubSetupProofs
open Airbender.Import.Setup.Scan Airbender.Compiler.NativeSetups.Proofs

/-- Field values `first`, `second` and `fourth` of decoder slots 0, 1 and 3; the sentinel in every other row. -/
def byRow (n first second fourth : Nat) : Nat :=
  pick (Nat.beq n 0) first <| pick (Nat.beq n 1) second <| pick (Nat.beq n 3) fourth sentinel

def column0 (n : Nat) : Nat := byRow n 0 4 12
def column1 (n : Nat) : Nat := byRow n 0 0 0
def column2 (n : Nat) : Nat := byRow n 0 1 3
def column3 (n : Nat) : Nat := byRow n 0 0 7
def column4 (n : Nat) : Nat := byRow n 0 1 3
def column5 (n : Nat) : Nat := byRow n 0 4 0
def column6 (n : Nat) : Nat := byRow n 0 0 0
def column7 (n : Nat) : Nat := byRow n 1 1 1

/-- The claimed rows, as the claim states them. -/
def claimedRow (n : Nat) : Vector Int 8 :=
  if n < 1048576 then addSubFixtureDecoderRow n else Vector.replicate 8 ((babyBearModulus - 1 : Nat) : Int)

-- One simp set serves every column; each column uses a part of it.
set_option linter.unusedSimpArgs false in
theorem column_eq (n : Nat) (c : Fin 8) :
    (claimedRow n)[c] = (![column0, column1, column2, column3, column4, column5, column6, column7] c n : Int) := by
  by_cases zero : n = 0
  · subst zero; fin_cases c <;> rfl
  by_cases one : n = 1
  · subst one; fin_cases c <;> rfl
  by_cases three : n = 3
  · subst three; fin_cases c <;> rfl
  fin_cases c <;>
  simp (disch := omega) only [claimedRow, addSubFixtureDecoderRow, zero, one, three, ↓reduceIte, Fin.zero_eta,
    Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, column0, column1, column2, column3, column4, column5, column6,
    column7, byRow, nat_beq, pick_false, Vector.getElem_replicate] <;>
  split_ifs <;> simp [babyBearModulus]

end Airbender.Compiler.NativeFixedRows.AddSubSetupProofs
