module
public import Human.Compiler.NativeSetups.AddSub
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

/-- The column formulas, in native column order. -/
def formulas : List (Nat → Nat) := [column0, column1, column2, column3, column4, column5, column6, column7]

/-- Rows from 4 (the later decoder slots and the padding rows): the sentinel `p - 1` in every field. -/
theorem row_after (n : Nat) (low : 4 ≤ n) :
    formulas.map (· n) = [sentinel, sentinel, sentinel, sentinel, sentinel, sentinel, sentinel, sentinel] := by
  simp (disch := omega) only [formulas, List.map_cons, List.map_nil, column0, column1, column2, column3, column4,
    column5, column6, column7, byRow, nat_beq, pick_false]

end Airbender.Compiler.NativeFixedRows.AddSubSetupProofs
