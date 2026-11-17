module
public import Human.Compiler.NativeFixedRows
public import Proven.Setup.Native.Common

@[expose] public section

/- Column formulas of the native multiply/divide setup, in the form that the kernel evaluates fast, and their
   agreement with the reviewed fixed rows `NativeFixedRows.mulDiv`. Rows from 270336 hold the decoder table of the
   setup fixture program (no multiply or divide instruction: every payload field is the sentinel `p - 1`, the tag is
   46), then zero padding. -/

namespace Airbender.Compiler.NativeFixedRows.MulDivSetupProofs
open Airbender.Import.Setup.Scan Airbender.Compiler.NativeSetups.Proofs

/-- The value of a row in each region: tables 1, 10, 26 and 41, the decoder rows, then zero padding. -/
def byRegion (n : Nat) (table1 table10 table26 table41 : Nat → Nat) (decoder : Nat) : Nat :=
  pick (Nat.blt n 131072) (table1 n) <|
  pick (Nat.blt n 196608) (table10 (Nat.sub n 131072)) <|
  pick (Nat.blt n 204800) (table26 (Nat.sub n 196608)) <|
  pick (Nat.blt n 270336) (table41 (Nat.sub n 204800)) <|
  pick (Nat.blt n 1318912) decoder 0

def column0 (n : Nat) : Nat :=
  byRegion n (fun key => key) (fun key => Nat.div key 256) (fun key => key) (fun key => key) sentinel
def column1 (n : Nat) : Nat :=
  byRegion n (fun key => pick (Nat.beq key 0) 1 0) (fun key => Nat.mod key 256) (fun _ => 0)
    (fun key => Nat.mod key 256) sentinel
def column2 (n : Nat) : Nat := byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) sentinel
def column3 (n : Nat) : Nat := byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) sentinel
def column4 (n : Nat) : Nat := byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) sentinel
def column5 (n : Nat) : Nat := byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) sentinel
def column6 (n : Nat) : Nat := byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) sentinel
def column7 (n : Nat) : Nat := byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) sentinel
def column8 (n : Nat) : Nat := byRegion n (fun _ => 1) (fun _ => 10) (fun _ => 26) (fun _ => 41) 46

/-- The reviewed fixed rows, as integers. -/
def fixedRow (index : Fin 270336) : Vector Int 9 := (mulDiv index).map (fun n : Nat => (n : Int))

set_option maxRecDepth 100000 in
theorem column_eq (n : Nat) (bound : n < 270336) :
    (fixedRow ⟨n, bound⟩)[0] = column0 n ∧ (fixedRow ⟨n, bound⟩)[1] = column1 n ∧
    (fixedRow ⟨n, bound⟩)[2] = column2 n ∧ (fixedRow ⟨n, bound⟩)[3] = column3 n ∧
    (fixedRow ⟨n, bound⟩)[4] = column4 n ∧ (fixedRow ⟨n, bound⟩)[5] = column5 n ∧
    (fixedRow ⟨n, bound⟩)[6] = column6 n ∧ (fixedRow ⟨n, bound⟩)[7] = column7 n ∧
    (fixedRow ⟨n, bound⟩)[8] = column8 n := by
  simp only [fixedRow, mulDiv]
  split_ifs
  all_goals simp (disch := omega) only [column0, column1, column2, column3, column4, column5, column6, column7,
    column8, byRegion, nat_blt, nat_beq, pick_true, pick_false, nat_sub, nat_div, nat_mod, Vector.getElem_map,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, and_self]

/-- Rows from 270336: the decoder rows of the setup fixture, then zero padding. -/
theorem column_after (n : Nat) (low : 270336 ≤ n) (c : Fin 9) :
    ((if n < 1318912 then (Vector.replicate 8 ((babyBearModulus - 1 : Nat) : Int)).push 46
      else Vector.replicate 9 0 : Vector Int 9))[c] =
      (![column0, column1, column2, column3, column4, column5, column6, column7, column8] c n : Int) := by
  fin_cases c <;>
  simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
  simp (disch := omega) only [column0, column1, column2, column3, column4, column5, column6, column7, column8,
    byRegion, nat_blt, pick_false] <;>
  split_ifs <;> simp_all [babyBearModulus]

end Airbender.Compiler.NativeFixedRows.MulDivSetupProofs
