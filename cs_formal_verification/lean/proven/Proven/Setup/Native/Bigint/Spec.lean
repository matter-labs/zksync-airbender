module
public import Human.Circuits.Bigint.Tables.Setup
public import Proven.Setup.Scan

@[expose] public section

/- Column formulas of the native bigint setup, in the form that the kernel evaluates fast, and their agreement with
   the reviewed row formula `Bigint.setupRow` (zero from row 1390592). -/

namespace Airbender.Bigint.SetupProofs
open Airbender.Import.Setup.Scan

/-- The reviewed rows with zero padding, as integers. -/
def paddedRow (index : Nat) : Vector Int 3 :=
  if bound : index < 1390592 then
    let row := setupRow ⟨index, bound⟩
    #v[(row.1 : Int), (row.2.1 : Int), (row.2.2 : Int)]
  else #v[0, 0, 0]

/-- Column 0: the first key. -/
def column0 (n : Nat) : Nat :=
  pick (Nat.blt n 262144) (Nat.div n 512) <|
  pick (Nat.blt n 1310720) (Nat.div (Nat.sub n 262144) 1024) <|
  pick (Nat.blt n 1312768) (Nat.sub n 1310720) <|
  pick (Nat.blt n 1316864) (Nat.sub n 1312768) <|
  pick (Nat.blt n 1325056) (Nat.sub n 1316864) <|
  pick (Nat.blt n 1390592) (Nat.sub n 1325056) 0

/-- Column 1: the second key. -/
def column1 (n : Nat) : Nat :=
  pick (Nat.blt n 262144) (Nat.mod n 512) <|
  pick (Nat.blt n 1310720) (Nat.mod (Nat.sub n 262144) 1024) <|
  pick (Nat.blt n 1325056) 0 <|
  pick (Nat.blt n 1390592) (Nat.mod (Nat.sub n 1325056) 256) 0

/-- Column 2: the table tag. -/
def column2 (n : Nat) : Nat :=
  pick (Nat.blt n 262144) 22 <|
  pick (Nat.blt n 1310720) 23 <|
  pick (Nat.blt n 1312768) 24 <|
  pick (Nat.blt n 1316864) 25 <|
  pick (Nat.blt n 1325056) 26 <|
  pick (Nat.blt n 1390592) 41 0

theorem columns_eq (n : Nat) :
    (paddedRow n)[0] = column0 n ∧ (paddedRow n)[1] = column1 n ∧ (paddedRow n)[2] = column2 n := by
  unfold paddedRow
  split
  · rename_i bound
    simp only [setupRow]
    split_ifs
    all_goals simp (disch := omega) only [column0, column1, column2, nat_blt, pick_true, pick_false, nat_sub,
      nat_div, nat_mod, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
      Nat.cast_ofNat, Nat.cast_zero, and_self]
  · rename_i bound
    simp (disch := omega) only [column0, column1, column2, nat_blt, pick_false, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, Nat.cast_zero, and_self]

end Airbender.Bigint.SetupProofs
