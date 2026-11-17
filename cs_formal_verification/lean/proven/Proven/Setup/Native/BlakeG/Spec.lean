module
public import Human.Circuits.Blake2G.Tables.SetupImport
public import Proven.Setup.Scan

@[expose] public section

/- Column formulas of the native BLAKE2 G setup, in the form that the kernel evaluates fast, and their agreement
   with the reviewed row formula `Blake2G.setupRow Control.controllerRows` (zero from row 344896). Regions: XOR with
   8-bit keys [0, 65536), 3-bit [65536, 65600), 4-bit [65600, 65856), 7-bit [65856, 82240), 9-bit [82240, 344384),
   controller [344384, 344896). -/

namespace Airbender.Blake2G.SetupProofs
open Airbender.Import.Setup.Scan

/-- The reviewed rows with zero padding, as integers. -/
def paddedRow (index : Nat) : Vector Int 9 :=
  if bound : index < 344896 then (setupRow Control.controllerRows ⟨index, bound⟩).map (fun n : Nat => (n : Int))
  else Vector.replicate 9 0

/-- Output `k` of the controller row of `key`. -/
def controller (k : Fin 7) (key : Nat) : Nat := (Control.controllerRows (Fin.ofNat 512 key))[k]

/-- The value of a row in each region, in region order; `xor width i` gives the XOR rows. -/
def byRegion (n : Nat) (xor : Nat → Nat → Nat) (control : Nat → Nat) : Nat :=
  pick (Nat.blt n 65536) (xor 8 n) <|
  pick (Nat.blt n 65600) (xor 3 (Nat.sub n 65536)) <|
  pick (Nat.blt n 65856) (xor 4 (Nat.sub n 65600)) <|
  pick (Nat.blt n 82240) (xor 7 (Nat.sub n 65856)) <|
  pick (Nat.blt n 344384) (xor 9 (Nat.sub n 82240)) <|
  pick (Nat.blt n 344896) (control (Nat.sub n 344384)) 0

def column0 (n : Nat) : Nat := byRegion n (fun width i => Nat.div i (Nat.pow 2 width)) (fun key => key)
def column1 (n : Nat) : Nat := byRegion n (fun width i => Nat.mod i (Nat.pow 2 width)) (controller 0)
def column2 (n : Nat) : Nat :=
  byRegion n (fun width i => Nat.xor (Nat.div i (Nat.pow 2 width)) (Nat.mod i (Nat.pow 2 width))) (controller 1)
def column3 (n : Nat) : Nat := byRegion n (fun _ _ => 0) (controller 2)
def column4 (n : Nat) : Nat := byRegion n (fun _ _ => 0) (controller 3)
def column5 (n : Nat) : Nat := byRegion n (fun _ _ => 0) (controller 4)
def column6 (n : Nat) : Nat := byRegion n (fun _ _ => 0) (controller 5)
def column7 (n : Nat) : Nat := byRegion n (fun _ _ => 0) (controller 6)
def column8 (n : Nat) : Nat :=
  byRegion n (fun width _ => pick (Nat.beq width 8) 4 <| pick (Nat.beq width 3) 17 <| pick (Nat.beq width 4) 18 <|
    pick (Nat.beq width 7) 19 20) (fun _ => 28)

set_option maxRecDepth 100000 in
theorem column_eq (n : Nat) :
    (paddedRow n)[0] = column0 n ∧ (paddedRow n)[1] = column1 n ∧ (paddedRow n)[2] = column2 n ∧
    (paddedRow n)[3] = column3 n ∧ (paddedRow n)[4] = column4 n ∧ (paddedRow n)[5] = column5 n ∧
    (paddedRow n)[6] = column6 n ∧ (paddedRow n)[7] = column7 n ∧ (paddedRow n)[8] = column8 n := by
  unfold paddedRow
  split
  · rename_i bound
    simp only [setupRow]
    split_ifs with h0 h1 h2 h3 h4
    all_goals simp (disch := omega) only [xorRow, column0, column1, column2, column3, column4, column5, column6,
      column7, column8, byRegion, controller, nat_blt, nat_beq, pick_true, pick_false, nat_sub, nat_div, nat_mod,
      nat_pow, nat_xor, Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.reducePow, decide_true, pick_of_true, Nat.cast_ofNat, Nat.cast_zero, true_and,
      and_self, and_true]
    have key : (⟨n - 344384, by omega⟩ : Fin 512) = Fin.ofNat 512 (n - 344384) :=
      Fin.ext (Nat.mod_eq_of_lt (by omega)).symm
    simp only [key]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rename_i bound
    simp (disch := omega) only [column0, column1, column2, column3, column4, column5, column6, column7, column8,
      byRegion, nat_blt, pick_false, Vector.getElem_replicate, Nat.cast_zero, and_self]

end Airbender.Blake2G.SetupProofs
