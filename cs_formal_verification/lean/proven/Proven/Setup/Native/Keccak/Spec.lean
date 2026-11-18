module
public import Human.Circuits.Keccak.Tables.SetupImport
public import Proven.Setup.Scan
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/- Column formulas of the native Keccak setup, in the form that the kernel evaluates fast, and their agreement with
   the reviewed row formula `Keccak.setupRow Controller.rows` (zero from row 1249281). -/

namespace Airbender.Keccak.SetupProofs
open Airbender.Import.Setup.Scan

/-- The reviewed rows with zero padding, as integers. -/
def paddedRow (index : Nat) : Vector Int 8 :=
  if bound : index < 1249281 then (setupRow Controller.rows ⟨index, bound⟩).map (fun n : Nat => (n : Int))
  else Vector.replicate 8 0

/-- `adjustedConstant`, as a table of the 32 control rounds. -/
def adjustedTable : List Nat :=
  [0, 1, 32898, 9223372036854808714, 9223372039002292224, 32907, 2147483649, 9223372039002292353,
    9223372036854808585, 138, 136, 2147516425, 2147483658, 2147516555, 9223372036854775947, 9223372036854808713,
    9223372036854808579, 9223372036854808578, 9223372036854775936, 32778, 9223372039002259466, 9223372039002292353,
    9223372036854808704, 2147483649, 9223372039002292232, 0, 0, 0, 0, 0, 0, 0]

/-- `iotaByte`, from the table. -/
def iota (control : Nat) : Nat :=
  Nat.mod (Nat.div (adjustedTable.getD (Nat.mod control 32) 0) (Nat.pow 2 (Nat.mul 8 (Nat.div control 32)))) 256

theorem adjustedTable_eq : ∀ round < 32, adjustedTable.getD round 0 = adjustedConstant round := by
  decide +kernel

theorem iota_eq (control : Nat) : iota control = iotaByte control := by
  simp only [iota, iotaByte, nat_mod, nat_div, nat_pow, nat_mul,
    adjustedTable_eq (control % 32) (Nat.mod_lt _ (by decide))]

/-- Output `k` of the controller row of `key`. -/
def controller (k : Fin 6) (key : Nat) : Nat := (Controller.rows (Fin.ofNat 4096 key))[k]

/-- The value of a row in each region, in region order: the zero row, the byte XOR rows (tag 4) on key `i`, the
    controller rows, the iota rows (tag 38), the chi rows (tag 39), the rotation rows (tag 40). -/
def byRegion (n : Nat) (xor : Nat → Nat) (control : Nat → Nat) (iotaRow chiRow rotation : Nat → Nat) : Nat :=
  pick (Nat.beq n 0) 0 <|
  pick (Nat.blt n 65537) (xor (Nat.sub n 1)) <|
  pick (Nat.blt n 69633) (control (Nat.sub n 65537)) <|
  pick (Nat.blt n 135169) (iotaRow (Nat.sub n 69633)) <|
  pick (Nat.blt n 200705) (chiRow (Nat.sub n 135169)) <|
  pick (Nat.blt n 1249281) (rotation (Nat.sub n 200705)) 0

/-- `value s` for `s < 16`, through four comparisons, so that each case has a literal `s`. -/
def bySixteen (s : Nat) (value : Nat → Nat) : Nat :=
  pick (Nat.blt s 8)
    (pick (Nat.blt s 4)
      (pick (Nat.blt s 2) (pick (Nat.blt s 1) (value 0) (value 1)) (pick (Nat.blt s 3) (value 2) (value 3)))
      (pick (Nat.blt s 6) (pick (Nat.blt s 5) (value 4) (value 5)) (pick (Nat.blt s 7) (value 6) (value 7))))
    (pick (Nat.blt s 12)
      (pick (Nat.blt s 10) (pick (Nat.blt s 9) (value 8) (value 9)) (pick (Nat.blt s 11) (value 10) (value 11)))
      (pick (Nat.blt s 14) (pick (Nat.blt s 13) (value 12) (value 13)) (pick (Nat.blt s 15) (value 14) (value 15))))

theorem bySixteen_eq (s : Nat) (value : Nat → Nat) (h : s < 16) : bySixteen s value = value s := by
  interval_cases s <;> rfl

/-- The bits that a rotation by `key / 65536` shifts out of the 16-bit word `key % 65536`. -/
def rotationHigh (key : Nat) : Nat :=
  bySixteen (Nat.div key 65536) fun shift => Nat.div (Nat.mod key 65536) (Nat.pow 2 (Nat.sub 16 shift))

/-- The low 16 bits of the 16-bit word `key % 65536` shifted left by `key / 65536`. -/
def rotationLow (key : Nat) : Nat :=
  bySixteen (Nat.div key 65536) fun shift => Nat.mod (Nat.mul (Nat.mod key 65536) (Nat.pow 2 shift)) 65536

def column0 (n : Nat) : Nat :=
  byRegion n (fun i => Nat.div i 256) (fun i => i) (fun i => Nat.mod i 256) (fun i => Nat.mod i 256) (fun i => i)
def column1 (n : Nat) : Nat :=
  byRegion n (fun i => Nat.mod i 256) (controller 0) (fun i => Nat.div i 256) (fun i => Nat.div i 256) rotationHigh
def column2 (n : Nat) : Nat :=
  byRegion n (fun i => Nat.xor (Nat.div i 256) (Nat.mod i 256)) (controller 1)
    (fun i => Nat.xor (Nat.mod i 256) (iota (Nat.div i 256)))
    (fun i => Nat.land (Nat.xor (Nat.mod i 256) 255) (Nat.div i 256)) rotationLow
def column3 (n : Nat) : Nat := byRegion n (fun _ => 0) (controller 2) (fun _ => 0) (fun _ => 0) (fun _ => 0)
def column4 (n : Nat) : Nat := byRegion n (fun _ => 0) (controller 3) (fun _ => 0) (fun _ => 0) (fun _ => 0)
def column5 (n : Nat) : Nat := byRegion n (fun _ => 0) (controller 4) (fun _ => 0) (fun _ => 0) (fun _ => 0)
def column6 (n : Nat) : Nat := byRegion n (fun _ => 0) (controller 5) (fun _ => 0) (fun _ => 0) (fun _ => 0)
def column7 (n : Nat) : Nat := byRegion n (fun _ => 4) (fun _ => 37) (fun _ => 38) (fun _ => 39) (fun _ => 40)

theorem rotationHigh_eq (key : Nat) (h : key < 1048576) :
    rotationHigh key = key % 65536 / 2 ^ (16 - key / 65536) := by
  simp only [rotationHigh, bySixteen_eq _ _ (show key / 65536 < 16 by omega), nat_div, nat_mod, nat_pow, nat_sub]

theorem rotationLow_eq (key : Nat) (h : key < 1048576) :
    rotationLow key = key % 65536 * 2 ^ (key / 65536) % 65536 := by
  simp only [rotationLow, bySixteen_eq _ _ (show key / 65536 < 16 by omega), nat_mul, nat_mod, nat_pow, nat_div]

set_option maxRecDepth 20000 in
theorem column_eq (n : Nat) :
    (paddedRow n)[0] = column0 n ∧ (paddedRow n)[1] = column1 n ∧ (paddedRow n)[2] = column2 n ∧
    (paddedRow n)[3] = column3 n ∧ (paddedRow n)[4] = column4 n ∧ (paddedRow n)[5] = column5 n ∧
    (paddedRow n)[6] = column6 n ∧ (paddedRow n)[7] = column7 n := by
  unfold paddedRow
  split
  · rename_i bound
    simp only [setupRow]
    split_ifs with h0 h1 h2 h3 h4
    all_goals simp (disch := omega) only [byteRow, rotationRow, column0, column1, column2, column3, column4,
      column5, column6, column7, byRegion, controller, iota_eq, nat_blt, nat_beq, pick_true, pick_false, nat_sub,
      nat_div, nat_mod, nat_xor, nat_land, Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_succ, List.getElem_cons_zero, Nat.reduceEqDiff, ↓reduceIte, Nat.cast_ofNat, true_and,
      Vector.getElem_replicate, Nat.cast_zero, and_self, and_true]
    · have key : (⟨n - 65537, by omega⟩ : Fin 4096) = Fin.ofNat 4096 (n - 65537) :=
        Fin.ext (Nat.mod_eq_of_lt (by omega)).symm
      simp only [key]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [rotationHigh_eq _ (by omega), rotationLow_eq _ (by omega)]
      exact ⟨rfl, rfl⟩
  · rename_i bound
    simp (disch := omega) only [column0, column1, column2, column3, column4, column5, column6, column7, byRegion,
      nat_blt, nat_beq, pick_false, Vector.getElem_replicate, Nat.cast_zero, and_self]

end Airbender.Keccak.SetupProofs
