module
public import Human.Compiler.NativeFixedRows
public import Human.Compiler.NativeSetups.JumpBranch
public import Proven.Setup.Native.Common
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/- Column formulas of the native jump/branch setup, in the form that the kernel evaluates fast, and their agreement
   with the reviewed fixed rows `NativeFixedRows.jumpBranch`. Rows from 4456448 hold the decoder table of the setup
   fixture program (slot 2 holds `jal x0, 0`; every payload field of every other slot is the sentinel `p - 1`; the tag
   is 46), then zero padding. -/

namespace Airbender.Compiler.NativeFixedRows.JumpBranchSetupProofs
open Airbender.Import.Setup.Scan Airbender.Compiler.NativeSetups.Proofs

/-- `Verification.conditionalValue`: the operation `key / 524288 % 8` applied to the sign, less-than and equality
    bits of the key. -/
def conditional (key : Nat) : Nat :=
  let rs2 := bit key 32768
  let rs1 := bit key 65536
  let less := bit key 131072
  let equal := bit key 262144
  let signed := pick (Nat.beq rs1 1) (pick (Nat.beq rs2 0) 1 less) (pick (Nat.beq rs2 1) 0 less)
  let operation := Nat.mod (Nat.div key 524288) 8
  pick (Nat.beq operation 0) equal <| pick (Nat.beq operation 1) (Nat.sub 1 equal) <|
  pick (Nat.beq operation 2) signed <| pick (Nat.beq operation 3) less <| pick (Nat.beq operation 4) signed <|
  pick (Nat.beq operation 5) (Nat.sub 1 signed) <| pick (Nat.beq operation 6) less (Nat.sub 1 less)

set_option maxRecDepth 10000 in
theorem conditional_eq (key : Nat) : conditional key = Verification.conditionalValue key := by
  have h0 : key / 32768 % 2 < 2 := Nat.mod_lt _ (by decide)
  have h1 : key / 65536 % 2 < 2 := Nat.mod_lt _ (by decide)
  have h2 : key / 131072 % 2 < 2 := Nat.mod_lt _ (by decide)
  have h3 : key / 262144 % 2 < 2 := Nat.mod_lt _ (by decide)
  have h4 : key / 524288 % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [conditional, Verification.conditionalValue, bit, nat_div, nat_mod, nat_sub, nat_beq, pick_decide]
  generalize key / 32768 % 2 = a at *
  generalize key / 65536 % 2 = b at *
  generalize key / 131072 % 2 = c at *
  generalize key / 262144 % 2 = d at *
  generalize key / 524288 % 8 = e at *
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;> interval_cases e <;> rfl

/-- The value of a row in each region: tables 1, 2, 5 and 31, the decoder rows, then zero padding. -/
def byRegion (n : Nat) (table1 table2 table5 table31 : Nat → Nat) (decoder : Nat → Nat) : Nat :=
  pick (Nat.blt n 131072) (table1 n) <|
  pick (Nat.blt n 196608) (table2 (Nat.sub n 131072)) <|
  pick (Nat.blt n 262144) (table5 (Nat.sub n 196608)) <|
  pick (Nat.blt n 4456448) (table31 (Nat.sub n 262144)) <|
  pick (Nat.blt n 5505024) (decoder (Nat.sub n 4456448)) 0

/-- Field `value` of decoder slot 2 (`jal x0, 0`), the sentinel in every other slot. -/
def decoder (value slot : Nat) : Nat := pick (Nat.beq slot 2) value sentinel

def column0 (n : Nat) : Nat :=
  byRegion n (fun key => key) (fun key => key) (fun key => key) (fun key => key) (decoder 8)
def column1 (n : Nat) : Nat :=
  byRegion n (fun key => pick (Nat.beq key 0) 1 0) (fun key => bit key 2) (fun key => Nat.div key 32768)
    conditional (decoder 0)
def column2 (n : Nat) : Nat :=
  byRegion n (fun _ => 0) (fun key => Nat.sub key (Nat.mod key 4)) (fun _ => 0) (fun _ => 0) (decoder 0)
def column3 (n : Nat) : Nat := byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (decoder 0)
def column4 (n : Nat) : Nat := byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (decoder 0)
def column5 (n : Nat) : Nat := byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (decoder 0)
def column6 (n : Nat) : Nat := byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (decoder 0)
def column7 (n : Nat) : Nat := byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (decoder 0)
def column8 (n : Nat) : Nat := byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (decoder 17)
def column9 (n : Nat) : Nat := byRegion n (fun _ => 1) (fun _ => 2) (fun _ => 5) (fun _ => 31) (fun _ => 46)

/-- The reviewed fixed rows, as integers. -/
def fixedRow (index : Fin 4456448) : Vector Int 10 := (jumpBranch index).map (fun n : Nat => (n : Int))

set_option maxRecDepth 100000 in
theorem column_eq (n : Nat) (bound : n < 4456448) :
    (fixedRow ⟨n, bound⟩)[0] = column0 n ∧ (fixedRow ⟨n, bound⟩)[1] = column1 n ∧
    (fixedRow ⟨n, bound⟩)[2] = column2 n ∧ (fixedRow ⟨n, bound⟩)[3] = column3 n ∧
    (fixedRow ⟨n, bound⟩)[4] = column4 n ∧ (fixedRow ⟨n, bound⟩)[5] = column5 n ∧
    (fixedRow ⟨n, bound⟩)[6] = column6 n ∧ (fixedRow ⟨n, bound⟩)[7] = column7 n ∧
    (fixedRow ⟨n, bound⟩)[8] = column8 n ∧ (fixedRow ⟨n, bound⟩)[9] = column9 n := by
  have conditional_row (low : 262144 ≤ n) : column1 n = conditional (n - 262144) := by
    simp (disch := omega) only [column1, byRegion, nat_blt, pick_false, pick_true, nat_sub]
  simp only [fixedRow, jumpBranch]
  split_ifs
  all_goals simp (disch := omega) only [column0, column2, column3, column4, column5, column6, column7, column8,
    column9, byRegion, nat_blt, pick_true, pick_false, nat_sub, nat_mod, Vector.getElem_map,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, and_self, true_and, and_true]
  all_goals first
    | rw [conditional_row (by omega), conditional_eq]
    | simp (disch := omega) only [column1, byRegion, bit, nat_blt, nat_beq, pick_true, pick_false, nat_sub, nat_div,
        nat_mod, Nat.cast_one, Nat.cast_zero]

/-- The column formulas, in native column order. -/
def formulas : List (Nat → Nat) :=
  [column0, column1, column2, column3, column4, column5, column6, column7, column8, column9]

-- One simp set serves every column; each column uses a part of it.
set_option linter.unusedSimpArgs false in
/-- Decoder slots from 4 (rows from 4456452): the sentinel `p - 1` in every payload field and the tag 46. -/
theorem row_decoder (n : Nat) (low : 4456452 ≤ n) (high : n < 5505024) :
    formulas.map (· n) =
      [sentinel, sentinel, sentinel, sentinel, sentinel, sentinel, sentinel, sentinel, sentinel, 46] := by
  simp (disch := omega) only [formulas, List.map_cons, List.map_nil, column0, column1, column2, column3, column4,
    column5, column6, column7, column8, column9, decoder, byRegion, nat_blt, nat_beq, nat_sub, pick_true, pick_false]

-- One simp set serves every column; each column uses a part of it.
set_option linter.unusedSimpArgs false in
/-- Rows from 5505024: zero padding. -/
theorem row_padding (n : Nat) (low : 5505024 ≤ n) : formulas.map (· n) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  simp (disch := omega) only [formulas, List.map_cons, List.map_nil, column0, column1, column2, column3, column4,
    column5, column6, column7, column8, column9, decoder, byRegion, nat_blt, nat_beq, nat_sub, pick_true, pick_false]

end Airbender.Compiler.NativeFixedRows.JumpBranchSetupProofs
