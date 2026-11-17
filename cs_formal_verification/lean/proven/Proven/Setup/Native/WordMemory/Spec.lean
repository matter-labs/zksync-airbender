module
public import Human.Compiler.NativeFixedRows
public import Human.Compiler.NativeSetups.WordMemory
public import Proven.Setup.Native.Common

@[expose] public section

/- Column formulas of the native word-memory setup, in the form that the kernel evaluates fast, and their agreement
   with the reviewed rows `NativeFixedRows.wordMemory` of the fixture ROM words. Rows from 1048577 hold the decoder
   table of the setup fixture program (every payload field is the sentinel `p - 1`, the tag is 46), then zero
   padding. -/

namespace Airbender.Compiler.NativeFixedRows.WordMemorySetupProofs
open Airbender.Import.Setup.Scan Airbender.Compiler.NativeSetups.Proofs

/-- The value of a row in each region: the disabled-query row, the ROM rows, the decoder rows, then zero padding. -/
def byRegion (n : Nat) (rom : Nat → Nat) (decoder : Nat) : Nat :=
  pick (Nat.beq n 0) 0 <| pick (Nat.blt n 1048577) (rom (Nat.sub n 1)) <| pick (Nat.blt n 2097153) decoder 0

def column0 (n : Nat) : Nat := byRegion n (fun key => Nat.mul 4 key) sentinel
def column1 (n : Nat) : Nat := byRegion n (fun key => Nat.mod (word key) 65536) sentinel
def column2 (n : Nat) : Nat := byRegion n (fun key => Nat.div (word key) 65536) sentinel
def column3 (n : Nat) : Nat := byRegion n (fun _ => 0) sentinel
def column4 (n : Nat) : Nat := byRegion n (fun _ => 0) sentinel
def column5 (n : Nat) : Nat := byRegion n (fun _ => 0) sentinel
def column6 (n : Nat) : Nat := byRegion n (fun _ => 0) sentinel
def column7 (n : Nat) : Nat := byRegion n (fun _ => 0) sentinel
def column8 (n : Nat) : Nat := byRegion n (fun _ => 34) 46

/-- The reviewed fixed rows, as integers. -/
def fixedRow (index : Fin 1048577) : Vector Int 9 :=
  (wordMemory NativeSetups.fixtureWords index).map (fun n : Nat => (n : Int))

set_option maxRecDepth 100000 in
theorem column_eq (n : Nat) (bound : n < 1048577) :
    (fixedRow ⟨n, bound⟩)[0] = column0 n ∧ (fixedRow ⟨n, bound⟩)[1] = column1 n ∧
    (fixedRow ⟨n, bound⟩)[2] = column2 n ∧ (fixedRow ⟨n, bound⟩)[3] = column3 n ∧
    (fixedRow ⟨n, bound⟩)[4] = column4 n ∧ (fixedRow ⟨n, bound⟩)[5] = column5 n ∧
    (fixedRow ⟨n, bound⟩)[6] = column6 n ∧ (fixedRow ⟨n, bound⟩)[7] = column7 n ∧
    (fixedRow ⟨n, bound⟩)[8] = column8 n := by
  simp only [fixedRow, wordMemory]
  split_ifs
  all_goals simp (disch := omega) only [column0, column1, column2, column3, column4, column5, column6, column7,
    column8, byRegion, Arithmetic.Word.ofBitVec, Arithmetic.limbBase, word_eq, nat_blt, nat_beq, pick_true,
    pick_false, nat_sub, nat_mul, nat_div, nat_mod, Vector.getElem_map, Vector.getElem_mk, Vector.getElem_replicate,
    List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, Nat.cast_ofNat, Nat.cast_zero, and_self]

/-- The column formulas, in native column order. -/
def formulas : List (Nat → Nat) := [column0, column1, column2, column3, column4, column5, column6, column7, column8]

-- One simp set serves every column; each column uses a part of it.
set_option linter.unusedSimpArgs false in
/-- Decoder slots from 4 (rows from 1048581): the sentinel `p - 1` in every payload field and the tag 46. -/
theorem row_decoder (n : Nat) (low : 1048581 ≤ n) (high : n < 2097153) :
    formulas.map (· n) = [sentinel, sentinel, sentinel, sentinel, sentinel, sentinel, sentinel, sentinel, 46] := by
  simp (disch := omega) only [formulas, List.map_cons, List.map_nil, column0, column1, column2, column3, column4,
    column5, column6, column7, column8, byRegion, nat_blt, nat_beq, nat_sub, pick_true, pick_false]

-- One simp set serves every column; each column uses a part of it.
set_option linter.unusedSimpArgs false in
/-- Rows from 2097153: zero padding. -/
theorem row_padding (n : Nat) (low : 2097153 ≤ n) : formulas.map (· n) = [0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  simp (disch := omega) only [formulas, List.map_cons, List.map_nil, column0, column1, column2, column3, column4,
    column5, column6, column7, column8, byRegion, nat_blt, nat_beq, nat_sub, pick_true, pick_false]

end Airbender.Compiler.NativeFixedRows.WordMemorySetupProofs
