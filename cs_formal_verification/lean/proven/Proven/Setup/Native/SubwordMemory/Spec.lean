module
public import Human.Compiler.NativeFixedRows
public import Human.Compiler.NativeSetups.SubwordMemory
public import Proven.Setup.Native.Common

@[expose] public section

/- Column formulas of the native subword-memory setup, in the form that the kernel evaluates fast, and their
   agreement with the reviewed rows `Verification.subwordRow` of the fixture ROM words. Rows from 13238273 hold the
   decoder table of the setup fixture program (every payload field is the sentinel `p - 1`, the tag is 46), then
   zero padding. -/

namespace Airbender.Compiler.NativeFixedRows.SubwordMemorySetupProofs
open Airbender.Import.Setup.Scan Airbender.Compiler.NativeSetups.Proofs Airbender.Verification

/-- The loaded value of `subwordLoadLimbs`: a half-word, or the byte that bit 17 selects. -/
def loadValue (byte : Bool) (key : Nat) : Nat :=
  pick byte (Nat.mod (Nat.div (Nat.mod key 65536) (pick (Nat.beq (bit key 131072) 1) 256 1)) 256) (Nat.mod key 65536)

/-- The sign extension of `subwordLoadLimbs` applies. -/
def negative (byte : Bool) (key : Nat) : Bool :=
  and (Nat.beq (bit key 65536) 1) (Nat.ble (pick byte 128 32768) (loadValue byte key))

/-- The two limbs of `subwordLoadLimbs`. -/
def loadLow (byte : Bool) (key : Nat) : Nat :=
  Nat.add (loadValue byte key) (pick (and byte (negative byte key)) 65280 0)
def loadHigh (byte : Bool) (key : Nat) : Nat := pick (negative byte key) 65535 0

theorem load_eq (byte : Bool) (key : Nat) :
    subwordLoadLimbs byte key = (loadLow byte key, loadHigh byte key) := by
  cases byte <;>
  simp only [subwordLoadLimbs, loadLow, loadHigh, negative, loadValue, bit, nat_beq, nat_ble, ← Bool.decide_and,
    pick_decide, pick_of_true, pick_of_false, nat_add, nat_div, nat_mod, Bool.false_and, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]

/-- `subwordStoreContribution`. -/
def store (clear : Bool) (key : Nat) : Nat :=
  pick clear
    (pick (Nat.beq (bit key 65536) 1) (Nat.mod (Nat.mod key 65536) 256)
      (Nat.sub (Nat.mod key 65536) (Nat.mod (Nat.mod key 65536) 256)))
    (Nat.mul (Nat.mod key 256) (pick (Nat.beq (bit key 65536) 1) 256 1))

theorem store_eq (clear : Bool) (key : Nat) : subwordStoreContribution clear key = store clear key := by
  cases clear <;> simp [subwordStoreContribution, store, bit, nat_beq, pick_decide, nat_div, nat_mod]

/-- The key of a ROM half-word row: the half-word, and the signed flag in bit 16. -/
def halfKey (i : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.div (word (Nat.div i 4)) (pick (Nat.beq (Nat.mod i 2) 1) 65536 1)) 65536)
    (Nat.mul 65536 (bit i 2))

/-- The key of a ROM byte row: the half-word, the signed flag in bit 16 and the byte selector in bit 17. -/
def byteKey (i : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.div (word (Nat.div i 8)) (pick (Nat.beq (bit i 2) 1) 65536 1)) 65536)
    (Nat.add (Nat.mul 65536 (bit i 4)) (Nat.mul 131072 (Nat.mod i 2)))

/-- The value of a row in each region: the zero row, the store tables 29 and 30, the load tables 42 and 43, the ROM
    tables 44 and 45, the decoder rows, then zero padding. -/
def byRegion (n : Nat) (place clear loadHalf loadByte romHalf romByte : Nat → Nat) (decoder : Nat) : Nat :=
  pick (Nat.beq n 0) 0 <|
  pick (Nat.blt n 131073) (place (Nat.sub n 1)) <|
  pick (Nat.blt n 262145) (clear (Nat.sub n 131073)) <|
  pick (Nat.blt n 393217) (loadHalf (Nat.sub n 262145)) <|
  pick (Nat.blt n 655361) (loadByte (Nat.sub n 393217)) <|
  pick (Nat.blt n 4849665) (romHalf (Nat.sub n 655361)) <|
  pick (Nat.blt n 13238273) (romByte (Nat.sub n 4849665)) <|
  pick (Nat.blt n 14286849) decoder 0

section Regions
variable {n : Nat} {place clear loadHalf loadByte romHalf romByte : Nat → Nat} {decoder : Nat}

/-! The formula of each region, for `long_ok`: a block in one region rewrites with one of these. -/

theorem byRegion_place (low : 1 ≤ n) (high : n < 131073) :
    byRegion n place clear loadHalf loadByte romHalf romByte decoder = place (n - 1) := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_true, pick_false, nat_sub]

theorem byRegion_clear (low : 131073 ≤ n) (high : n < 262145) :
    byRegion n place clear loadHalf loadByte romHalf romByte decoder = clear (n - 131073) := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_true, pick_false, nat_sub]

theorem byRegion_loadHalf (low : 262145 ≤ n) (high : n < 393217) :
    byRegion n place clear loadHalf loadByte romHalf romByte decoder = loadHalf (n - 262145) := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_true, pick_false, nat_sub]

theorem byRegion_loadByte (low : 393217 ≤ n) (high : n < 655361) :
    byRegion n place clear loadHalf loadByte romHalf romByte decoder = loadByte (n - 393217) := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_true, pick_false, nat_sub]

theorem byRegion_romHalf (low : 655361 ≤ n) (high : n < 4849665) :
    byRegion n place clear loadHalf loadByte romHalf romByte decoder = romHalf (n - 655361) := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_true, pick_false, nat_sub]

theorem byRegion_romByte (low : 4849665 ≤ n) (high : n < 13238273) :
    byRegion n place clear loadHalf loadByte romHalf romByte decoder = romByte (n - 4849665) := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_true, pick_false, nat_sub]

theorem byRegion_decoder (low : 13238273 ≤ n) (high : n < 14286849) :
    byRegion n place clear loadHalf loadByte romHalf romByte decoder = decoder := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_true, pick_false]

theorem byRegion_padding (low : 14286849 ≤ n) :
    byRegion n place clear loadHalf loadByte romHalf romByte decoder = 0 := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_false]

end Regions

/-- Zero on every fixed row, the sentinel on the decoder rows, then zero padding. -/
def fixedZero (n : Nat) : Nat := pick (Nat.blt n 13238273) 0 <| pick (Nat.blt n 14286849) sentinel 0

def column0 (n : Nat) : Nat :=
  byRegion n (fun key => key) (fun key => key) (fun key => key) (fun key => key)
    (fun i => Nat.add (Nat.mul 4 (Nat.div i 4)) (Nat.add (Nat.mul 4194304 (bit i 2)) (Nat.mul 8388608 (Nat.mod i 2))))
    (fun i => Nat.add (Nat.mul 4 (Nat.div i 8)) (Nat.add (Nat.mul 4194304 (bit i 4))
      (Nat.add (Nat.mul 8388608 (bit i 2)) (Nat.mul 16777216 (Nat.mod i 2)))))
    sentinel
def column1 (n : Nat) : Nat :=
  byRegion n (store false) (store true) (loadLow false) (loadLow true) (fun i => loadLow false (halfKey i))
    (fun i => loadLow true (byteKey i)) sentinel
def column2 (n : Nat) : Nat :=
  byRegion n (fun _ => 0) (fun _ => 0) (loadHigh false) (loadHigh true) (fun i => loadHigh false (halfKey i))
    (fun i => loadHigh true (byteKey i)) sentinel
def column3 (n : Nat) : Nat := fixedZero n
def column4 (n : Nat) : Nat := fixedZero n
def column5 (n : Nat) : Nat := fixedZero n
def column6 (n : Nat) : Nat := fixedZero n
def column7 (n : Nat) : Nat := fixedZero n
def column8 (n : Nat) : Nat :=
  byRegion n (fun _ => 29) (fun _ => 30) (fun _ => 42) (fun _ => 43) (fun _ => 44) (fun _ => 45) 46

/-- The reviewed fixed rows, as integers. -/
def fixedRow (index : Fin 13238273) : Vector Int 9 :=
  (subwordRow NativeSetups.fixtureWords index).map (fun n : Nat => (n : Int))

set_option maxRecDepth 100000 in
theorem column_eq (n : Nat) (bound : n < 13238273) :
    (fixedRow ⟨n, bound⟩)[0] = column0 n ∧ (fixedRow ⟨n, bound⟩)[1] = column1 n ∧
    (fixedRow ⟨n, bound⟩)[2] = column2 n ∧ (fixedRow ⟨n, bound⟩)[3] = column3 n ∧
    (fixedRow ⟨n, bound⟩)[4] = column4 n ∧ (fixedRow ⟨n, bound⟩)[5] = column5 n ∧
    (fixedRow ⟨n, bound⟩)[6] = column6 n ∧ (fixedRow ⟨n, bound⟩)[7] = column7 n ∧
    (fixedRow ⟨n, bound⟩)[8] = column8 n := by
  simp only [fixedRow, subwordRow]
  split_ifs
  all_goals simp (disch := omega) only [subwordDataRow, load_eq, store_eq, column0, column1, column2, column3,
    column4, column5, column6, column7, column8, fixedZero, byRegion, halfKey, byteKey, bit, word_eq, nat_blt,
    nat_beq, pick_true, pick_false, nat_add, nat_sub, nat_mul, nat_div, nat_mod, Vector.getElem_map,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, Nat.cast_ofNat,
    Nat.cast_zero, and_self]
  all_goals simp only [Nat.add_assoc, and_true]

/-- The column formulas, in native column order. -/
def formulas : List (Nat → Nat) := [column0, column1, column2, column3, column4, column5, column6, column7, column8]

-- One simp set serves every column; each column uses a part of it.
set_option linter.unusedSimpArgs false in
/-- Decoder slots from 4 (rows from 13238277): the sentinel `p - 1` in every payload field and the tag 46. -/
theorem row_decoder (n : Nat) (low : 13238277 ≤ n) (high : n < 14286849) :
    formulas.map (· n) = [sentinel, sentinel, sentinel, sentinel, sentinel, sentinel, sentinel, sentinel, 46] := by
  simp (disch := omega) only [formulas, List.map_cons, List.map_nil, column0, column1, column2, column3, column4,
    column5, column6, column7, column8, fixedZero, byRegion, nat_blt, nat_beq, nat_sub, pick_true, pick_false]

-- One simp set serves every column; each column uses a part of it.
set_option linter.unusedSimpArgs false in
/-- Rows from 14286849: zero padding. -/
theorem row_padding (n : Nat) (low : 14286849 ≤ n) : formulas.map (· n) = [0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  simp (disch := omega) only [formulas, List.map_cons, List.map_nil, column0, column1, column2, column3, column4,
    column5, column6, column7, column8, fixedZero, byRegion, nat_blt, nat_beq, nat_sub, pick_true, pick_false]

end Airbender.Compiler.NativeFixedRows.SubwordMemorySetupProofs
