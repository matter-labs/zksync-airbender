module
public import Human.Helpers.Tables.Bytes
public import Proven.Setup.Native.Common
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

/- Column formulas of the native shift/binary setup, in the form that the kernel evaluates fast, and their agreement
   with the reviewed fixed rows `Verification.shiftBinopRow`. Rows from 524545 hold the decoder table of the setup
   fixture program (no shift or binary instruction: every payload field is the sentinel `p - 1`, the tag is 46),
   then zero padding. -/

namespace Airbender.Verification.ShiftBinopSetupProofs
open Airbender.Import.Setup.Scan Airbender.Compiler.NativeSetups.Proofs

/-- The value of a row in each region: the zero row, the sign rows (tag 3), the XOR, OR and AND rows (tags 4, 6,
    7), the low-five-bits rows (tag 8), the shift rows (tag 9), the decoder rows, then zero padding. -/
def byRegion (n : Nat) (sign : Nat → Nat) (xor or and low5 shift : Nat → Nat) (decoder : Nat) : Nat :=
  pick (Nat.beq n 0) 0 <|
  pick (Nat.blt n 257) (sign (Nat.sub n 1)) <|
  pick (Nat.blt n 65793) (xor (Nat.sub n 257)) <|
  pick (Nat.blt n 131329) (or (Nat.sub n 65793)) <|
  pick (Nat.blt n 196865) (and (Nat.sub n 131329)) <|
  pick (Nat.blt n 262401) (low5 (Nat.sub n 196865)) <|
  pick (Nat.blt n 524545) (shift (Nat.sub n 262401)) <|
  pick (Nat.blt n 1573121) decoder 0

/-- The high and the low byte of a byte-pair key. -/
def high (key : Nat) : Nat := Nat.div (Nat.mod key 65536) 256
def low (key : Nat) : Nat := Nat.mod (Nat.mod key 65536) 256

/-- `shiftByteContribution`, with natural-number arithmetic on the 32-bit values. -/
def contribution (position byte amount operation : Nat) : Nat :=
  let input := Nat.mod (Nat.mul (Nat.mod byte 4294967296) (Nat.pow 2 (Nat.mul 8 position))) 4294967296
  pick (Nat.beq operation 1) (Nat.mod (Nat.mul input (Nat.pow 2 amount)) 4294967296) <|
  pick (Nat.beq operation 2) (Nat.div input (Nat.pow 2 amount)) <|
  pick (Nat.beq operation 3)
    (pick (Nat.ble 2147483648 input) (Nat.sub 4294967295 (Nat.div (Nat.sub 4294967295 input) (Nat.pow 2 amount)))
      (Nat.div input (Nat.pow 2 amount))) <|
  pick (Nat.beq operation 5)
    (pick (Nat.beq amount 0)
      (Nat.mod (Nat.mul (Nat.mod byte 4294967296) (Nat.pow 2 (Nat.mul 8 (Nat.sub 3 position)))) 4294967296) 0) 0

/-- The 32-bit output of a shift key. -/
def output (key : Nat) : Nat :=
  contribution (Nat.div key 65536) (Nat.mod (Nat.div key 256) 256) (Nat.mod (Nat.div key 8) 32) (Nat.mod key 8)

def column0 (n : Nat) : Nat :=
  byRegion n (fun byte => byte) high high high high (fun key => Nat.div key 65536) sentinel
def column1 (n : Nat) : Nat :=
  byRegion n (fun byte => pick (Nat.blt byte 128) 0 255) low low low low
    (fun key => Nat.mod (Nat.div key 256) 256) sentinel
def column2 (n : Nat) : Nat :=
  byRegion n (fun _ => 0) (fun key => Nat.xor (high key) (low key)) (fun key => Nat.lor (high key) (low key))
    (fun key => Nat.land (high key) (low key)) (fun key => Nat.mod (high key) 32)
    (fun key => Nat.mod (Nat.div key 8) 32) sentinel
def column3 (n : Nat) : Nat :=
  byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun key => Nat.mod key 8) sentinel
def column4 (n : Nat) : Nat :=
  byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun key => Nat.mod (output key) 256)
    sentinel
def column5 (n : Nat) : Nat :=
  byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun key => Nat.mod (Nat.div (output key) 256) 256) sentinel
def column6 (n : Nat) : Nat :=
  byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun key => Nat.mod (Nat.div (output key) 65536) 256) sentinel
def column7 (n : Nat) : Nat :=
  byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun key => Nat.mod (Nat.div (output key) 16777216) 256) sentinel
def column8 (n : Nat) : Nat :=
  byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) sentinel
def column9 (n : Nat) : Nat :=
  byRegion n (fun _ => 3) (fun _ => 4) (fun _ => 6) (fun _ => 7) (fun _ => 8) (fun _ => 9) 46

theorem contribution_eq (position byte amount operation : Nat) :
    (shiftByteContribution position byte amount operation).toNat =
      contribution position byte amount operation := by
  unfold shiftByteContribution contribution
  obtain _ | _ | _ | _ | _ | _ | operation := operation
  all_goals simp only [nat_beq, pick_decide, nat_mod, nat_mul, nat_pow, nat_div, nat_sub,
    BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_sshiftRight, BitVec.msb_eq_decide,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, BitVec.shiftLeft_eq, BitVec.ushiftRight_eq]
  all_goals simp [pick_decide, nat_ble, apply_ite BitVec.toNat, Nat.shiftLeft_eq]

theorem xor_byte (a b : Fin 256) : ((a ^^^ b : Fin 256) : Nat) = a.val ^^^ b.val :=
  Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 8) a.isLt b.isLt)

/-- The reviewed fixed rows, as integers. -/
def fixedRow (index : Fin 524545) : Vector Int 10 := (shiftBinopRow index).map (fun n : Nat => (n : Int))

set_option maxRecDepth 100000 in
theorem column_eq (n : Nat) (bound : n < 524545) :
    (fixedRow ⟨n, bound⟩)[0] = column0 n ∧ (fixedRow ⟨n, bound⟩)[1] = column1 n ∧
    (fixedRow ⟨n, bound⟩)[2] = column2 n ∧ (fixedRow ⟨n, bound⟩)[3] = column3 n ∧
    (fixedRow ⟨n, bound⟩)[4] = column4 n ∧ (fixedRow ⟨n, bound⟩)[5] = column5 n ∧
    (fixedRow ⟨n, bound⟩)[6] = column6 n ∧ (fixedRow ⟨n, bound⟩)[7] = column7 n ∧
    (fixedRow ⟨n, bound⟩)[8] = column8 n ∧ (fixedRow ⟨n, bound⟩)[9] = column9 n := by
  simp only [fixedRow, shiftBinopRow]
  split_ifs
  all_goals simp (disch := omega) only [binaryByteRow, ByteUtils.splitTwoBytes, column0, column1, column2,
    column3, column4, column5, column6, column7, column8, column9, byRegion, high, low, output,
    ← contribution_eq, xor_byte, nat_blt, nat_beq, pick_true, pick_false, nat_sub, nat_div, nat_mod, nat_xor,
    nat_land, nat_lor, Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
    List.getElem_cons_zero, Nat.reduceEqDiff, ↓reduceIte, Nat.cast_ofNat, Nat.cast_zero, and_self]

/-- Rows from 524545: the decoder rows of the setup fixture, then zero padding. -/
theorem column_after (n : Nat) (low : 524545 ≤ n) (c : Fin 10) :
    ((if n < 1573121 then (Vector.replicate 9 ((babyBearModulus - 1 : Nat) : Int)).push 46
      else Vector.replicate 10 0 : Vector Int 10))[c] =
      (![column0, column1, column2, column3, column4, column5, column6, column7, column8, column9] c n : Int) := by
  fin_cases c <;>
  simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
  simp (disch := omega) only [column0, column1, column2, column3, column4, column5, column6, column7, column8,
    column9, byRegion, nat_blt, nat_beq, pick_false] <;>
  split_ifs <;> simp_all [babyBearModulus]

end Airbender.Verification.ShiftBinopSetupProofs
