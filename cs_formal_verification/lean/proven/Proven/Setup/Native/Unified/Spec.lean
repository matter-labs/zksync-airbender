module
public import Proven.Setup.Native.ShiftBinop.Spec
public import Human.Compiler.NativeSetups.Claims
public import Proven.Setup.Native.JumpBranch.Spec
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FinCases

@[expose] public section

/- Column formulas of the native unified setup, in the form that the kernel evaluates fast, and their agreement with
   the reviewed rows `NativeFixedRows.unified` of the fixture ROM words, in native row order. The native regions, in
   row order: the zero row, tables 1, 2, 3, 5, 8 and 9, the ROM words (34), the XOR-rotate tables (47 to 50), the
   conditional table (51), the wide binary tables (52, 53, 54), then the decoder rows of the setup fixture program
   and zero padding. -/

namespace Airbender.Compiler.NativeFixedRows.UnifiedSetupProofs
open Airbender.Import.Setup.Scan Airbender.Compiler.NativeSetups.Proofs
open Airbender.Compiler.NativeFixedRows.JumpBranchSetupProofs (conditional conditional_eq)
open Airbender.Verification.ShiftBinopSetupProofs renaming column0 → binary0, column1 → binary1, column2 → binary2,
  column3 → binary3, column4 → binary4, column5 → binary5, column6 → binary6, column7 → binary7, column8 → binary8,
  column9 → binary9

/-- The rotation of an XOR-rotate key. -/
def rotation (i : Nat) : Nat :=
  pick (Nat.blt i 65536) 16 <| pick (Nat.blt i 131072) 12 <| pick (Nat.blt i 196608) 8 7

/-- The 32-bit output of an XOR-rotate key: the byte XOR rotated right by `rotation`. -/
def rotated (i : Nat) : Nat :=
  Nat.lor (Nat.div (Nat.xor (Nat.mod (Nat.div i 256) 256) (Nat.mod i 256)) (Nat.pow 2 (rotation i)))
    (Nat.mod (Nat.mul (Nat.xor (Nat.mod (Nat.div i 256) 256) (Nat.mod i 256)) (Nat.pow 2 (Nat.sub 32 (rotation i))))
      4294967296)

/-- `conditionalKey`: the seven-bit key packed into the standalone conditional key. -/
def packedKey (key : Nat) : Nat :=
  Nat.add (Nat.mul (Nat.mod key 2) 32768) <| Nat.add (Nat.mul (bit key 2) 65536) <|
    Nat.add (Nat.mul (bit key 4) 131072) <|
      Nat.add (Nat.mul (bit key 8) 262144) (Nat.mul (Nat.mod (Nat.div key 16) 8) 524288)

/-- Field values of decoder slots 0 to 3 of the setup fixture program; the sentinel in every other slot. -/
def decoder (first second third fourth slot : Nat) : Nat :=
  pick (Nat.beq slot 0) first <| pick (Nat.beq slot 1) second <| pick (Nat.beq slot 2) third <|
    pick (Nat.beq slot 3) fourth sentinel

/-- The value of a row in each native region. -/
def byRegion (n : Nat) (zeroTest jump sign limbSign low5 shift rom rotate conditional7 wide : Nat → Nat)
    (fixtureDecoder : Nat → Nat) : Nat :=
  pick (Nat.beq n 0) 0 <|
  pick (Nat.blt n 131073) (zeroTest (Nat.sub n 1)) <|
  pick (Nat.blt n 196609) (jump (Nat.sub n 131073)) <|
  pick (Nat.blt n 196865) (sign (Nat.sub n 196609)) <|
  pick (Nat.blt n 262401) (limbSign (Nat.sub n 196865)) <|
  pick (Nat.blt n 327937) (low5 (Nat.sub n 262401)) <|
  pick (Nat.blt n 590081) (shift (Nat.sub n 327937)) <|
  pick (Nat.blt n 1638657) (rom (Nat.sub n 590081)) <|
  pick (Nat.blt n 1900801) (rotate (Nat.sub n 1638657)) <|
  pick (Nat.blt n 1900929) (conditional7 (Nat.sub n 1900801)) <|
  pick (Nat.blt n 2097537) (wide (Nat.sub n 1900929)) <|
  pick (Nat.blt n 3146113) (fixtureDecoder (Nat.sub n 2097537)) 0

section Regions
variable {n : Nat} {zeroTest jump sign limbSign low5 shift rom rotate conditional7 wide fixtureDecoder : Nat → Nat}

/-! The formula of each region, for `long_ok`: a block in one region rewrites with one of these. -/

theorem byRegion_zeroTest (low : 1 ≤ n) (high : n < 131073) :
    byRegion n zeroTest jump sign limbSign low5 shift rom rotate conditional7 wide fixtureDecoder =
      zeroTest (n - 1) := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_true, pick_false, nat_sub]

theorem byRegion_jump (low : 131073 ≤ n) (high : n < 196609) :
    byRegion n zeroTest jump sign limbSign low5 shift rom rotate conditional7 wide fixtureDecoder =
      jump (n - 131073) := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_true, pick_false, nat_sub]

theorem byRegion_sign (low : 196609 ≤ n) (high : n < 196865) :
    byRegion n zeroTest jump sign limbSign low5 shift rom rotate conditional7 wide fixtureDecoder =
      sign (n - 196609) := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_true, pick_false, nat_sub]

theorem byRegion_limbSign (low : 196865 ≤ n) (high : n < 262401) :
    byRegion n zeroTest jump sign limbSign low5 shift rom rotate conditional7 wide fixtureDecoder =
      limbSign (n - 196865) := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_true, pick_false, nat_sub]

theorem byRegion_low5 (low : 262401 ≤ n) (high : n < 327937) :
    byRegion n zeroTest jump sign limbSign low5 shift rom rotate conditional7 wide fixtureDecoder =
      low5 (n - 262401) := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_true, pick_false, nat_sub]

theorem byRegion_shift (low : 327937 ≤ n) (high : n < 590081) :
    byRegion n zeroTest jump sign limbSign low5 shift rom rotate conditional7 wide fixtureDecoder =
      shift (n - 327937) := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_true, pick_false, nat_sub]

theorem byRegion_rom (low : 590081 ≤ n) (high : n < 1638657) :
    byRegion n zeroTest jump sign limbSign low5 shift rom rotate conditional7 wide fixtureDecoder =
      rom (n - 590081) := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_true, pick_false, nat_sub]

theorem byRegion_rotate (low : 1638657 ≤ n) (high : n < 1900801) :
    byRegion n zeroTest jump sign limbSign low5 shift rom rotate conditional7 wide fixtureDecoder =
      rotate (n - 1638657) := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_true, pick_false, nat_sub]

theorem byRegion_conditional (low : 1900801 ≤ n) (high : n < 1900929) :
    byRegion n zeroTest jump sign limbSign low5 shift rom rotate conditional7 wide fixtureDecoder =
      conditional7 (n - 1900801) := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_true, pick_false, nat_sub]

theorem byRegion_wide (low : 1900929 ≤ n) (high : n < 2097537) :
    byRegion n zeroTest jump sign limbSign low5 shift rom rotate conditional7 wide fixtureDecoder =
      wide (n - 1900929) := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_true, pick_false, nat_sub]

theorem byRegion_decoder (low : 2097537 ≤ n) (high : n < 3146113) :
    byRegion n zeroTest jump sign limbSign low5 shift rom rotate conditional7 wide fixtureDecoder =
      fixtureDecoder (n - 2097537) := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_true, pick_false, nat_sub]

theorem byRegion_padding (low : 3146113 ≤ n) :
    byRegion n zeroTest jump sign limbSign low5 shift rom rotate conditional7 wide fixtureDecoder = 0 := by
  simp (disch := omega) only [byRegion, nat_beq, nat_blt, pick_false]

end Regions

/-- The value of a row in each native region, with the regions of the shift/binary setup (`binary`, tables 3, 8, 9
    and the wide binary tables) read at their row of that setup. -/
abbrev byRegionShift (n : Nat) (zeroTest jump limbSign rom rotate conditional7 : Nat → Nat) (binary : Nat → Nat)
    (fixtureDecoder : Nat → Nat) : Nat :=
  byRegion n zeroTest jump (fun k => binary (Nat.add 1 k)) limbSign (fun k => binary (Nat.add 196865 k))
    (fun k => binary (Nat.add 262401 k)) rom rotate conditional7 (fun k => binary (Nat.add 257 k)) fixtureDecoder

def column0 (n : Nat) : Nat :=
  byRegionShift n (fun key => key) (fun key => key) (fun key => key) (fun key => Nat.mul 4 key)
    (fun i => Nat.mod (Nat.div i 256) 256) (fun key => key) binary0 (decoder 0 4 8 12)
def column1 (n : Nat) : Nat :=
  byRegionShift n (fun key => pick (Nat.beq key 0) 1 0) (fun key => bit key 2) (fun key => Nat.div key 32768)
    (fun key => Nat.mod (word key) 65536) (fun i => Nat.mod i 256) (fun key => conditional (packedKey key))
    binary1 (decoder 0 0 0 0)
def column2 (n : Nat) : Nat :=
  byRegionShift n (fun _ => 0) (fun key => Nat.sub key (Nat.mod key 4)) (fun _ => 0)
    (fun key => Nat.div (word key) 65536) (fun i => Nat.mod (rotated i) 256) (fun _ => 0) binary2
    (decoder 0 1 0 3)
def column3 (n : Nat) : Nat :=
  byRegionShift n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun i => Nat.mod (Nat.div (rotated i) 256) 256)
    (fun _ => 0) binary3 (decoder 0 0 0 7)
def column4 (n : Nat) : Nat :=
  byRegionShift n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun i => Nat.mod (Nat.div (rotated i) 65536) 256) (fun _ => 0) binary4 (decoder 0 1 0 3)
def column5 (n : Nat) : Nat :=
  byRegionShift n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun i => Nat.mod (Nat.div (rotated i) 16777216) 256) (fun _ => 0) binary5 (decoder 0 4 0 0)
def column6 (n : Nat) : Nat :=
  byRegionShift n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) binary6
    (decoder 0 0 0 0)
def column7 (n : Nat) : Nat :=
  byRegionShift n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) binary7
    (decoder 0 0 0 0)
def column8 (n : Nat) : Nat :=
  byRegionShift n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) binary8
    (decoder 1 1 17408 1)
def column9 (n : Nat) : Nat :=
  byRegion n (fun _ => 1) (fun _ => 2) (fun _ => 3) (fun _ => 5) (fun _ => 8) (fun _ => 9) (fun _ => 34)
    (fun i => Nat.add 47 (Nat.div i 65536)) (fun _ => 51)
    (fun key => pick (Nat.blt key 65536) 52 <| pick (Nat.blt key 131072) 53 54) (fun _ => 46)

-- The kernel checks of the `omega` proofs recurse deeply on the large row numbers.
set_option maxRecDepth 100000

section Rows
open UnifiedReduced.Setup

/-! Rows of `NativeFixedRows.unified` in each native region. These lemmas rewrite with `rw` only: a `simp` rewrite
inside the row vectors leaves the kernel comparisons of different arithmetic terms, which it evaluates on the large
row numbers. -/

theorem rowWith_fixed (words : Nat → BitVec 32) (i : Fin 2097537) (h : i.val < 1048961) :
    rowWith words i = fixedRow ⟨i.val, h⟩ := by
  unfold rowWith; rw [dite_eq_left h]

theorem rowWith_rom (words : Nat → BitVec 32) (i : Fin 2097537) (h : 1048961 ≤ i.val) :
    rowWith words i = #v[4 * (i.val - 1048961), (Arithmetic.Word.ofBitVec (words (i.val - 1048961))).lo,
      (Arithmetic.Word.ofBitVec (words (i.val - 1048961))).hi, 0, 0, 0, 0, 0, 0, 34] := by
  unfold rowWith; rw [dite_eq_right (by omega)]

theorem fixed_binary (m : Nat) (h : m < 1048961) (binary : m < 524545) : fixedRow ⟨m, h⟩ = binaryRow ⟨m, binary⟩ := by
  unfold fixedRow; dsimp only; rw [dite_eq_left binary]

theorem fixed_zeroTest (m : Nat) (h : m < 1048961) (low : 524545 ≤ m) (high : m < 655617) :
    fixedRow ⟨m, h⟩ = #v[m - 524545, if m - 524545 = 0 then 1 else 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  unfold fixedRow; dsimp only; rw [dite_eq_right (by omega), ite_eq_left high]

theorem fixed_limbSign (m : Nat) (h : m < 1048961) (low : 655617 ≤ m) (high : m < 721153) :
    fixedRow ⟨m, h⟩ = #v[m - 655617, (m - 655617) / 32768, 0, 0, 0, 0, 0, 0, 0, 5] := by
  unfold fixedRow; dsimp only; rw [dite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left high]

theorem fixed_jump (m : Nat) (h : m < 1048961) (low : 721153 ≤ m) (high : m < 786689) :
    fixedRow ⟨m, h⟩ = #v[m - 721153, (m - 721153) / 2 % 2, m - 721153 - (m - 721153) % 4, 0, 0, 0, 0, 0, 0, 2] := by
  unfold fixedRow; dsimp only; rw [dite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left high]

theorem fixed_conditional (m : Nat) (h : m < 1048961) (low : 786689 ≤ m) (high : m < 786817) :
    fixedRow ⟨m, h⟩ = #v[m - 786689, Verification.conditionalValue (conditionalKey (m - 786689)), 0, 0, 0, 0, 0, 0,
      0, 51] := by
  unfold fixedRow; dsimp only
  rw [dite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left high]

theorem fixed_rotate (m : Nat) (h : m < 1048961) (low : 786817 ≤ m) :
    fixedRow ⟨m, h⟩ = rotateRow ⟨m - 786817, by omega⟩ := by
  unfold fixedRow; dsimp only
  rw [dite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega)]

end Rows

/-! The logical row of native row `n` in each region: `unifiedIndex` moves each region as a whole. -/

theorem index_zeroTest {n : Nat} (bound : n < 2097537) (low : 1 ≤ n) (high : n < 131073) :
    (unifiedIndex ⟨n, bound⟩).val = 524545 + (n - 1) := by
  simp only [unifiedIndex]; split_ifs <;> omega

theorem index_jump {n : Nat} (bound : n < 2097537) (low : 131073 ≤ n) (high : n < 196609) :
    (unifiedIndex ⟨n, bound⟩).val = 721153 + (n - 131073) := by
  simp only [unifiedIndex]; split_ifs <;> omega

theorem index_sign {n : Nat} (bound : n < 2097537) (low : 196609 ≤ n) (high : n < 196865) :
    (unifiedIndex ⟨n, bound⟩).val = 1 + (n - 196609) := by
  simp only [unifiedIndex]; split_ifs <;> omega

theorem index_limbSign {n : Nat} (bound : n < 2097537) (low : 196865 ≤ n) (high : n < 262401) :
    (unifiedIndex ⟨n, bound⟩).val = 655617 + (n - 196865) := by
  simp only [unifiedIndex]; split_ifs <;> omega

theorem index_low5 {n : Nat} (bound : n < 2097537) (low : 262401 ≤ n) (high : n < 327937) :
    (unifiedIndex ⟨n, bound⟩).val = 196865 + (n - 262401) := by
  simp only [unifiedIndex]; split_ifs <;> omega

theorem index_shift {n : Nat} (bound : n < 2097537) (low : 327937 ≤ n) (high : n < 590081) :
    (unifiedIndex ⟨n, bound⟩).val = 262401 + (n - 327937) := by
  simp only [unifiedIndex]; split_ifs <;> omega

theorem index_rom {n : Nat} (bound : n < 2097537) (low : 590081 ≤ n) (high : n < 1638657) :
    (unifiedIndex ⟨n, bound⟩).val = 1048961 + (n - 590081) := by
  simp only [unifiedIndex]; split_ifs <;> omega

theorem index_rotate {n : Nat} (bound : n < 2097537) (low : 1638657 ≤ n) (high : n < 1900801) :
    (unifiedIndex ⟨n, bound⟩).val = 786817 + (n - 1638657) := by
  simp only [unifiedIndex]; split_ifs <;> omega

theorem index_conditional {n : Nat} (bound : n < 2097537) (low : 1900801 ≤ n) (high : n < 1900929) :
    (unifiedIndex ⟨n, bound⟩).val = 786689 + (n - 1900801) := by
  simp only [unifiedIndex]; split_ifs <;> omega

theorem index_wide {n : Nat} (bound : n < 2097537) (low : 1900929 ≤ n) :
    (unifiedIndex ⟨n, bound⟩).val = 257 + (n - 1900929) := by
  simp only [unifiedIndex]; split_ifs <;> omega

theorem rotated_eq (i : Nat) (bound : i < 262144) :
    ((BitVec.ofNat 32 (i / 256 % 256 ^^^ i % 256)).rotateRight #[16, 12, 8, 7][i / 65536]!).toNat = rotated i := by
  have small : i / 256 % 256 ^^^ i % 256 < 4294967296 :=
    lt_of_lt_of_le (Nat.xor_lt_two_pow (n := 8) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))) (by decide)
  have shift : i / 65536 < 4 := by omega
  simp only [BitVec.toNat_rotateRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, rotated, rotation, nat_blt,
    pick_decide, nat_xor, nat_div, nat_mod, nat_pow, nat_mul, nat_sub, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    nat_lor]
  interval_cases h : i / 65536 <;> simp (disch := omega) [ite_eq_left, ite_eq_right]

theorem packedKey_eq (key : Nat) : packedKey key = UnifiedReduced.Setup.conditionalKey key := by
  simp only [packedKey, UnifiedReduced.Setup.conditionalKey, bit, nat_add, nat_mul, nat_mod, nat_div]
  omega

theorem rotateRow_eq (k : Nat) (h : k < 262144) :
    UnifiedReduced.Setup.rotateRow ⟨k, h⟩ = #v[k / 256 % 256, k % 256, rotated k % 256, rotated k / 256 % 256,
      rotated k / 65536 % 256, rotated k / 16777216 % 256, 0, 0, 0, 47 + k / 65536] := by
  unfold UnifiedReduced.Setup.rotateRow
  dsimp only
  rw [rotated_eq k h]

theorem romWord_eq (k : Nat) :
    (Arithmetic.Word.ofBitVec (NativeSetups.fixtureWords k)).lo = word k % 65536 ∧
      (Arithmetic.Word.ofBitVec (NativeSetups.fixtureWords k)).hi = word k / 65536 := by
  simp only [Arithmetic.Word.ofBitVec, Arithmetic.limbBase, word_eq, and_self]

/-! The unified rows in each native region, in terms of the native row. -/

section Unified
variable {n : Nat} (bound : n < 2097537)
include bound

theorem unified_zeroTest (low : 1 ≤ n) (high : n < 131073) :
    unified NativeSetups.fixtureWords ⟨n, bound⟩ = #v[n - 1, if n - 1 = 0 then 1 else 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  have index := index_zeroTest bound low high
  rw [unified, rowWith_fixed _ _ (by omega), fixed_zeroTest _ _ (by omega) (by omega), index,
    Nat.add_sub_cancel_left]

theorem unified_jump (low : 131073 ≤ n) (high : n < 196609) :
    unified NativeSetups.fixtureWords ⟨n, bound⟩ =
      #v[n - 131073, (n - 131073) / 2 % 2, n - 131073 - (n - 131073) % 4, 0, 0, 0, 0, 0, 0, 2] := by
  have index := index_jump bound low high
  rw [unified, rowWith_fixed _ _ (by omega), fixed_jump _ _ (by omega) (by omega), index, Nat.add_sub_cancel_left]

theorem unified_limbSign (low : 196865 ≤ n) (high : n < 262401) :
    unified NativeSetups.fixtureWords ⟨n, bound⟩ = #v[n - 196865, (n - 196865) / 32768, 0, 0, 0, 0, 0, 0, 0, 5] := by
  have index := index_limbSign bound low high
  rw [unified, rowWith_fixed _ _ (by omega), fixed_limbSign _ _ (by omega) (by omega), index,
    Nat.add_sub_cancel_left]

theorem unified_conditional (low : 1900801 ≤ n) (high : n < 1900929) :
    unified NativeSetups.fixtureWords ⟨n, bound⟩ = #v[n - 1900801,
      Verification.conditionalValue (UnifiedReduced.Setup.conditionalKey (n - 1900801)), 0, 0, 0, 0, 0, 0, 0, 51] := by
  have index := index_conditional bound low high
  rw [unified, rowWith_fixed _ _ (by omega), fixed_conditional _ _ (by omega) (by omega), index,
    Nat.add_sub_cancel_left]

theorem unified_rom (low : 590081 ≤ n) (high : n < 1638657) :
    unified NativeSetups.fixtureWords ⟨n, bound⟩ = #v[4 * (n - 590081), word (n - 590081) % 65536,
      word (n - 590081) / 65536, 0, 0, 0, 0, 0, 0, 34] := by
  have index := index_rom bound low high
  rw [unified, rowWith_rom _ _ (by omega), index, Nat.add_sub_cancel_left, (romWord_eq (n - 590081)).1,
    (romWord_eq (n - 590081)).2]

theorem unified_rotate (low : 1638657 ≤ n) (high : n < 1900801) :
    unified NativeSetups.fixtureWords ⟨n, bound⟩ = #v[(n - 1638657) / 256 % 256, (n - 1638657) % 256,
      rotated (n - 1638657) % 256, rotated (n - 1638657) / 256 % 256, rotated (n - 1638657) / 65536 % 256,
      rotated (n - 1638657) / 16777216 % 256, 0, 0, 0, 47 + (n - 1638657) / 65536] := by
  have index := index_rotate bound low high
  rw [unified, rowWith_fixed _ _ (by omega), fixed_rotate _ _ (by omega)]
  simp only [index, Nat.add_sub_cancel_left]
  exact rotateRow_eq _ _

theorem unified_sign (low : 196609 ≤ n) (high : n < 196865) :
    unified NativeSetups.fixtureWords ⟨n, bound⟩ = UnifiedReduced.Setup.binaryRow ⟨1 + (n - 196609), by omega⟩ := by
  have index := index_sign bound low high
  rw [unified, rowWith_fixed _ _ (by omega), fixed_binary _ _ (by omega)]
  simp only [index]

theorem unified_low5 (low : 262401 ≤ n) (high : n < 327937) :
    unified NativeSetups.fixtureWords ⟨n, bound⟩ = UnifiedReduced.Setup.binaryRow ⟨196865 + (n - 262401),
        by omega⟩ := by
  have index := index_low5 bound low high
  rw [unified, rowWith_fixed _ _ (by omega), fixed_binary _ _ (by omega)]
  simp only [index]

theorem unified_shift (low : 327937 ≤ n) (high : n < 590081) :
    unified NativeSetups.fixtureWords ⟨n, bound⟩ = UnifiedReduced.Setup.binaryRow ⟨262401 + (n - 327937),
        by omega⟩ := by
  have index := index_shift bound low high
  rw [unified, rowWith_fixed _ _ (by omega), fixed_binary _ _ (by omega)]
  simp only [index]

theorem unified_wide (low : 1900929 ≤ n) :
    unified NativeSetups.fixtureWords ⟨n, bound⟩ = UnifiedReduced.Setup.binaryRow ⟨257 + (n - 1900929), by omega⟩ := by
  have index := index_wide bound low
  rw [unified, rowWith_fixed _ _ (by omega), fixed_binary _ _ (by omega)]
  simp only [index]

end Unified

/-- The reviewed rows, as integers. -/
def fixedRow (index : Fin 2097537) : Vector Int 10 :=
  (unified NativeSetups.fixtureWords index).map (fun n : Nat => (n : Int))

/-- The entries of a row vector, as integers; with variable entries, so that the kernel checks it once. -/
theorem vector_get (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Nat) :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].map (fun n : Nat => (n : Int)))[0] = a0 ∧
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].map (fun n : Nat => (n : Int)))[1] = a1 ∧
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].map (fun n : Nat => (n : Int)))[2] = a2 ∧
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].map (fun n : Nat => (n : Int)))[3] = a3 ∧
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].map (fun n : Nat => (n : Int)))[4] = a4 ∧
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].map (fun n : Nat => (n : Int)))[5] = a5 ∧
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].map (fun n : Nat => (n : Int)))[6] = a6 ∧
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].map (fun n : Nat => (n : Int)))[7] = a7 ∧
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].map (fun n : Nat => (n : Int)))[8] = a8 ∧
    (#v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].map (fun n : Nat => (n : Int)))[9] = a9 :=
  by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
    List.getElem_cons_zero]

/-- The entries of a binary row: the shift/binary row with the wide binary tags. -/
theorem binary_get (m : Nat) (h : m < 524545) :
    ∀ k (hk : k < 9), (UnifiedReduced.Setup.binaryRow ⟨m, h⟩)[k] = (Verification.shiftBinopRow ⟨m, h⟩)[k] := by
  intro k hk
  unfold UnifiedReduced.Setup.binaryRow
  rw [Vector.getElem_set_ne _ _ (by omega)]

theorem binary_tag (m : Nat) (h : m < 524545) :
    (UnifiedReduced.Setup.binaryRow ⟨m, h⟩)[9] = UnifiedReduced.Setup.binaryTag (Verification.shiftBinopRow ⟨m,
        h⟩)[9] := by
  unfold UnifiedReduced.Setup.binaryRow
  rw [Vector.getElem_set_self]

/-! The column formulas on each native region. -/

section Columns
variable {n : Nat} (bound : n < 2097537)
include bound

theorem columns_zero (zero : n = 0) :
    (fixedRow ⟨n, bound⟩)[0] = column0 n ∧ (fixedRow ⟨n, bound⟩)[1] = column1 n ∧
    (fixedRow ⟨n, bound⟩)[2] = column2 n ∧ (fixedRow ⟨n, bound⟩)[3] = column3 n ∧
    (fixedRow ⟨n, bound⟩)[4] = column4 n ∧ (fixedRow ⟨n, bound⟩)[5] = column5 n ∧
    (fixedRow ⟨n, bound⟩)[6] = column6 n ∧ (fixedRow ⟨n, bound⟩)[7] = column7 n ∧
    (fixedRow ⟨n, bound⟩)[8] = column8 n ∧ (fixedRow ⟨n, bound⟩)[9] = column9 n := by
  subst zero
  rw [show (⟨0, bound⟩ : Fin 2097537) = ⟨0, by decide⟩ from rfl]
  decide +kernel

theorem columns_zeroTest (low : 1 ≤ n) (high : n < 131073) :
    (fixedRow ⟨n, bound⟩)[0] = column0 n ∧ (fixedRow ⟨n, bound⟩)[1] = column1 n ∧
    (fixedRow ⟨n, bound⟩)[2] = column2 n ∧ (fixedRow ⟨n, bound⟩)[3] = column3 n ∧
    (fixedRow ⟨n, bound⟩)[4] = column4 n ∧ (fixedRow ⟨n, bound⟩)[5] = column5 n ∧
    (fixedRow ⟨n, bound⟩)[6] = column6 n ∧ (fixedRow ⟨n, bound⟩)[7] = column7 n ∧
    (fixedRow ⟨n, bound⟩)[8] = column8 n ∧ (fixedRow ⟨n, bound⟩)[9] = column9 n := by
  rw [fixedRow, unified_zeroTest bound low high]
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ :=
    vector_get (n - 1) (if n - 1 = 0 then 1 else 0) 0 0 0 0 0 0 0 1
  rw [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (disch := omega) only [column0, column1, column2, column3, column4, column5, column6, column7, column8,
      column9, byRegionShift, byRegion_zeroTest, nat_beq, pick_decide]

theorem columns_jump (low : 131073 ≤ n) (high : n < 196609) :
    (fixedRow ⟨n, bound⟩)[0] = column0 n ∧ (fixedRow ⟨n, bound⟩)[1] = column1 n ∧
    (fixedRow ⟨n, bound⟩)[2] = column2 n ∧ (fixedRow ⟨n, bound⟩)[3] = column3 n ∧
    (fixedRow ⟨n, bound⟩)[4] = column4 n ∧ (fixedRow ⟨n, bound⟩)[5] = column5 n ∧
    (fixedRow ⟨n, bound⟩)[6] = column6 n ∧ (fixedRow ⟨n, bound⟩)[7] = column7 n ∧
    (fixedRow ⟨n, bound⟩)[8] = column8 n ∧ (fixedRow ⟨n, bound⟩)[9] = column9 n := by
  rw [fixedRow, unified_jump bound low high]
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ :=
    vector_get (n - 131073) ((n - 131073) / 2 % 2) (n - 131073 - (n - 131073) % 4) 0 0 0 0 0 0 2
  rw [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (disch := omega) only [column0, column1, column2, column3, column4, column5, column6, column7, column8,
      column9, byRegionShift, byRegion_jump, bit, nat_div, nat_mod, nat_sub]

theorem columns_limbSign (low : 196865 ≤ n) (high : n < 262401) :
    (fixedRow ⟨n, bound⟩)[0] = column0 n ∧ (fixedRow ⟨n, bound⟩)[1] = column1 n ∧
    (fixedRow ⟨n, bound⟩)[2] = column2 n ∧ (fixedRow ⟨n, bound⟩)[3] = column3 n ∧
    (fixedRow ⟨n, bound⟩)[4] = column4 n ∧ (fixedRow ⟨n, bound⟩)[5] = column5 n ∧
    (fixedRow ⟨n, bound⟩)[6] = column6 n ∧ (fixedRow ⟨n, bound⟩)[7] = column7 n ∧
    (fixedRow ⟨n, bound⟩)[8] = column8 n ∧ (fixedRow ⟨n, bound⟩)[9] = column9 n := by
  rw [fixedRow, unified_limbSign bound low high]
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ :=
    vector_get (n - 196865) ((n - 196865) / 32768) 0 0 0 0 0 0 0 5
  rw [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (disch := omega) only [column0, column1, column2, column3, column4, column5, column6, column7, column8,
      column9, byRegionShift, byRegion_limbSign, nat_div]

theorem columns_rom (low : 590081 ≤ n) (high : n < 1638657) :
    (fixedRow ⟨n, bound⟩)[0] = column0 n ∧ (fixedRow ⟨n, bound⟩)[1] = column1 n ∧
    (fixedRow ⟨n, bound⟩)[2] = column2 n ∧ (fixedRow ⟨n, bound⟩)[3] = column3 n ∧
    (fixedRow ⟨n, bound⟩)[4] = column4 n ∧ (fixedRow ⟨n, bound⟩)[5] = column5 n ∧
    (fixedRow ⟨n, bound⟩)[6] = column6 n ∧ (fixedRow ⟨n, bound⟩)[7] = column7 n ∧
    (fixedRow ⟨n, bound⟩)[8] = column8 n ∧ (fixedRow ⟨n, bound⟩)[9] = column9 n := by
  rw [fixedRow, unified_rom bound low high]
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ :=
    vector_get (4 * (n - 590081)) (word (n - 590081) % 65536) (word (n - 590081) / 65536) 0 0 0 0 0 0 34
  rw [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (disch := omega) only [column0, column1, column2, column3, column4, column5, column6, column7, column8,
      column9, byRegionShift, byRegion_rom, nat_mul, nat_div, nat_mod]

theorem columns_rotate (low : 1638657 ≤ n) (high : n < 1900801) :
    (fixedRow ⟨n, bound⟩)[0] = column0 n ∧ (fixedRow ⟨n, bound⟩)[1] = column1 n ∧
    (fixedRow ⟨n, bound⟩)[2] = column2 n ∧ (fixedRow ⟨n, bound⟩)[3] = column3 n ∧
    (fixedRow ⟨n, bound⟩)[4] = column4 n ∧ (fixedRow ⟨n, bound⟩)[5] = column5 n ∧
    (fixedRow ⟨n, bound⟩)[6] = column6 n ∧ (fixedRow ⟨n, bound⟩)[7] = column7 n ∧
    (fixedRow ⟨n, bound⟩)[8] = column8 n ∧ (fixedRow ⟨n, bound⟩)[9] = column9 n := by
  rw [fixedRow, unified_rotate bound low high]
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ :=
    vector_get ((n - 1638657) / 256 % 256) ((n - 1638657) % 256) (rotated (n - 1638657) % 256)
    (rotated (n - 1638657) / 256 % 256) (rotated (n - 1638657) / 65536 % 256)
    (rotated (n - 1638657) / 16777216 % 256) 0 0 0 (47 + (n - 1638657) / 65536)
  rw [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (disch := omega) only [column0, column1, column2, column3, column4, column5, column6, column7, column8,
      column9, byRegionShift, byRegion_rotate, nat_add, nat_div, nat_mod]

theorem columns_conditional (low : 1900801 ≤ n) (high : n < 1900929) :
    (fixedRow ⟨n, bound⟩)[0] = column0 n ∧ (fixedRow ⟨n, bound⟩)[1] = column1 n ∧
    (fixedRow ⟨n, bound⟩)[2] = column2 n ∧ (fixedRow ⟨n, bound⟩)[3] = column3 n ∧
    (fixedRow ⟨n, bound⟩)[4] = column4 n ∧ (fixedRow ⟨n, bound⟩)[5] = column5 n ∧
    (fixedRow ⟨n, bound⟩)[6] = column6 n ∧ (fixedRow ⟨n, bound⟩)[7] = column7 n ∧
    (fixedRow ⟨n, bound⟩)[8] = column8 n ∧ (fixedRow ⟨n, bound⟩)[9] = column9 n := by
  rw [fixedRow, unified_conditional bound low high]
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ :=
    vector_get (n - 1900801) (Verification.conditionalValue (UnifiedReduced.Setup.conditionalKey (n - 1900801)))
      0 0 0 0 0 0 0 51
  rw [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (disch := omega) only [column0, column1, column2, column3, column4, column5, column6, column7, column8,
      column9, byRegionShift, byRegion_conditional, ← conditional_eq, ← packedKey_eq]

theorem columns_sign (low : 196609 ≤ n) (high : n < 196865) :
    (fixedRow ⟨n, bound⟩)[0] = column0 n ∧ (fixedRow ⟨n, bound⟩)[1] = column1 n ∧
    (fixedRow ⟨n, bound⟩)[2] = column2 n ∧ (fixedRow ⟨n, bound⟩)[3] = column3 n ∧
    (fixedRow ⟨n, bound⟩)[4] = column4 n ∧ (fixedRow ⟨n, bound⟩)[5] = column5 n ∧
    (fixedRow ⟨n, bound⟩)[6] = column6 n ∧ (fixedRow ⟨n, bound⟩)[7] = column7 n ∧
    (fixedRow ⟨n, bound⟩)[8] = column8 n ∧ (fixedRow ⟨n, bound⟩)[9] = column9 n := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ :=
    Verification.ShiftBinopSetupProofs.column_eq (1 + (n - 196609)) (by omega)
  simp only [Verification.ShiftBinopSetupProofs.fixedRow, Vector.getElem_map] at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
  rw [fixedRow, unified_sign bound low high]
  simp only [Vector.getElem_map]
  rw [binary_get _ _ 0 (by decide), binary_get _ _ 1 (by decide), binary_get _ _ 2 (by decide),
    binary_get _ _ 3 (by decide), binary_get _ _ 4 (by decide), binary_get _ _ 5 (by decide),
    binary_get _ _ 6 (by decide), binary_get _ _ 7 (by decide), binary_get _ _ 8 (by decide), binary_tag,
    s0, s1, s2, s3, s4, s5, s6, s7, s8, Int.natCast_inj.mp s9]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (disch := omega) only [column0, column1, column2, column3, column4, column5, column6, column7, column8,
      column9, byRegionShift, byRegion_sign, nat_add, binary9,
    Verification.ShiftBinopSetupProofs.byRegion, UnifiedReduced.Setup.binaryTag, nat_blt, nat_beq, pick_true,
    pick_false, pick_decide, nat_sub, Nat.reduceEqDiff, ↓reduceIte]

theorem columns_low5 (low : 262401 ≤ n) (high : n < 327937) :
    (fixedRow ⟨n, bound⟩)[0] = column0 n ∧ (fixedRow ⟨n, bound⟩)[1] = column1 n ∧
    (fixedRow ⟨n, bound⟩)[2] = column2 n ∧ (fixedRow ⟨n, bound⟩)[3] = column3 n ∧
    (fixedRow ⟨n, bound⟩)[4] = column4 n ∧ (fixedRow ⟨n, bound⟩)[5] = column5 n ∧
    (fixedRow ⟨n, bound⟩)[6] = column6 n ∧ (fixedRow ⟨n, bound⟩)[7] = column7 n ∧
    (fixedRow ⟨n, bound⟩)[8] = column8 n ∧ (fixedRow ⟨n, bound⟩)[9] = column9 n := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ :=
    Verification.ShiftBinopSetupProofs.column_eq (196865 + (n - 262401)) (by omega)
  simp only [Verification.ShiftBinopSetupProofs.fixedRow, Vector.getElem_map] at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
  rw [fixedRow, unified_low5 bound low high]
  simp only [Vector.getElem_map]
  rw [binary_get _ _ 0 (by decide), binary_get _ _ 1 (by decide), binary_get _ _ 2 (by decide),
    binary_get _ _ 3 (by decide), binary_get _ _ 4 (by decide), binary_get _ _ 5 (by decide),
    binary_get _ _ 6 (by decide), binary_get _ _ 7 (by decide), binary_get _ _ 8 (by decide), binary_tag,
    s0, s1, s2, s3, s4, s5, s6, s7, s8, Int.natCast_inj.mp s9]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (disch := omega) only [column0, column1, column2, column3, column4, column5, column6, column7, column8,
      column9, byRegionShift, byRegion_low5, nat_add, binary9,
    Verification.ShiftBinopSetupProofs.byRegion, UnifiedReduced.Setup.binaryTag, nat_blt, nat_beq, pick_true,
    pick_false, pick_decide, nat_sub, Nat.reduceEqDiff, ↓reduceIte]

theorem columns_shift (low : 327937 ≤ n) (high : n < 590081) :
    (fixedRow ⟨n, bound⟩)[0] = column0 n ∧ (fixedRow ⟨n, bound⟩)[1] = column1 n ∧
    (fixedRow ⟨n, bound⟩)[2] = column2 n ∧ (fixedRow ⟨n, bound⟩)[3] = column3 n ∧
    (fixedRow ⟨n, bound⟩)[4] = column4 n ∧ (fixedRow ⟨n, bound⟩)[5] = column5 n ∧
    (fixedRow ⟨n, bound⟩)[6] = column6 n ∧ (fixedRow ⟨n, bound⟩)[7] = column7 n ∧
    (fixedRow ⟨n, bound⟩)[8] = column8 n ∧ (fixedRow ⟨n, bound⟩)[9] = column9 n := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ :=
    Verification.ShiftBinopSetupProofs.column_eq (262401 + (n - 327937)) (by omega)
  simp only [Verification.ShiftBinopSetupProofs.fixedRow, Vector.getElem_map] at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
  rw [fixedRow, unified_shift bound low high]
  simp only [Vector.getElem_map]
  rw [binary_get _ _ 0 (by decide), binary_get _ _ 1 (by decide), binary_get _ _ 2 (by decide),
    binary_get _ _ 3 (by decide), binary_get _ _ 4 (by decide), binary_get _ _ 5 (by decide),
    binary_get _ _ 6 (by decide), binary_get _ _ 7 (by decide), binary_get _ _ 8 (by decide), binary_tag,
    s0, s1, s2, s3, s4, s5, s6, s7, s8, Int.natCast_inj.mp s9]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (disch := omega) only [column0, column1, column2, column3, column4, column5, column6, column7, column8,
      column9, byRegionShift, byRegion_shift, nat_add, binary9,
    Verification.ShiftBinopSetupProofs.byRegion, UnifiedReduced.Setup.binaryTag, nat_blt, nat_beq, pick_true,
    pick_false, pick_decide, nat_sub, Nat.reduceEqDiff, ↓reduceIte]

theorem columns_wide (low : 1900929 ≤ n) :
    (fixedRow ⟨n, bound⟩)[0] = column0 n ∧ (fixedRow ⟨n, bound⟩)[1] = column1 n ∧
    (fixedRow ⟨n, bound⟩)[2] = column2 n ∧ (fixedRow ⟨n, bound⟩)[3] = column3 n ∧
    (fixedRow ⟨n, bound⟩)[4] = column4 n ∧ (fixedRow ⟨n, bound⟩)[5] = column5 n ∧
    (fixedRow ⟨n, bound⟩)[6] = column6 n ∧ (fixedRow ⟨n, bound⟩)[7] = column7 n ∧
    (fixedRow ⟨n, bound⟩)[8] = column8 n ∧ (fixedRow ⟨n, bound⟩)[9] = column9 n := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ :=
    Verification.ShiftBinopSetupProofs.column_eq (257 + (n - 1900929)) (by omega)
  simp only [Verification.ShiftBinopSetupProofs.fixedRow, Vector.getElem_map] at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
  rw [fixedRow, unified_wide bound low]
  simp only [Vector.getElem_map]
  rw [binary_get _ _ 0 (by decide), binary_get _ _ 1 (by decide), binary_get _ _ 2 (by decide),
    binary_get _ _ 3 (by decide), binary_get _ _ 4 (by decide), binary_get _ _ 5 (by decide),
    binary_get _ _ 6 (by decide), binary_get _ _ 7 (by decide), binary_get _ _ 8 (by decide), binary_tag,
    s0, s1, s2, s3, s4, s5, s6, s7, s8, Int.natCast_inj.mp s9]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (disch := omega) only [column0, column1, column2, column3, column4, column5, column6, column7, column8,
      column9, byRegionShift, byRegion_wide, nat_add, binary9,
    Verification.ShiftBinopSetupProofs.byRegion, UnifiedReduced.Setup.binaryTag, nat_blt, nat_beq, pick_true,
    pick_false, pick_decide, nat_sub]
  all_goals split_ifs <;> first | rfl | omega

end Columns

theorem column_eq (n : Nat) (bound : n < 2097537) :
    (fixedRow ⟨n, bound⟩)[0] = column0 n ∧ (fixedRow ⟨n, bound⟩)[1] = column1 n ∧
    (fixedRow ⟨n, bound⟩)[2] = column2 n ∧ (fixedRow ⟨n, bound⟩)[3] = column3 n ∧
    (fixedRow ⟨n, bound⟩)[4] = column4 n ∧ (fixedRow ⟨n, bound⟩)[5] = column5 n ∧
    (fixedRow ⟨n, bound⟩)[6] = column6 n ∧ (fixedRow ⟨n, bound⟩)[7] = column7 n ∧
    (fixedRow ⟨n, bound⟩)[8] = column8 n ∧ (fixedRow ⟨n, bound⟩)[9] = column9 n := by
  by_cases r0 : n = 0
  · exact columns_zero bound r0
  by_cases r1 : n < 131073
  · exact columns_zeroTest bound (by omega) r1
  by_cases r2 : n < 196609
  · exact columns_jump bound (by omega) r2
  by_cases r3 : n < 196865
  · exact columns_sign bound (by omega) r3
  by_cases r4 : n < 262401
  · exact columns_limbSign bound (by omega) r4
  by_cases r5 : n < 327937
  · exact columns_low5 bound (by omega) r5
  by_cases r6 : n < 590081
  · exact columns_shift bound (by omega) r6
  by_cases r7 : n < 1638657
  · exact columns_rom bound (by omega) r7
  by_cases r8 : n < 1900801
  · exact columns_rotate bound (by omega) r8
  by_cases r9 : n < 1900929
  · exact columns_conditional bound (by omega) r9
  · exact columns_wide bound (by omega)

-- One simp set serves every column; each column uses a part of it.
set_option linter.unusedSimpArgs false in
/-- Rows from 2097537: the decoder rows of the setup fixture, then zero padding. -/
theorem column_after (n : Nat) (low : 2097537 ≤ n) (c : Fin 10) :
    ((if n < 3146113 then unifiedFixtureDecoderRow (n - 2097537) else Vector.replicate 10 0 : Vector Int 10))[c] =
      (![column0, column1, column2, column3, column4, column5, column6, column7, column8, column9] c n : Int) := by
  by_cases decoderRow : n < 3146113
  · by_cases zero : n = 2097537
    · subst zero; fin_cases c <;> rfl
    by_cases one : n = 2097538
    · subst one; fin_cases c <;> rfl
    by_cases two : n = 2097539
    · subst two; fin_cases c <;> rfl
    by_cases three : n = 2097540
    · subst three; fin_cases c <;> rfl
    fin_cases c <;>
    simp (disch := omega) only [decoderRow, ↓reduceIte, unifiedFixtureDecoderRow, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val, column0, column1, column2, column3, column4, column5, column6, column7,
          column8, column9, byRegionShift, byRegion_decoder, decoder, nat_beq, pick_false,
      Vector.getElem_push_eq, Vector.getElem_push_lt, Vector.getElem_replicate] <;>
    split_ifs <;> first | omega | simp [babyBearModulus]
  · fin_cases c <;>
    simp (disch := omega) only [decoderRow, ↓reduceIte, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
      column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, byRegionShift,
          byRegion_padding, Vector.getElem_replicate, Nat.cast_zero] <;>
    rfl

end Airbender.Compiler.NativeFixedRows.UnifiedSetupProofs
