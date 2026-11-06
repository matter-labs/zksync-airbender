import Human.Circuits.JumpBranchSlt.Artifact
import Human.Circuits.JumpBranchSlt.Tables.Control
import Human.Helpers.Core.BabyBearPrime
import Slop.Constraints
import Slop.Trace.Timestamps
import Slop.JumpBranchSlt.Completeness.Attr
import Mathlib.Tactic.LinearCombination

/-! Completeness of the standalone JumpBranchSlt circuit (lean-strategies §2.4): the honest
    assignment computed from the operands satisfies every retained equation, range query and
    fixed-table query (`complete`), and with ordered previous clocks also the eight native
    timestamp queries (`clock_complete`). Proved once, symbolically; only the selector and
    destination cases are split. Witness tests check their input facts and that their rows
    agree with the honest assignment on the constrained columns (`complete_of_agree`).

    The clock part mirrors `UnifiedReduced.Completeness.Frame` under this circuit's column
    layout. It is not reused: that module is stated over the unified artifact's columns, its
    `Clock`/`Valid` bounds the incremented PC (false for this circuit's wrapping jumps), and its
    port lemmas are private. -/

namespace Airbender.JumpBranchSlt.Completeness
open Verification
set_option warningAsError true

/-- Inputs of one honest row. `sel` is 0 (JAL), 1 (JALR), 2 (comparison) or 3 (branch);
    `rdZero` marks a discarded destination; `imm*` are the decoder's immediate limbs, `a*`/`b*`
    the two register operands, `old*` the destination's previous value. `ts*` is the row clock,
    `prevK*` the previous access clock of memory port `K`, and `borrowK` that port's low-limb
    comparison borrow (only Boolean for `complete`; computed for `clock_complete`). -/
structure Inputs where
  sel : Nat
  rdZero : Bool
  funct3 : Nat
  rs1 : Nat
  rs2 : Nat
  rd : Nat
  pcLo : Nat
  pcHi : Nat
  aLo : Nat
  aHi : Nat
  bLo : Nat
  bHi : Nat
  immLo : Nat
  immHi : Nat
  oldLo : Nat
  oldHi : Nat
  tsLo : Nat
  tsHi : Nat
  prev0Lo : Nat
  prev0Hi : Nat
  prev1Lo : Nat
  prev1Hi : Nat
  prev2Lo : Nat
  prev2Hi : Nat
  borrow0 : Nat
  borrow1 : Nat
  borrow2 : Nat

/-- Borrow of the low-limb comparison of a previous clock against `ts + k`. -/
def borrow (prevLo tsLo k : Nat) : Nat := if prevLo < tsLo + k then 1 else 0

namespace Inputs

def isSel (x : Inputs) (k : Nat) : Nat := if x.sel = k then 1 else 0
def rdZeroN (x : Inputs) : Nat := if x.rdZero then 1 else 0
/-- Second comparison operand: register plus immediate (one of them is zero). -/
def op2Lo (x : Inputs) : Nat := x.bLo + if x.sel = 2 then x.immLo else 0
def op2Hi (x : Inputs) : Nat := x.bHi + if x.sel = 2 then x.immHi else 0
/-- Limbs of the return address (jumps) or of the operand difference, with their carries. -/
def carryLo (x : Inputs) : Nat :=
  if x.sel ≤ 1 then (x.pcLo + 4) / 65536 else if x.aLo < x.op2Lo then 1 else 0
def diffLo (x : Inputs) : Nat :=
  if x.sel ≤ 1 then (x.pcLo + 4) % 65536 else x.aLo + 65536 * x.carryLo - x.op2Lo
def carryHi (x : Inputs) : Nat :=
  if x.sel ≤ 1 then (x.pcHi + x.carryLo) / 65536
  else if x.aHi < x.op2Hi + x.carryLo then 1 else 0
def diffHi (x : Inputs) : Nat :=
  if x.sel ≤ 1 then (x.pcHi + x.carryLo) % 65536
  else x.aHi + 65536 * x.carryHi - x.op2Hi - x.carryLo
def zero (x : Inputs) : Nat := if x.diffLo + x.diffHi = 0 then 1 else 0
def sign (x : Inputs) : Nat := x.aHi / 32768
def key (x : Inputs) : Nat :=
  x.op2Hi + 65536 * x.sign + 131072 * x.carryHi + 262144 * x.zero + 524288 * x.funct3
/-- The resolved condition, in the fixed table's own form. -/
def flag (x : Inputs) : Nat := conditionalValue x.key
def taken (x : Inputs) : Nat := if x.sel = 3 then x.flag else 0
def targetLo (x : Inputs) : Nat :=
  if x.sel = 0 then x.pcLo + x.immLo else if x.sel = 1 then x.aLo + x.immLo
  else if x.taken = 1 then x.pcLo + x.immLo else x.pcLo + 4
def nextLo (x : Inputs) : Nat := x.targetLo % 65536
def carryNext (x : Inputs) : Nat := x.targetLo / 65536
def targetHi (x : Inputs) : Nat :=
  (if x.sel = 0 then x.pcHi + x.immHi else if x.sel = 1 then x.aHi + x.immHi
    else x.pcHi + x.taken * x.immHi) + x.carryNext
def nextHi (x : Inputs) : Nat := x.targetHi % 65536
def carryHiNext (x : Inputs) : Nat := x.targetHi / 65536
def misaligned (x : Inputs) : Nat := x.nextLo / 2 % 2
def aligned (x : Inputs) : Nat := x.nextLo - x.nextLo % 4
/-- Destination value before the discard. -/
def writeLo (x : Inputs) : Nat := if x.sel ≤ 1 then x.diffLo else if x.sel = 2 then x.flag else 0
def writeHi (x : Inputs) : Nat := if x.sel ≤ 1 then x.diffHi else 0
def outLo (x : Inputs) : Nat := if x.rdZero then 0 else x.writeLo
def outHi (x : Inputs) : Nat := if x.rdZero then 0 else x.writeHi
def tsCarry (x : Inputs) : Nat := (x.tsLo + 4) / 524288
def finalTsLo (x : Inputs) : Nat := (x.tsLo + 4) % 524288
def finalTsHi (x : Inputs) : Nat := x.tsHi + x.tsCarry

/-- Range conditions of an honest row. -/
structure Valid (x : Inputs) : Prop where
  sel : x.sel ≤ 3
  funct3 : x.funct3 < 8
  pcLo : x.pcLo < 65536
  pcHi : x.pcHi < 65536
  aLo : x.aLo < 65536
  aHi : x.aHi < 65536
  immLo : x.immLo < 65536
  immHi : x.immHi < 65536
  op2Lo : x.op2Lo < 65536
  op2Hi : x.op2Hi < 65536
  tsLo : x.tsLo < 524288
  borrow0 : x.borrow0 ≤ 1
  borrow1 : x.borrow1 ≤ 1
  borrow2 : x.borrow2 ≤ 1
  aligned : x.sel ≤ 1 ∨ x.taken = 1 → x.misaligned = 0

/-- Clock conditions for the timestamp queries: no clock overflow, every previous port access
    strictly before its in-row clock, and the borrows computed from them. -/
structure Clocked (x : Inputs) : Prop where
  tsLo : x.tsLo + 2 < 524288
  tsHi : x.finalTsHi < 524288
  prev0Lo : x.prev0Lo < 524288
  prev1Lo : x.prev1Lo < 524288
  prev2Lo : x.prev2Lo < 524288
  prev0 : x.prev0Hi * 524288 + x.prev0Lo < x.tsHi * 524288 + x.tsLo
  prev1 : x.prev1Hi * 524288 + x.prev1Lo < x.tsHi * 524288 + x.tsLo + 1
  prev2 : x.prev2Hi * 524288 + x.prev2Lo < x.tsHi * 524288 + x.tsLo + 2
  borrow0 : x.borrow0 = borrow x.prev0Lo x.tsLo 0
  borrow1 : x.borrow1 = borrow x.prev1Lo x.tsLo 1
  borrow2 : x.borrow2 = borrow x.prev2Lo x.tsLo 2

/-- The honest witness columns of a row. -/
def honest (x : Inputs) : Nat → ZMod babyBearModulus
  | 0 => (x.pcLo : Nat) | 1 => (x.pcHi : Nat) | 2 => (x.tsLo : Nat) | 3 => (x.tsHi : Nat)
  | 4 => 1
  | 5 => (x.rs1 : Nat) | 6 => (x.rs2 : Nat) | 7 => (x.rd : Nat)
  | 8 => (x.immLo : Nat) | 9 => (x.immHi : Nat) | 10 => (x.funct3 : Nat)
  | 11 => (x.isSel 0 : Nat) | 12 => (x.isSel 1 : Nat) | 13 => (x.isSel 2 : Nat)
  | 14 => (x.isSel 3 : Nat) | 15 => (x.rdZeroN : Nat)
  | 16 => (x.aligned : Nat) | 17 => (x.nextHi : Nat)
  | 18 => (x.finalTsLo : Nat) | 19 => (x.finalTsHi : Nat)
  | 20 => (x.prev0Lo : Nat) | 21 => (x.prev0Hi : Nat)
  | 22 => (x.aLo : Nat) | 23 => (x.aHi : Nat)
  | 24 => (x.prev1Lo : Nat) | 25 => (x.prev1Hi : Nat)
  | 26 => (x.bLo : Nat) | 27 => (x.bHi : Nat)
  | 28 => (x.oldLo : Nat) | 29 => (x.oldHi : Nat)
  | 30 => (x.outLo : Nat) | 31 => (x.outHi : Nat)
  | 32 => (x.prev2Lo : Nat) | 33 => (x.prev2Hi : Nat)
  | 34 => (x.diffLo : Nat) | 35 => (x.diffHi : Nat)
  | 36 => (x.nextLo : Nat)
  | 37 => (x.carryLo : Nat) | 38 => (x.carryHi : Nat)
  | 39 => (x.carryNext : Nat) | 40 => (x.carryHiNext : Nat)
  | 41 => (x.zero : Nat) | 42 => (x.sign : Nat) | 43 => (x.op2Hi : Nat)
  | 44 => (x.flag : Nat) | 45 => (x.taken : Nat) | 46 => (x.misaligned : Nat)
  | 47 => (x.writeLo : Nat) | 48 => (x.writeHi : Nat)
  | 49 => (x.borrow0 : Nat) | 50 => (x.borrow1 : Nat) | 51 => (x.borrow2 : Nat)
  | _ => 0

-- BEGIN generated columns
-- generated: one rfl lemma per column (keeps `simp` off the column match)
@[jbs_honest] theorem col_0 (x : Inputs) : x.honest 0 = ((x.pcLo : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_1 (x : Inputs) : x.honest 1 = ((x.pcHi : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_2 (x : Inputs) : x.honest 2 = ((x.tsLo : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_3 (x : Inputs) : x.honest 3 = ((x.tsHi : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_4 (x : Inputs) : x.honest 4 = (1 : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_5 (x : Inputs) : x.honest 5 = ((x.rs1 : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_6 (x : Inputs) : x.honest 6 = ((x.rs2 : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_7 (x : Inputs) : x.honest 7 = ((x.rd : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_8 (x : Inputs) : x.honest 8 = ((x.immLo : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_9 (x : Inputs) : x.honest 9 = ((x.immHi : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_10 (x : Inputs) : x.honest 10 = ((x.funct3 : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_11 (x : Inputs) : x.honest 11 = ((x.isSel 0 : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_12 (x : Inputs) : x.honest 12 = ((x.isSel 1 : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_13 (x : Inputs) : x.honest 13 = ((x.isSel 2 : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_14 (x : Inputs) : x.honest 14 = ((x.isSel 3 : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_15 (x : Inputs) : x.honest 15 = ((x.rdZeroN : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_16 (x : Inputs) : x.honest 16 = ((x.aligned : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_17 (x : Inputs) : x.honest 17 = ((x.nextHi : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_18 (x : Inputs) : x.honest 18 = ((x.finalTsLo : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_19 (x : Inputs) : x.honest 19 = ((x.finalTsHi : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_20 (x : Inputs) : x.honest 20 = ((x.prev0Lo : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_21 (x : Inputs) : x.honest 21 = ((x.prev0Hi : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_22 (x : Inputs) : x.honest 22 = ((x.aLo : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_23 (x : Inputs) : x.honest 23 = ((x.aHi : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_24 (x : Inputs) : x.honest 24 = ((x.prev1Lo : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_25 (x : Inputs) : x.honest 25 = ((x.prev1Hi : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_26 (x : Inputs) : x.honest 26 = ((x.bLo : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_27 (x : Inputs) : x.honest 27 = ((x.bHi : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_28 (x : Inputs) : x.honest 28 = ((x.oldLo : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_29 (x : Inputs) : x.honest 29 = ((x.oldHi : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_30 (x : Inputs) : x.honest 30 = ((x.outLo : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_31 (x : Inputs) : x.honest 31 = ((x.outHi : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_32 (x : Inputs) : x.honest 32 = ((x.prev2Lo : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_33 (x : Inputs) : x.honest 33 = ((x.prev2Hi : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_34 (x : Inputs) : x.honest 34 = ((x.diffLo : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_35 (x : Inputs) : x.honest 35 = ((x.diffHi : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_36 (x : Inputs) : x.honest 36 = ((x.nextLo : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_37 (x : Inputs) : x.honest 37 = ((x.carryLo : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_38 (x : Inputs) : x.honest 38 = ((x.carryHi : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_39 (x : Inputs) : x.honest 39 = ((x.carryNext : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_40 (x : Inputs) : x.honest 40 = ((x.carryHiNext : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_41 (x : Inputs) : x.honest 41 = ((x.zero : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_42 (x : Inputs) : x.honest 42 = ((x.sign : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_43 (x : Inputs) : x.honest 43 = ((x.op2Hi : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_44 (x : Inputs) : x.honest 44 = ((x.flag : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_45 (x : Inputs) : x.honest 45 = ((x.taken : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_46 (x : Inputs) : x.honest 46 = ((x.misaligned : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_47 (x : Inputs) : x.honest 47 = ((x.writeLo : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_48 (x : Inputs) : x.honest 48 = ((x.writeHi : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_49 (x : Inputs) : x.honest 49 = ((x.borrow0 : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_50 (x : Inputs) : x.honest 50 = ((x.borrow1 : Nat) : ZMod babyBearModulus) := rfl
@[jbs_honest] theorem col_51 (x : Inputs) : x.honest 51 = ((x.borrow2 : Nat) : ZMod babyBearModulus) := rfl
-- END generated columns

/-! ### Arithmetic facts of the honest columns -/

theorem cast_mod (n d : Nat) :
    ((n % d : Nat) : ZMod babyBearModulus) = (n : ZMod babyBearModulus) - (d : Nat) * ((n / d : Nat) : ZMod babyBearModulus) := by
  have h := congrArg (Nat.cast : Nat → ZMod babyBearModulus) (Nat.mod_add_div n d)
  push_cast at h ⊢
  linear_combination h

theorem bool_of_le {n : Nat} (h : n ≤ 1) :
    (n : ZMod babyBearModulus) * ((n : ZMod babyBearModulus) - 1) = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl <;> simp

/-- Normal form of imported constants: `Int.ofNat`/`Int.negSucc` casts become numerals. -/
theorem cast_ofNat (n : Nat) : ((Int.ofNat n : Int) : ZMod babyBearModulus) = (n : ZMod babyBearModulus) := by
  simp
theorem cast_negSucc (n : Nat) :
    ((Int.negSucc n : Int) : ZMod babyBearModulus) = -((n + 1 : Nat) : ZMod babyBearModulus) := by
  simp [Int.cast_negSucc]

theorem isSel_le (x : Inputs) (k : Nat) : x.isSel k ≤ 1 := by unfold isSel; split <;> omega
theorem rdZeroN_le (x : Inputs) : x.rdZeroN ≤ 1 := by unfold rdZeroN; split <;> omega

theorem flag_le (x : Inputs) : x.flag ≤ 1 := by
  simp only [flag, conditionalValue]; split_ifs <;> omega

theorem taken_le (x : Inputs) : x.taken ≤ 1 := by
  unfold taken; split
  · exact x.flag_le
  · omega

theorem carryLo_le {x : Inputs} (hx : x.Valid) : x.carryLo ≤ 1 := by
  have := hx.pcLo; unfold carryLo; split
  · omega
  · split <;> omega

theorem carryHi_le {x : Inputs} (hx : x.Valid) : x.carryHi ≤ 1 := by
  have := hx.pcHi; have := carryLo_le hx
  unfold carryHi; split
  · omega
  · split <;> omega

theorem diffLo_lt {x : Inputs} (hx : x.Valid) : x.diffLo < 65536 := by
  have := hx.op2Lo; have := hx.aLo
  unfold diffLo carryLo; split
  · exact Nat.mod_lt _ (by decide)
  · split <;> omega

theorem diffHi_lt {x : Inputs} (hx : x.Valid) : x.diffHi < 65536 := by
  have := hx.op2Hi; have := hx.aHi; have := carryLo_le hx
  unfold diffHi carryHi; split
  · exact Nat.mod_lt _ (by decide)
  · split <;> omega

theorem carryNext_le {x : Inputs} (hx : x.Valid) : x.carryNext ≤ 1 := by
  have := hx.pcLo; have := hx.aLo; have := hx.immLo
  unfold carryNext targetLo; split
  · omega
  · split
    · omega
    · split <;> omega

theorem carryHiNext_le {x : Inputs} (hx : x.Valid) : x.carryHiNext ≤ 1 := by
  have := hx.pcHi; have := hx.aHi; have := hx.immHi; have := carryNext_le hx
  have : x.taken * x.immHi ≤ x.immHi := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp x.taken_le with e | e <;> simp [e]
  unfold carryHiNext targetHi; split
  · omega
  · split <;> omega

theorem diffLo_jump (x : Inputs) (h : x.sel ≤ 1) :
    (x.diffLo : ZMod babyBearModulus) = (x.pcLo : Nat) + 4 - 65536 * (x.carryLo : Nat) := by
  simp only [diffLo, carryLo, h, ↓reduceIte, cast_mod]; push_cast; ring

theorem diffHi_jump (x : Inputs) (h : x.sel ≤ 1) :
    (x.diffHi : ZMod babyBearModulus) = (x.pcHi : Nat) + (x.carryLo : Nat) - 65536 * (x.carryHi : Nat) := by
  simp only [diffHi, carryHi, h, ↓reduceIte, cast_mod]; push_cast; ring

theorem diffLo_cond {x : Inputs} (hx : x.Valid) (h : ¬ x.sel ≤ 1) :
    (x.diffLo : ZMod babyBearModulus) = (x.aLo : Nat) + 65536 * (x.carryLo : Nat) - (x.op2Lo : Nat) := by
  have := hx.op2Lo; have := hx.aLo
  simp only [diffLo, carryLo, h, ↓reduceIte]
  split <;> (rw [Nat.cast_sub (by omega)]; push_cast; ring)

theorem diffHi_cond {x : Inputs} (hx : x.Valid) (h : ¬ x.sel ≤ 1) :
    (x.diffHi : ZMod babyBearModulus) =
      (x.aHi : Nat) + 65536 * (x.carryHi : Nat) - (x.op2Hi : Nat) - (x.carryLo : Nat) := by
  have := hx.op2Hi; have := hx.aHi; have := carryLo_le hx
  simp only [diffHi, carryHi, h, ↓reduceIte]
  split <;> (rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring)

theorem nextLo_eq (x : Inputs) :
    (x.nextLo : ZMod babyBearModulus) = (x.targetLo : Nat) - 65536 * (x.carryNext : Nat) := by
  simp only [nextLo, carryNext, cast_mod]; push_cast; ring

theorem nextHi_eq (x : Inputs) :
    (x.nextHi : ZMod babyBearModulus) = (x.targetHi : Nat) - 65536 * (x.carryHiNext : Nat) := by
  simp only [nextHi, carryHiNext, cast_mod]; push_cast; ring

theorem targetLo_branch (x : Inputs) (h : x.sel = 3) :
    (x.targetLo : ZMod babyBearModulus) =
      (x.pcLo : Nat) + 4 + (x.taken : Nat) * ((x.immLo : Nat) - 4) := by
  have := x.taken_le
  simp only [targetLo, h, Nat.reduceEqDiff, ↓reduceIte]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with e | e <;> simp only [e, ↓reduceIte,
    Nat.reduceEqDiff] <;> push_cast <;> ring

theorem key_eq (x : Inputs) :
    (x.key : ZMod babyBearModulus) = (x.op2Hi : Nat) + 65536 * ((x.sign : Nat) : ZMod babyBearModulus) +
      131072 * (x.carryHi : Nat) + 262144 * (x.zero : Nat) + 524288 * (x.funct3 : Nat) := by
  simp only [key]; push_cast; ring

theorem taken_branch (x : Inputs) (h : x.sel = 3) :
    (x.taken : ZMod babyBearModulus) = (x.flag : Nat) := by
  simp [taken, h]

theorem taken_misaligned {x : Inputs} (hx : x.Valid) :
    (x.taken : ZMod babyBearModulus) * (x.misaligned : Nat) = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp x.taken_le with e | e
  · simp [e]
  · simp [hx.aligned (Or.inr e)]

/-! ### The clock -/

theorem clockWrap : (3840 : ZMod babyBearModulus) * 524288 = -1 := by decide

theorem tsCarry_le {x : Inputs} (hx : x.Valid) : x.tsCarry ≤ 1 := by
  have := hx.tsLo; unfold tsCarry; omega

theorem ts_low (x : Inputs) :
    (x.tsLo : ZMod babyBearModulus) + 4 = (x.finalTsLo : Nat) + 524288 * (x.tsCarry : Nat) := by
  simp only [finalTsLo, tsCarry, cast_mod]; push_cast; ring

/-- Constraint 12: the clock low limb advances by 4 with at most one wrap. -/
theorem ts_square {x : Inputs} (hx : x.Valid) :
    (14745600 : ZMod babyBearModulus) * ((x.tsLo : ZMod babyBearModulus) + 4 - (x.finalTsLo : Nat)) ^ 2 +
      3840 * ((x.tsLo : ZMod babyBearModulus) + 4 - (x.finalTsLo : Nat)) = 0 := by
  have hX : (x.tsLo : ZMod babyBearModulus) + 4 - (x.finalTsLo : Nat) = 524288 * (x.tsCarry : Nat) := by
    linear_combination x.ts_low
  rw [hX]
  linear_combination ((3840 * 524288 - 1) * (x.tsCarry : ZMod babyBearModulus) ^ 2 +
    (x.tsCarry : ZMod babyBearModulus)) * clockWrap + bool_of_le (tsCarry_le hx)

/-- Constraint 13: the high clock limb absorbs the wrap. -/
theorem ts_high (x : Inputs) :
    (x.finalTsHi : ZMod babyBearModulus) - (x.tsHi : Nat) +
      3840 * ((x.tsLo : ZMod babyBearModulus) + 4 - (x.finalTsLo : Nat)) = 0 := by
  unfold finalTsHi
  push_cast
  linear_combination 3840 * x.ts_low + (x.tsCarry : ZMod babyBearModulus) * clockWrap

/-! ### Fixed-table queries from an explicit row -/

theorem pair_contains {p : Nat} [Fact p.Prime] {name : String} {length : Nat} {value : Nat → Nat}
    {key val : Expression (ZMod p)} {env : _root_.Environment (ZMod p)} (n : Nat) (hn : n < length)
    (hk : key.eval env = (n : ZMod p)) (hv : val.eval env = (value n : ZMod p)) :
    (pairLookup (pairTable name length value) key val).Contains env := by
  refine ⟨⟨n, hn⟩, ?_⟩
  with_unfolding_all change ((key.eval env, val.eval env) : fieldPair (ZMod p)) =
    ((n : ZMod p), (value n : ZMod p))
  rw [hk, hv]

theorem cleanup_contains {p : Nat} [Fact p.Prime] {k b c : Expression (ZMod p)}
    {env : _root_.Environment (ZMod p)} (n : Nat) (hn : n < 65536)
    (hk : k.eval env = (n : ZMod p)) (hb : b.eval env = ((n / 2 % 2 : Nat) : ZMod p))
    (hc : c.eval env = ((n - n % 4 : Nat) : ZMod p)) :
    (jumpCleanup k b c).Contains env := by
  refine ⟨⟨n, hn⟩, ?_⟩
  with_unfolding_all change ((k.eval env, b.eval env, c.eval env) : fieldTriple (ZMod p)) =
    ((n : ZMod p), ((n / 2 % 2 : Nat) : ZMod p), ((n - n % 4 : Nat) : ZMod p))
  rw [hk, hb, hc]

/-! ### Completeness -/

set_option linter.unusedSimpArgs false in
/-- Every retained equation, range query and fixed-table query holds for a valid row. -/
theorem complete (x : Inputs) (hx : x.Valid) :
    FlatOperation.ConstraintsHoldFlat (environment x.honest) (importedConstraints (p := babyBearModulus)) := by
  have := hx.pcHi; have := hx.aHi; have := hx.op2Hi; have := hx.funct3
  have hdl := diffLo_lt hx; have hdh := diffHi_lt hx
  have hcl := carryLo_le hx; have hch := carryHi_le hx
  have hcn := carryNext_le hx; have hchn := carryHiNext_le hx
  have hnl : x.nextLo < 65536 := Nat.mod_lt _ (by decide)
  have : x.zero ≤ 1 := by unfold zero; split <;> omega
  have : x.sign ≤ 1 := by unfold sign; omega
  have hkey : x.key < 4194304 := by unfold key; omega
  simp only [importedConstraints, FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  -- goals 1-26: equations; 27-30: 16-bit ranges; 31-34: fixed-table queries
  on_goal 31 =>
    refine pair_contains (x.diffLo + x.diffHi) (by omega) ?_ ?_
    all_goals simp [Expression.eval, environment, jbs_honest, zero]
  on_goal 31 =>
    refine pair_contains x.aHi (by omega) ?_ ?_
    all_goals simp [Expression.eval, environment, jbs_honest, sign]
  on_goal 31 =>
    refine pair_contains x.key hkey ?_ ?_
    · simp only [Expression.eval, environment, jbs_honest, cast_ofNat, key_eq]; ring
    · simp [Expression.eval, environment, jbs_honest, flag]
  on_goal 31 =>
    refine cleanup_contains x.nextLo hnl ?_ ?_ ?_
    all_goals simp [Expression.eval, environment, jbs_honest, misaligned, aligned]
  all_goals first
    | exact True.intro
    | (apply range16_contains
       simp only [Expression.eval, environment, jbs_honest, cast_ofNat, Nat.cast_zero, Nat.cast_one,
         zero_add, one_mul, Arithmetic.limbBase]
       rw [ZMod.val_natCast]; exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega))
    | skip
  all_goals simp only [Expression.eval, environment, jbs_honest, cast_ofNat, cast_negSucc,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, mul_zero, zero_mul,
    add_zero, zero_add, mul_one, one_mul]
  all_goals first
    | ring1
    | linear_combination ts_square hx
    | linear_combination ts_high x
    | linear_combination bool_of_le (x.isSel_le 0)
    | linear_combination bool_of_le (x.isSel_le 1)
    | linear_combination bool_of_le (x.isSel_le 2)
    | linear_combination bool_of_le (x.isSel_le 3)
    | linear_combination bool_of_le x.rdZeroN_le
    | linear_combination bool_of_le hcl
    | linear_combination bool_of_le hch
    | linear_combination bool_of_le hcn
    | linear_combination bool_of_le hchn
    | linear_combination bool_of_le hx.borrow0
    | linear_combination bool_of_le hx.borrow1
    | linear_combination bool_of_le hx.borrow2
    | (have hsel := hx.sel
       have hal := hx.aligned
       have htm := taken_misaligned hx
       have hnle := nextLo_eq x
       have hnhe := nextHi_eq x
       obtain h | h | h | h : x.sel = 0 ∨ x.sel = 1 ∨ x.sel = 2 ∨ x.sel = 3 := by omega
       · have e1 := diffLo_jump x (by omega)
         have e2 := diffHi_jump x (by omega)
         have hm := hal (Or.inl (by omega))
         cases hz : x.rdZero <;>
           simp (config := { decide := true }) only [isSel, rdZeroN, writeLo, writeHi, outLo, outHi,
             taken, op2Lo, op2Hi, targetLo, targetHi, h, hz, hm, e1, e2, hnle, hnhe,
             Nat.reduceEqDiff, Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_mul,
             Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, zero_le, and_true, and_false, true_and,
             mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] <;>
           ring1
       · have e1 := diffLo_jump x (by omega)
         have e2 := diffHi_jump x (by omega)
         have hm := hal (Or.inl (by omega))
         cases hz : x.rdZero <;>
           simp (config := { decide := true }) only [isSel, rdZeroN, writeLo, writeHi, outLo, outHi,
             taken, op2Lo, op2Hi, targetLo, targetHi, h, hz, hm, e1, e2, hnle, hnhe,
             Nat.reduceEqDiff, Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_mul,
             Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, le_refl, and_true, and_false, true_and,
             mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] <;>
           ring1
       · have e1 := diffLo_cond hx (by omega)
         have e2 := diffHi_cond hx (by omega)
         cases hz : x.rdZero <;>
           simp (config := { decide := true }) only [isSel, rdZeroN, writeLo, writeHi, outLo, outHi,
             taken, op2Lo, op2Hi, targetLo, targetHi, h, hz, e1, e2, hnle, hnhe,
             Nat.reduceEqDiff, Nat.reduceLeDiff, Bool.false_eq_true, ↓reduceIte, Nat.cast_add,
             Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, and_true, and_false,
             true_and, false_and, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] <;>
           ring1
       · have e1 := diffLo_cond hx (by omega)
         have e2 := diffHi_cond hx (by omega)
         have e3 := targetLo_branch x h
         cases hz : x.rdZero <;>
           simp (config := { decide := true }) only [isSel, rdZeroN, writeLo, writeHi, outLo, outHi,
             op2Lo, op2Hi, targetHi, h, hz, e1, e2, e3, hnle, hnhe, Nat.reduceEqDiff,
             Nat.reduceLeDiff, Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_mul,
             Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, and_true, and_false, true_and, false_and,
             mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] <;>
           first
             | ring1
             | linear_combination htm
             | linear_combination -(taken_branch x h))

private theorem natCast_val_lt {n bound : Nat} (y : ZMod babyBearModulus) (h : y = n) (hn : n < bound)
    (hb : bound ≤ babyBearModulus) : y.val < bound := by
  subst h
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  exact hn

private theorem port_lo (tsLo prevLo k : Nat) (hts : tsLo + 2 < 524288) (hprev : prevLo < 524288)
    (hk : k ≤ 2) (y : ZMod babyBearModulus)
    (hy : y = -(tsLo : ZMod babyBearModulus) + prevLo + 524288 * (borrow prevLo tsLo k : Nat) - k) :
    y.val < 524288 := by
  unfold borrow at hy
  split at hy
  · refine natCast_val_lt y (n := prevLo + 524288 - tsLo - k) ?_ (by omega) (by decide)
    have e : (((prevLo + 524288 - tsLo - k) + tsLo + k : Nat) : ZMod babyBearModulus) =
        ((prevLo + 524288 : Nat) : ZMod babyBearModulus) := congrArg _ (by omega)
    push_cast at e hy
    rw [hy]; linear_combination -e
  · refine natCast_val_lt y (n := prevLo - tsLo - k) ?_ (by omega) (by decide)
    have e : (((prevLo - tsLo - k) + tsLo + k : Nat) : ZMod babyBearModulus) =
        ((prevLo : Nat) : ZMod babyBearModulus) := congrArg _ (by omega)
    push_cast at e hy
    rw [hy]; linear_combination -e

private theorem port_hi (tsLo tsHi prevLo prevHi k : Nat) (hts : tsHi < 524288)
    (hprev : prevHi * 524288 + prevLo < tsHi * 524288 + tsLo + k)
    (htsLo : tsLo + 2 < 524288) (hk : k ≤ 2) (y : ZMod babyBearModulus)
    (hy : y = -(tsHi : ZMod babyBearModulus) + prevHi - (borrow prevLo tsLo k : Nat) + 524288) :
    y.val < 524288 := by
  unfold borrow at hy
  split at hy
  · have : prevHi ≤ tsHi := by omega
    refine natCast_val_lt y (n := prevHi + 524287 - tsHi) ?_ (by omega) (by decide)
    have e : (((prevHi + 524287 - tsHi) + tsHi + 1 : Nat) : ZMod babyBearModulus) =
        ((prevHi + 524288 : Nat) : ZMod babyBearModulus) := congrArg _ (by omega)
    push_cast at e hy
    rw [hy]; linear_combination -e
  · have : prevHi < tsHi := by omega
    refine natCast_val_lt y (n := prevHi + 524288 - tsHi) ?_ (by omega) (by decide)
    have e : (((prevHi + 524288 - tsHi) + tsHi : Nat) : ZMod babyBearModulus) =
        ((prevHi + 524288 : Nat) : ZMod babyBearModulus) := congrArg _ (by omega)
    push_cast at e hy
    rw [hy]; linear_combination -e

/-- The eight native timestamp range queries hold for a clocked row. -/
theorem timestamps {x : Inputs} (hc : x.Clocked) :
    FlatOperation.ConstraintsHoldFlat (environment x.honest)
      (importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  have hi : x.tsHi < 524288 := by have := hc.tsHi; unfold finalTsHi at this; omega
  simp only [importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals apply Trace.Proofs.range_contains
  all_goals simp only [Trace.timestampBase, Expression.eval, environment, jbs_honest, hc.borrow0,
    hc.borrow1, hc.borrow2, cast_ofNat, cast_negSucc]
  · exact natCast_val_lt _ (n := x.finalTsLo) (by push_cast; ring) (by unfold finalTsLo; omega) (by decide)
  · exact natCast_val_lt _ (n := x.finalTsHi) (by push_cast; ring) hc.tsHi (by decide)
  · exact port_lo _ _ 0 hc.tsLo hc.prev0Lo (by decide) _ (by push_cast; ring)
  · exact port_hi _ _ _ _ 0 hi (by simpa using hc.prev0) hc.tsLo (by decide) _ (by push_cast; ring)
  · exact port_lo _ _ 1 hc.tsLo hc.prev1Lo (by decide) _ (by push_cast; ring)
  · exact port_hi _ _ _ _ 1 hi hc.prev1 hc.tsLo (by decide) _ (by push_cast; ring)
  · exact port_lo _ _ 2 hc.tsLo hc.prev2Lo (by decide) _ (by push_cast; ring)
  · exact port_hi _ _ _ _ 2 hi hc.prev2 hc.tsLo (by decide) _ (by push_cast; ring)

/-- The full row relation with its timestamp queries. -/
theorem clock_complete (x : Inputs) (hx : x.Valid) (hc : x.Clocked) :
    FlatOperation.ConstraintsHoldFlat (environment x.honest) (clockConstraints (p := babyBearModulus)) :=
  holds_append (complete x hx) (timestamps hc)

end Inputs

/-! ### Rows that agree with an honest row on the constrained columns -/

/-- The columns the circuit's constraints read; 5-7 and 28-29 are trace-only. -/
def columns : List Nat :=
  [0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27,
    30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]

theorem imported_congr {w w' : Nat → ZMod babyBearModulus} (h : ∀ i ∈ columns, w i = w' i) :
    FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints (p := babyBearModulus)) ↔
      FlatOperation.ConstraintsHoldFlat (environment w') (importedConstraints (p := babyBearModulus)) := by
  simp (disch := decide) only [importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Lookup.Contains, Vector.map, List.map_toArray, List.map_cons, List.map_nil, Expression.eval,
    environment, range16, pairLookup, jumpCleanup, h, iff_self]

theorem timestamps_congr {w w' : Nat → ZMod babyBearModulus} (h : ∀ i ∈ columns, w i = w' i) :
    FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraintsTimestampLookups (p := babyBearModulus)) ↔
      FlatOperation.ConstraintsHoldFlat (environment w')
        (importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  simp (disch := decide) only [importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Lookup.Contains, Vector.map, List.map_toArray, List.map_cons, List.map_nil, Expression.eval,
    environment, Trace.timestampLookup, h, iff_self]

/-- `complete` for any row agreeing with a valid honest row on `columns`. -/
theorem complete_of_agree (x : Inputs) (hx : x.Valid) {w : Nat → ZMod babyBearModulus}
    (hw : ∀ i ∈ columns, w i = x.honest i) :
    FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints (p := babyBearModulus)) :=
  (imported_congr hw).mpr (x.complete hx)

/-- `clock_complete` for any row agreeing with a valid, clocked honest row on `columns`. -/
theorem clock_complete_of_agree (x : Inputs) (hx : x.Valid) (hc : x.Clocked)
    {w : Nat → ZMod babyBearModulus} (hw : ∀ i ∈ columns, w i = x.honest i) :
    FlatOperation.ConstraintsHoldFlat (environment w) (clockConstraints (p := babyBearModulus)) :=
  holds_append (complete_of_agree x hx hw) ((timestamps_congr hw).mpr (Inputs.timestamps hc))

end Airbender.JumpBranchSlt.Completeness
