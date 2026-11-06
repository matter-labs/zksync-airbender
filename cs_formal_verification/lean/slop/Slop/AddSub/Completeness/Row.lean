import Human.Circuits.AddSub.Artifact
import Slop.UnifiedReduced.Completeness.Control
import Slop.AddSub.Completeness.Attr

/-! Completeness of the standalone ADD/SUB circuit: the honest assignment built from
    valid inputs satisfies every retained equation and range query, and, with ordered
    previous port accesses, the eight timestamp queries. Proved once, symbolically;
    only the operation case is split. The row frame (PC, clock and port timing) and its
    lemmas are the unified circuit's `Frame`. -/

namespace Airbender.AddSub.Completeness
open Verification
open Airbender.UnifiedReduced.Completeness
set_option warningAsError true
set_option maxRecDepth 16384

/-- The operation flag a row raises: ADD/ADDI (column 10), SUB (11), AUIPC (12),
    delegation (17), non-determinism read (18), or none. The modular-arithmetic flags
    13–16 are never raised by this witness. -/
inductive Op
  | add | sub | auipc | delegation | oracle | idle
  deriving DecidableEq

/-- Inputs of one honest row (omitted fields are zero). `resp` is the free output of an
    oracle or idle row.
    The register indices and `c` (third operand of the modular multiply-add) occur in
    no constraint this witness activates, so they are arbitrary field elements. -/
structure Row where
  frame : Frame
  op : Op
  active : Nat := 0
  rs1 : ZMod babyBearModulus := 0
  rs2 : ZMod babyBearModulus := 0
  rd : ZMod babyBearModulus := 0
  immLo : Nat := 0
  immHi : Nat := 0
  aLo : Nat := 0
  aHi : Nat := 0
  bLo : Nat := 0
  bHi : Nat := 0
  cLo : ZMod babyBearModulus := 0
  cHi : ZMod babyBearModulus := 0
  respLo : Nat := 0
  respHi : Nat := 0

namespace Row

def isOp (x : Row) (o : Op) : Nat := if x.op = o then 1 else 0
def sumLo (x : Row) : Nat := match x.op with
  | .add => x.aLo + x.bLo + x.immLo
  | .auipc => x.frame.pcLo + x.immLo
  | _ => 0
def carryLo (x : Row) : Nat := match x.op with
  | .sub => if x.aLo < x.bLo then 1 else 0
  | _ => x.sumLo / 65536
def outLo (x : Row) : Nat := match x.op with
  | .sub => x.aLo + 65536 * x.carryLo - x.bLo
  | .add | .auipc => x.sumLo % 65536
  | .delegation => 0
  | .oracle | .idle => x.respLo
def sumHi (x : Row) : Nat := match x.op with
  | .add => x.carryLo + x.aHi + x.bHi + x.immHi
  | .auipc => x.carryLo + x.frame.pcHi + x.immHi
  | _ => 0
def carryHi (x : Row) : Nat := match x.op with
  | .sub => if x.aHi < x.bHi + x.carryLo then 1 else 0
  | _ => x.sumHi / 65536
def outHi (x : Row) : Nat := match x.op with
  | .sub => x.aHi + 65536 * x.carryHi - x.bHi - x.carryLo
  | .add | .auipc => x.sumHi % 65536
  | .delegation => 0
  | .oracle | .idle => x.respHi

/-- Range conditions of an honest row; the ordering of previous port accesses is a
    separate `Frame.Valid` premise, needed only for the timestamp queries. -/
structure Valid (x : Row) : Prop where
  clock : x.frame.Clock
  active : x.active ≤ 1
  aLo : x.aLo < 65536
  aHi : x.aHi < 65536
  bLo : x.bLo < 65536
  bHi : x.bHi < 65536
  respLo : x.respLo < 65536
  respHi : x.respHi < 65536
  carryLo : x.carryLo ≤ 1
  carryHi : x.carryHi ≤ 1
  delegation : x.op = .delegation →
    x.bLo = 0 ∧ x.bHi = 0 ∧ x.frame.prev1Lo = 0 ∧ x.frame.prev1Hi = 0

/-- Closes `Row.Valid x` for a concrete row by deciding each range fact. -/
macro "addsub_row_valid" : tactic =>
  `(tactic| (refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide))

/-- Closes `Frame.Valid f` for a concrete frame by deciding each range and order fact. -/
macro "addsub_frame_valid" : tactic =>
  `(tactic| (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide))

/-- The honest witness columns of a row. -/
def honest (x : Row) : Nat → ZMod babyBearModulus
  | 0 => (x.frame.pcLo : Nat) | 1 => (x.frame.pcHi : Nat)
  | 2 => (x.frame.tsLo : Nat) | 3 => (x.frame.tsHi : Nat)
  | 4 => (x.active : Nat)
  | 5 => x.rs1 | 6 => x.rs2 | 7 => x.rd
  | 8 => (x.immLo : Nat) | 9 => (x.immHi : Nat)
  | 10 => (x.isOp .add : Nat) | 11 => (x.isOp .sub : Nat) | 12 => (x.isOp .auipc : Nat)
  | 17 => (x.isOp .delegation : Nat) | 18 => (x.isOp .oracle : Nat)
  | 19 => (x.frame.finalPcLo : Nat) | 20 => (x.frame.finalPcHi : Nat)
  | 21 => (x.frame.finalTsLo : Nat) | 22 => (x.frame.finalTsHi : Nat)
  | 23 => (x.frame.prev0Lo : Nat) | 24 => (x.frame.prev0Hi : Nat)
  | 25 => (x.aLo : Nat) | 26 => (x.aHi : Nat)
  | 27 => (x.frame.prev1Lo : Nat) | 28 => (x.frame.prev1Hi : Nat)
  | 29 => (x.bLo : Nat) | 30 => (x.bHi : Nat)
  | 31 => x.cLo | 32 => x.cHi
  | 33 => (x.outLo : Nat) | 34 => (x.outHi : Nat)
  | 35 => (x.frame.prev2Lo : Nat) | 36 => (x.frame.prev2Hi : Nat)
  | 39 => (x.carryLo : Nat) | 40 => (x.carryHi : Nat)
  | 41 => ((x.aLo : Nat) + 65536 * (x.aHi : Nat)) * ((x.bLo : Nat) + 65536 * (x.bHi : Nat)) * 943718400
  | 42 => (x.frame.borrow0 : Nat) | 43 => (x.frame.borrow1 : Nat)
  | 44 => (x.frame.borrow2 : Nat)
  | _ => 0

-- BEGIN generated columns
-- generated: one rfl lemma per column (keeps `simp` off the column match)
@[addsub_honest] theorem col_0 (x : Row) : x.honest 0 = ((x.frame.pcLo : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_1 (x : Row) : x.honest 1 = ((x.frame.pcHi : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_2 (x : Row) : x.honest 2 = ((x.frame.tsLo : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_3 (x : Row) : x.honest 3 = ((x.frame.tsHi : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_4 (x : Row) : x.honest 4 = ((x.active : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_5 (x : Row) : x.honest 5 = (x.rs1 : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_6 (x : Row) : x.honest 6 = (x.rs2 : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_7 (x : Row) : x.honest 7 = (x.rd : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_8 (x : Row) : x.honest 8 = ((x.immLo : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_9 (x : Row) : x.honest 9 = ((x.immHi : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_10 (x : Row) : x.honest 10 = ((x.isOp .add : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_11 (x : Row) : x.honest 11 = ((x.isOp .sub : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_12 (x : Row) : x.honest 12 = ((x.isOp .auipc : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_13 (x : Row) : x.honest 13 = (0 : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_14 (x : Row) : x.honest 14 = (0 : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_15 (x : Row) : x.honest 15 = (0 : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_16 (x : Row) : x.honest 16 = (0 : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_17 (x : Row) : x.honest 17 = ((x.isOp .delegation : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_18 (x : Row) : x.honest 18 = ((x.isOp .oracle : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_19 (x : Row) : x.honest 19 = ((x.frame.finalPcLo : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_20 (x : Row) : x.honest 20 = ((x.frame.finalPcHi : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_21 (x : Row) : x.honest 21 = ((x.frame.finalTsLo : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_22 (x : Row) : x.honest 22 = ((x.frame.finalTsHi : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_23 (x : Row) : x.honest 23 = ((x.frame.prev0Lo : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_24 (x : Row) : x.honest 24 = ((x.frame.prev0Hi : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_25 (x : Row) : x.honest 25 = ((x.aLo : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_26 (x : Row) : x.honest 26 = ((x.aHi : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_27 (x : Row) : x.honest 27 = ((x.frame.prev1Lo : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_28 (x : Row) : x.honest 28 = ((x.frame.prev1Hi : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_29 (x : Row) : x.honest 29 = ((x.bLo : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_30 (x : Row) : x.honest 30 = ((x.bHi : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_31 (x : Row) : x.honest 31 = (x.cLo : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_32 (x : Row) : x.honest 32 = (x.cHi : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_33 (x : Row) : x.honest 33 = ((x.outLo : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_34 (x : Row) : x.honest 34 = ((x.outHi : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_35 (x : Row) : x.honest 35 = ((x.frame.prev2Lo : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_36 (x : Row) : x.honest 36 = ((x.frame.prev2Hi : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_37 (x : Row) : x.honest 37 = (0 : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_38 (x : Row) : x.honest 38 = (0 : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_39 (x : Row) : x.honest 39 = ((x.carryLo : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_40 (x : Row) : x.honest 40 = ((x.carryHi : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_41 (x : Row) : x.honest 41 = (((x.aLo : Nat) + 65536 * (x.aHi : Nat)) * ((x.bLo : Nat) + 65536 * (x.bHi : Nat)) * 943718400 : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_42 (x : Row) : x.honest 42 = ((x.frame.borrow0 : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_43 (x : Row) : x.honest 43 = ((x.frame.borrow1 : Nat) : ZMod babyBearModulus) := rfl
@[addsub_honest] theorem col_44 (x : Row) : x.honest 44 = ((x.frame.borrow2 : Nat) : ZMod babyBearModulus) := rfl
-- END generated columns

theorem isOp_bool (x : Row) (o : Op) :
    (x.isOp o : ZMod babyBearModulus) * ((x.isOp o : ZMod babyBearModulus) - 1) = 0 := by
  unfold isOp; split <;> simp

theorem outLo_lt {x : Row} (hx : x.Valid) : x.outLo < 65536 := by
  have := hx.aLo; have := hx.bLo; have := hx.respLo
  cases h : x.op <;> simp only [outLo, carryLo, h]
  all_goals first | omega | exact Nat.mod_lt _ (by decide) | (split <;> omega)

theorem outHi_lt {x : Row} (hx : x.Valid) : x.outHi < 65536 := by
  have := hx.aHi; have := hx.bHi; have := hx.respHi; have := hx.carryLo
  cases h : x.op <;> simp only [outHi, carryHi, h]
  all_goals first | omega | exact Nat.mod_lt _ (by decide) | (split <;> omega)

/-- Low-limb equation per operation, as the circuit states it (constraint 4). -/
theorem low (x : Row) (hx : x.Valid) :
    (x.isOp .add : ZMod babyBearModulus) * ((x.aLo : Nat) + (x.bLo : Nat) + (x.immLo : Nat) -
        (x.outLo : Nat) - 65536 * (x.carryLo : Nat)) +
      (x.isOp .auipc : Nat) * ((x.frame.pcLo : Nat) + (x.immLo : Nat) - (x.outLo : Nat) -
        65536 * (x.carryLo : Nat)) +
      (x.isOp .sub : Nat) * ((x.outLo : Nat) + (x.bLo : Nat) - (x.aLo : Nat) -
        65536 * (x.carryLo : Nat)) = 0 := by
  have := hx.aLo; have := hx.bLo; have hc := hx.carryLo
  cases h : x.op
  case add | auipc =>
    have e := Control.cast_mod x.sumLo 65536
    simp only [isOp, outLo, carryLo, sumLo, h, reduceCtorEq, ↓reduceIte, Nat.cast_one,
      Nat.cast_zero, zero_mul, one_mul, add_zero, zero_add] at e ⊢
    push_cast at e ⊢; linear_combination -e
  case sub =>
    simp only [isOp, outLo, carryLo, h, reduceCtorEq, ↓reduceIte, Nat.cast_one, Nat.cast_zero,
      zero_mul, one_mul, add_zero, zero_add] at hc ⊢
    split <;> (rw [Nat.cast_sub (by omega)]; push_cast; ring)
  all_goals simp [isOp, h]

/-- High-limb equation per operation, as the circuit states it (constraint 5). -/
theorem high (x : Row) (hx : x.Valid) :
    (x.isOp .add : ZMod babyBearModulus) * ((x.carryLo : Nat) + (x.aHi : Nat) + (x.bHi : Nat) +
        (x.immHi : Nat) - (x.outHi : Nat) - 65536 * (x.carryHi : Nat)) +
      (x.isOp .auipc : Nat) * ((x.carryLo : Nat) + (x.frame.pcHi : Nat) + (x.immHi : Nat) -
        (x.outHi : Nat) - 65536 * (x.carryHi : Nat)) +
      (x.isOp .sub : Nat) * ((x.carryLo : Nat) + (x.outHi : Nat) + (x.bHi : Nat) - (x.aHi : Nat) -
        65536 * (x.carryHi : Nat)) = 0 := by
  have := hx.aHi; have := hx.bHi; have hc := hx.carryHi; have hcl := hx.carryLo
  cases h : x.op
  case add | auipc =>
    have e := Control.cast_mod x.sumHi 65536
    simp only [isOp, outHi, carryHi, sumHi, h, reduceCtorEq, ↓reduceIte, Nat.cast_one,
      Nat.cast_zero, zero_mul, one_mul, add_zero, zero_add] at e ⊢
    push_cast at e ⊢; linear_combination -e
  case sub =>
    simp only [isOp, outHi, carryHi, h, reduceCtorEq, ↓reduceIte, Nat.cast_one, Nat.cast_zero,
      zero_mul, one_mul, add_zero, zero_add] at hc ⊢
    split <;> (rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring)
  all_goals simp [isOp, h]

/-- A delegation row reads a zero second operand at clock zero and writes nothing
    (constraints 6–11). -/
theorem delegation_zero (x : Row) (hx : x.Valid) :
    (x.isOp .delegation : ZMod babyBearModulus) * (x.bLo : Nat) = 0 ∧
      (x.isOp .delegation : ZMod babyBearModulus) * (x.bHi : Nat) = 0 ∧
      (x.isOp .delegation : ZMod babyBearModulus) * (x.frame.prev1Lo : Nat) = 0 ∧
      (x.isOp .delegation : ZMod babyBearModulus) * (x.frame.prev1Hi : Nat) = 0 ∧
      (x.isOp .delegation : ZMod babyBearModulus) * (x.outLo : Nat) = 0 ∧
      (x.isOp .delegation : ZMod babyBearModulus) * (x.outHi : Nat) = 0 := by
  by_cases h : x.op = .delegation
  · obtain ⟨h1, h2, h3, h4⟩ := hx.delegation h
    simp [outLo, outHi, h, h1, h2, h3, h4]
  · simp [isOp, h]

end Row

/-- `-30720` inverts the limb base `2^16` in BabyBear. -/
theorem inv65536 : (-30720 : ZMod babyBearModulus) * 65536 = 1 := by decide

/-- The circuit recomputes the PC carry as `(pcLo + 4 - finalPcLo) / 2^16`. -/
theorem pc_carry (f : Frame) :
    (-30720 : ZMod babyBearModulus) * ((f.pcLo : Nat) + 4 - (f.finalPcLo : Nat)) = (f.pcCarry : Nat) := by
  have hX : (f.pcLo : ZMod babyBearModulus) + 4 - (f.finalPcLo : Nat) = 65536 * (f.pcCarry : Nat) := by
    linear_combination f.pc_low
  rw [hX]; linear_combination (f.pcCarry : ZMod babyBearModulus) * inv65536

/-- Constraint 12: the recomputed PC carry is boolean. -/
theorem pc_square {f : Frame} (hf : f.Clock) :
    (-30720 : ZMod babyBearModulus) * ((f.pcLo : Nat) + 4 - (f.finalPcLo : Nat)) *
      ((-30720 : ZMod babyBearModulus) * ((f.pcLo : Nat) + 4 - (f.finalPcLo : Nat)) - 1) = 0 := by
  rw [pc_carry f]; exact Frame.pcCarry_bool hf

/-- Constraint 13: the high PC limb absorbs the recomputed carry. -/
theorem pc_carry_high (f : Frame) :
    (-30720 : ZMod babyBearModulus) * ((f.pcLo : Nat) + 4 - (f.finalPcLo : Nat)) +
      (f.pcHi : Nat) - (f.finalPcHi : Nat) = 0 := by
  rw [pc_carry f]; linear_combination -f.pc_high

/-- The unified circuit's clock columns, read off the AddSub columns: both circuits
    import the same eight timestamp queries, only the column numbers differ. -/
def unifiedClock (w : Nat → ZMod babyBearModulus) : Nat → ZMod babyBearModulus
  | 32 => w 21 | 33 => w 22 | 34 => w 23 | 35 => w 24 | 40 => w 27 | 41 => w 28
  | 46 => w 35 | 47 => w 36 | 123 => w 42 | 124 => w 43 | 125 => w 44 | i => w i

/-- The eight native timestamp queries hold for every row whose frame is valid. -/
theorem timestamps {x : Row} (hf : x.frame.Valid) :
    FlatOperation.ConstraintsHoldFlat (environment x.honest)
      (importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  have h := UnifiedReduced.Completeness.Frame.timestamps hf (w := unifiedClock x.honest)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [UnifiedReduced.importedConstraintsTimestampLookups,
    FlatOperation.ConstraintsHoldFlat] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, -⟩ := h
  have b0 := Trace.Proofs.range_bound h0; have b1 := Trace.Proofs.range_bound h1
  have b2 := Trace.Proofs.range_bound h2; have b3 := Trace.Proofs.range_bound h3
  have b4 := Trace.Proofs.range_bound h4; have b5 := Trace.Proofs.range_bound h5
  have b6 := Trace.Proofs.range_bound h6; have b7 := Trace.Proofs.range_bound h7
  simp only [importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
  exact ⟨Trace.Proofs.range_contains b0, Trace.Proofs.range_contains b1,
    Trace.Proofs.range_contains b2, Trace.Proofs.range_contains b3,
    Trace.Proofs.range_contains b4, Trace.Proofs.range_contains b5,
    Trace.Proofs.range_contains b6, Trace.Proofs.range_contains b7, trivial⟩

namespace Row

/-- Every retained equation and range query holds for a valid row. -/
theorem complete_core (x : Row) (hx : x.Valid) :
    FlatOperation.ConstraintsHoldFlat (environment x.honest)
      (importedConstraints (p := babyBearModulus)) := by
  have hf := hx.clock
  have : x.frame.finalPcLo < 65536 := Nat.mod_lt _ (by decide)
  have := hf.pcHi
  have := x.outLo_lt hx; have := x.outHi_lt hx
  have hl := x.low hx; have hh := x.high hx
  obtain ⟨d0, d1, d2, d3, d4, d5⟩ := x.delegation_zero hx
  simp only [importedConstraints, FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | (apply range16_contains
       simp only [Expression.eval, environment, addsub_honest, cast_ofNat, Nat.cast_zero,
         Nat.cast_one, zero_add, one_mul, Arithmetic.limbBase]
       first
         | (rw [ZMod.val_natCast]; exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega))
         | (simp only [ZMod.val_zero]; decide))
    | skip
  all_goals simp only [Expression.eval, environment, addsub_honest, cast_ofNat, cast_negSucc,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, mul_zero, zero_mul, add_zero, zero_add, one_mul]
  all_goals first
    | ring1
    | linear_combination hl
    | linear_combination hh
    | linear_combination d0
    | linear_combination d1
    | linear_combination d2
    | linear_combination d3
    | linear_combination d4
    | linear_combination d5
    | linear_combination pc_square hf
    | linear_combination pc_carry_high x.frame
    | linear_combination x.frame.ts_square hf
    | linear_combination x.frame.ts_high
    | linear_combination Control.bool_of_le hx.active
    | linear_combination Control.bool_of_le hx.carryLo
    | linear_combination Control.bool_of_le hx.carryHi
    | linear_combination x.frame.borrow0_bool
    | linear_combination x.frame.borrow1_bool
    | linear_combination x.frame.borrow2_bool
    | linear_combination x.isOp_bool .add
    | linear_combination x.isOp_bool .sub
    | linear_combination x.isOp_bool .auipc
    | linear_combination x.isOp_bool .delegation
    | linear_combination x.isOp_bool .oracle

/-- With ordered previous port accesses, the timestamp queries hold as well. -/
theorem complete (x : Row) (hx : x.Valid) (hf : x.frame.Valid) :
    FlatOperation.ConstraintsHoldFlat (environment x.honest)
      (clockConstraints (p := babyBearModulus)) :=
  holds_append (x.complete_core hx) (timestamps hf)

end Row

end Airbender.AddSub.Completeness
