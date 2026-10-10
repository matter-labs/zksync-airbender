import Airbender.Review.ShiftBinop.Theorems
import Airbender.Proofs.ShiftBinop.Shifts
import Mathlib.Tactic.IntervalCases

namespace Tests.Shifts
open Airbender
open Airbender.ShiftBinop

-- Three shifts and REV8, amounts 0/31, immediate/register preprocessing, a negative
-- source and PC carry. Register amounts 32/63 exercise low-five-bit truncation.
private def amount (tag : Fin 4) (zero : Bool) : Nat := if tag.val = 3 ∨ zero then 0 else 31
private def code (tag : Fin 4) : Nat := if tag.val = 3 then 5 else tag.val + 1
private def zeroRight (tag : Fin 4) (immediate : Bool) : Bool := immediate || tag.val = 3
private def source : BitVec 32 := 2158742802
private def sourceByte (i : Nat) : Nat := (source.extractLsb' (8 * i) 8).toNat
-- Concrete expected bytes; soundness checks this value against original Sail.
private def result (tag : Fin 4) (zero : Bool) : Nat :=
  if tag.val = 3 then 315468672 else
    (Verification.shiftOperation (code tag) source (amount tag zero)).toNat
private def part (tag : Fin 4) (zero : Bool) (i j : Nat) : Nat :=
  (BitVec.extractLsb' (8 * j) 8
    (Verification.shiftByteContribution i (sourceByte i) (amount tag zero) (code tag))).toNat

private def row (tag : Fin 4) (immediate zero : Bool) : Nat → ZMod babyBearModulus
  | 0 => 65532
  | 4 | 5 | 7 | 11 | 14 => 1
  | 6 => if zeroRight tag immediate then 0 else 2
  | 8 => if immediate then amount tag zero else 0
  | 10 => code tag
  | 15 => 4
  | 19 => sourceByte 0 | 20 => sourceByte 1
  | 21 => sourceByte 2 | 22 => sourceByte 3
  | 25 | 52 => if zeroRight tag immediate then 0 else amount tag zero + 32
  | 27 => if zeroRight tag immediate then 0 else 52
  | 28 => if zeroRight tag immediate then 0 else 18
  | 31 => (result tag zero % 65536 : Nat)
  | 32 => (result tag zero / 65536 : Nat)
  | 35 | 54 => if zeroRight tag immediate then 0 else amount tag zero
  | 55 => 8
  | n => if 36 ≤ n ∧ n < 52 then part tag zero ((n - 36) / 4) ((n - 36) % 4) else
    if 56 ≤ n ∧ n < 92 then
      let i := (n - 56) / 9
      match (n - 56) % 9 with
      | 0 => i | 1 => sourceByte i | 2 => amount tag zero | 3 => code tag
      | 8 => 9 | j => part tag zero i (j - 4)
    else 0

private def rowIndex (xs : Vector (ZMod babyBearModulus) 10) : Nat :=
  if xs[9].val = 8 then 196865 + xs[0].val * 256 + xs[1].val else
    262401 + xs[0].val * 65536 + xs[1].val * 256 + xs[2].val * 8 + xs[3].val

private theorem checkedRow (xs : Vector (ZMod babyBearModulus) 10)
    (bound : rowIndex xs < 524545)
    (correct : xs = (Verification.shiftBinopRow ⟨rowIndex xs, bound⟩).map
      (fun (n : Nat) => (n : ZMod babyBearModulus))) :
    ∃ i : Fin 524545, xs = (Verification.shiftBinopRow i).map
      (fun (n : Nat) => (n : ZMod babyBearModulus)) := ⟨⟨_, bound⟩, correct⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
private theorem satisfies (tag : Fin 4) (immediate zero : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row tag immediate zero))
      importedConstraints := by
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  have equations : ∀ i : Fin (FlatOperation.constraints
      (importedConstraints (p := babyBearModulus))).length,
      ((FlatOperation.constraints importedConstraints).get i).eval
        (Verification.environment (row tag immediate zero)) = 0 := by
    intro i
    fin_cases i <;> fin_cases tag <;> cases immediate <;> cases zero <;> decide
  have queries : ∀ i : Fin (FlatOperation.lookups
      (importedConstraints (p := babyBearModulus))).length,
      ((FlatOperation.lookups importedConstraints).get i).Contains
        (Verification.environment (row tag immediate zero)) := by
    intro i
    fin_cases i <;> fin_cases tag <;> cases immediate <;> cases zero <;>
      simp [importedConstraints, FlatOperation.lookups, Lookup.Contains,
        Verification.shiftBinopLookup, Verification.shiftBinopTable, Table.fromStatic,
        Table.toRaw, Expression.eval, Verification.environment, row, amount,
        sourceByte, source, part, code, zeroRight, Verification.shiftByteContribution]
    all_goals solve
      | (apply Verification.range16_contains; decide)
      | (with_unfolding_all refine checkedRow _ (by decide) ?_
         apply Vector.ext
         intro j bound
         rw [Vector.getElem_map]
         interval_cases j <;> decide +revert)
  constructor
  · intro c hc
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hc
    exact equations i
  · intro q hq
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hq
    exact queries i

example (tag : Fin 4) (immediate zero : Bool) :
    (Arithmetic.Word.mk (row tag immediate zero 31).val (row tag immediate zero 32).val).toBitVec =
      Verification.shiftOperation (code tag) source (amount tag zero) := by
  have tagValue : (row tag immediate zero 10).val = code tag := by
    fin_cases tag <;> decide +revert
  have truncated : (row tag immediate zero 35 + row tag immediate zero 8).val = amount tag zero := by
    fin_cases tag <;> cases immediate <;> cases zero <;> decide
  have result := Proofs.shift_destination (p := babyBearModulus) (by decide) source
    (satisfies tag immediate zero) (by simp [row])
    (by rw [tagValue]; fin_cases tag <;> decide)
    (by rw [tagValue]; fin_cases tag <;> cases immediate <;> cases zero <;> decide)
    (by intro i; fin_cases i <;> rfl)
  rw [tagValue, truncated] at result
  exact result

private def instruction (tag : Fin 4) : Operation :=
  if tag.val = 0 then .sll else if tag.val = 1 then .srl else if tag.val = 2 then .sra else .rev8

private def input (tag : Fin 4) (immediate zero : Bool) : Input where
  operation := instruction tag
  immediate := immediate
  left := source
  right := BitVec.ofNat 32 (305397760 + amount tag zero + 32)
  pc := ⟨65532, 0⟩
  rs1 := .Regidx 1
  rs2 := if zeroRight tag immediate then .Regidx 0 else .Regidx 2
  rd := .Regidx 1
  encodedImmediate := BitVec.ofNat 12 (amount tag zero + if tag.val = 2 then 1024 else 0)
  before := { (default : Reference.RiscV.Sail.State) with regs :=
    ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 source
      |>.insert .x2 (BitVec.ofNat 32 (305397760 + amount tag zero + 32))
      |>.insert .PC (65532 : BitVec 32)) }

private def output (tag : Fin 4) (zero : Bool) : Reference.RiscV.Sail.Output :=
  let value := result tag zero
  ⟨⟨value % 65536, value / 65536⟩, ⟨0, 1⟩⟩

-- The shift/REV8 fixtures also satisfy the public native Sail step claim.
-- SRAI retains its upper encoding bits; rs1=rd tests source/destination aliasing.
example (tag : Fin 4) (immediate zero : Bool) :
    spec (input tag immediate zero) (output tag zero) := by
  apply Airbender.ShiftBinop.Proofs.soundness (by decide) (by decide) (input tag immediate zero) (output tag zero) (row tag immediate zero)
  refine ⟨?_, satisfies tag immediate zero, ?_⟩
  · constructor
    all_goals solve
      | (apply Reference.RiscV.Sail.read_register
         fin_cases tag <;> cases immediate <;> cases zero <;>
           simp [input, Arithmetic.Word.toBitVec, Arithmetic.Word.value,
             Arithmetic.limbBase, Std.ExtDHashMap.get?_insert])
      | (intro hi noReverse; change immediate = false at hi
         cases immediate
         · fin_cases tag <;> simp [input, instruction] at noReverse ⊢
           all_goals
             apply Reference.RiscV.Sail.read_register
             simp [Std.ExtDHashMap.get?_insert]
         · contradiction)
      | (intro hi hb; fin_cases tag <;> cases immediate <;> cases zero <;>
         dsimp [input, instruction, amount, code, zeroRight, Operation.isShift] at hi hb ⊢ <;> decide)
      | (intros; fin_cases tag <;> cases immediate <;> cases zero <;>
         simp_all [input, instruction, Operation.isShift])
      | (change (⟨65532, 0⟩ : Arithmetic.Word).Bounded
         exact ⟨by decide, by decide⟩)
      | (fin_cases tag <;> cases immediate <;> cases zero <;>
         norm_num [input, row, instruction, code, zeroRight, Operation.tag, Operation.isShift])
  · constructor
    all_goals solve
      | (intro hs; fin_cases tag <;> cases immediate <;> cases zero <;>
         dsimp [input, row, instruction, amount, Operation.isShift] <;> decide)
      | (intro i; fin_cases i <;> fin_cases tag <;> cases immediate <;> cases zero <;>
         dsimp [input, output, row, instruction, amount, sourceByte, source, result, code, zeroRight,
           Operation.tag, Operation.isShift] <;> decide)
      | (fin_cases tag <;> cases immediate <;> cases zero <;>
         dsimp [input, output, row, instruction, amount, sourceByte, source, result, code, zeroRight,
           Operation.tag, Operation.isShift] <;> decide)

-- A shift count outside the table's five-bit domain cannot satisfy the query.
example : ¬ (Verification.shiftBinopLookup
    (#v[.const 0, .const 18, .const 32, .const 1, .const 0, .const 0,
      .const 0, .const 0, .const 0, .const 9] :
        Vector (Expression (ZMod babyBearModulus)) 10)).Contains
          (Verification.environment (fun _ => 0)) := by
  intro h
  have bound := (Verification.shift_lookup (by decide) h (by rfl)).2.2.1
  change (32 : ZMod babyBearModulus).val < 32 at bound
  exact (by decide : ¬ (32 : ZMod babyBearModulus).val < 32) bound

end Tests.Shifts
