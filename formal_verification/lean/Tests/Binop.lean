import Airbender.Proofs.ShiftBinop.Claims
import Mathlib.Tactic.IntervalCases

namespace Tests.Binop
open Airbender
open Airbender.ShiftBinop

-- Complementary immediate/register bytes, sign extension, source/destination
-- aliasing and a PC limb carry. Every query and retained equation is satisfied.
private def instruction (operation : Fin 3) : Operation :=
  if operation.val = 0 then .xor else if operation.val = 1 then .or else .and

private def resultByte (operation : Fin 3) (byte : Nat) : Nat :=
  if operation.val = 0 then 255 - byte else if operation.val = 1 then 255 else byte

private def row (operation : Fin 3) (immediate : Bool) : Nat → ZMod babyBearModulus
  | 0 => 65532
  | 4 | 5 | 7 | 12 | 14 => 1
  | 6 => if immediate then 0 else 2
  | 8 | 9 | 35 | 52 | 53 => if immediate then 255 else 0
  | 10 | 64 | 73 | 82 | 91 => (instruction operation).tag
  | 15 => 4
  | 19 | 56 => 18
  | 20 | 65 => 205
  | 21 | 74 => 171
  | 22 | 83 => 128
  | 25 | 26 | 27 | 28 => if immediate then 0 else 255
  | 31 => resultByte operation 18 + 256 * resultByte operation 205
  | 32 => resultByte operation 171 + 256 * resultByte operation 128
  | 36 | 58 => resultByte operation 18
  | 37 | 67 => resultByte operation 205
  | 38 | 76 => resultByte operation 171
  | 39 | 85 => resultByte operation 128
  | 55 => 3
  | 57 | 66 | 75 | 84 => 255
  | _ => 0

private def rowIndex (xs : Vector (ZMod babyBearModulus) 10) : Nat :=
  if xs[9].val = 3 then 1 + xs[0].val else
    (if xs[9].val = 4 then 257 else if xs[9].val = 6 then 65793 else 131329) +
      xs[0].val * 256 + xs[1].val

private theorem checkedRow (xs : Vector (ZMod babyBearModulus) 10)
    (bound : rowIndex xs < 524545)
    (correct : xs = (Verification.shiftBinopRow
      ⟨rowIndex xs, bound⟩).map
        (fun (n : Nat) => (n : ZMod babyBearModulus))) :
    ∃ i : Fin 524545, xs = (Verification.shiftBinopRow i).map
      (fun (n : Nat) => (n : ZMod babyBearModulus)) :=
  ⟨⟨_, bound⟩, correct⟩

set_option maxHeartbeats 3000000 in
private theorem satisfies (operation : Fin 3) (immediate : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row operation immediate))
      importedConstraints := by
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  have equations : ∀ i : Fin (FlatOperation.constraints
      (importedConstraints (p := babyBearModulus))).length,
      ((FlatOperation.constraints importedConstraints).get i).eval
        (Verification.environment (row operation immediate)) = 0 := by
    intro i
    fin_cases i <;> fin_cases operation <;> cases immediate <;> decide
  have queries : ∀ i : Fin (FlatOperation.lookups
      (importedConstraints (p := babyBearModulus))).length,
      ((FlatOperation.lookups importedConstraints).get i).Contains
        (Verification.environment (row operation immediate)) := by
    intro i
    fin_cases i <;> fin_cases operation <;> cases immediate <;>
      simp [importedConstraints, FlatOperation.lookups, Lookup.Contains,
        Verification.shiftBinopLookup, Verification.shiftBinopTable, Table.fromStatic,
        Table.toRaw, Expression.eval, Verification.environment, row, resultByte, instruction, Operation.tag]
    all_goals solve
      | (apply Verification.range16_contains; decide)
      | (with_unfolding_all refine checkedRow _ (by decide) ?_
         rw [Verification.shiftBinopRow_eq_reference]
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

private def input (operation : Fin 3) (immediate : Bool) : Input where
  operation := instruction operation
  immediate := immediate
  left := 2158742802
  right := 4294967295
  pc := ⟨65532, 0⟩
  rs1 := .Regidx 1
  rs2 := if immediate then .Regidx 0 else .Regidx 2
  rd := .Regidx 1
  encodedImmediate := 4095
  before := { (default : Reference.RiscV.Sail.State) with regs :=
    ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (2158742802 : BitVec 32) |>.insert .x2 (4294967295 : BitVec 32)
      |>.insert .PC (65532 : BitVec 32)) }

private def output (operation : Fin 3) : Reference.RiscV.Sail.Output :=
  ⟨⟨resultByte operation 18 + 256 * resultByte operation 205,
    resultByte operation 171 + 256 * resultByte operation 128⟩, ⟨0, 1⟩⟩

example (operation : Fin 3) (immediate : Bool) :
    spec (input operation immediate) (output operation) := by
  apply Airbender.ShiftBinop.Proofs.soundness (by decide) (by decide) (input operation immediate) (output operation) (row operation immediate)
  refine ⟨?_, satisfies operation immediate, ?_⟩
  · constructor
    all_goals solve
      | (apply Reference.RiscV.Sail.read_register
         fin_cases operation <;> cases immediate <;>
           simp [input, Arithmetic.Word.toBitVec, Arithmetic.Word.value,
             Arithmetic.limbBase, Std.ExtDHashMap.get?_insert])
      | (intro hi _; change immediate = false at hi
         cases immediate
         · dsimp [input]
           apply Reference.RiscV.Sail.read_register
           simp [Std.ExtDHashMap.get?_insert]
         · contradiction)
      | (intro hi hb; fin_cases operation <;> cases immediate <;>
         dsimp [input, instruction, Operation.isShift] at hi hb ⊢ <;> decide)
      | (intros; fin_cases operation <;> cases immediate <;>
         simp_all [input, instruction, Operation.isShift])
      | (change (⟨65532, 0⟩ : Arithmetic.Word).Bounded
         exact ⟨by decide, by decide⟩)
      | (fin_cases operation <;> cases immediate <;> simp [input, row, instruction, Operation.tag, Operation.isShift])
  · constructor
    all_goals solve
      | (intro hs; fin_cases operation <;> simp [input, instruction, Operation.isShift] at hs)
      | (intro i; fin_cases i <;> fin_cases operation <;> cases immediate <;>
         dsimp [input, output, row, resultByte, instruction, Operation.tag] <;> decide)
      | (fin_cases operation <;> cases immediate <;>
         dsimp [input, output, row, resultByte, instruction, Operation.tag] <;> decide)

end Tests.Binop
