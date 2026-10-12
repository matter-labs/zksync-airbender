import Airbender.Proofs.AddSub.RowClaims
import Airbender.Review.AddSub.Theorems

namespace Tests.Discarded
open Airbender
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

private def row : Nat → ZMod babyBearModulus
  | 0 => 65532
  | 4 | 10 | 20 => 1
  | 21 => 4
  | _ => 0

private theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row) AddSub.importedConstraints := by
  simp [AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, row]
  repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains; decide)

private def input (instruction : AddSub.Discarded.Instruction) : AddSub.Discarded.Input where
  instruction := instruction
  pc := ⟨65532, 0⟩
  before := { (default : Sail.State) with regs :=
    ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (123 : BitVec 32) |>.insert .x2 (4294967295 : BitVec 32)
      |>.insert .PC (65532 : BitVec 32)) }

private theorem interfaces (instruction : AddSub.Discarded.Instruction)
    (reads : match instruction with
      | .register _ rs1 rs2 | .multiply _ rs1 rs2 | .divide _ rs1 rs2 | .remainder _ rs1 rs2 => ∃ left right,
          run (SailRV32.Functions.rX_bits rs1) (input instruction).before =
            .ok left (input instruction).before ∧
          run (SailRV32.Functions.rX_bits rs2) (input instruction).before =
            .ok right (input instruction).before
      | .immediate _ rs1 _ | .shiftImmediate _ rs1 _ | .rev8 rs1 => ∃ left,
          run (SailRV32.Functions.rX_bits rs1) (input instruction).before =
            .ok left (input instruction).before) :
    AddSub.Discarded.InterfaceAssumptions (input instruction) ⟨0, 1⟩ row := by
  constructor
  · rfl
  · intro k lower upper
    interval_cases k <;> rfl
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · change Arithmetic.Word.Bounded ⟨65532, 0⟩
    exact ⟨by decide, by decide⟩
  · exact reads
  · apply Sail.read_register
    simp [input, Arithmetic.Word.toBitVec, Arithmetic.Word.value]

/-- Every retained RTYPE opcode, including SLT/SLTU, discards the computed result.
    Original nonzero operands differ from NOP's zeros; PC crosses a limb boundary. -/
example (op : SailRV32.rop) :
    AddSub.Discarded.spec (input (.register op (.Regidx 1) (.Regidx 2))) ⟨0, 1⟩ := by
  apply AddSub.Discarded.babyBear_soundness _ _ row
  refine ⟨interfaces _ ?_, satisfies, ?_, rfl⟩
  · refine ⟨123, 4294967295, ?_, ?_⟩
    all_goals apply Sail.read_register
    all_goals simp [input, Std.ExtDHashMap.get?_insert]
  · constructor <;> rfl

/-- Every retained ITYPE opcode, including SLTI/SLTIU, with original immediate -1. -/
example (op : SailRV32.iop) :
    AddSub.Discarded.spec (input (.immediate op (.Regidx 1) 4095)) ⟨0, 1⟩ := by
  apply AddSub.Discarded.babyBear_soundness _ _ row
  refine ⟨interfaces _ ?_, satisfies, ?_, rfl⟩
  · refine ⟨123, ?_⟩
    apply Sail.read_register
    simp [input, Std.ExtDHashMap.get?_insert]
  · constructor <;> rfl

-- All immediate shift clauses reuse the same NOP proof, for every decoded count.
example (op : SailRV32.sop) (amount : BitVec 6) :
    AddSub.Discarded.spec (input (.shiftImmediate op (.Regidx 1) amount)) ⟨0, 1⟩ := by
  apply AddSub.Discarded.babyBear_soundness _ _ row
  refine ⟨interfaces _ ?_, satisfies, ?_, rfl⟩
  · refine ⟨123, ?_⟩
    apply Sail.read_register
    simp [input, Std.ExtDHashMap.get?_insert]
  · constructor <;> rfl

-- REV8 writes to x0 reuse the same imported NOP row and original Sail clause.
example : AddSub.Discarded.spec (input (.rev8 (.Regidx 1))) ⟨0, 1⟩ := by
  apply AddSub.Discarded.babyBear_soundness _ _ row
  refine ⟨interfaces _ ?_, satisfies, ?_, rfl⟩
  · refine ⟨123, ?_⟩
    apply Sail.read_register
    simp [input, Std.ExtDHashMap.get?_insert]
  · constructor <;> rfl

-- All native multiplication sign/half choices and both division signedness
-- choices share the same imported NOP row; the original operands are nonzero.
example (op : SailRV32.mul_op) :
    AddSub.Discarded.spec (input (.multiply op (.Regidx 1) (.Regidx 2))) ⟨0, 1⟩ := by
  apply AddSub.Discarded.babyBear_soundness _ _ row
  refine ⟨interfaces _ ?_, satisfies, ?_, rfl⟩
  · refine ⟨123, 4294967295, ?_, ?_⟩
    all_goals apply Sail.read_register
    all_goals simp [input, Std.ExtDHashMap.get?_insert]
  · constructor <;> rfl

example (unsigned : Bool) :
    AddSub.Discarded.spec (input (.divide unsigned (.Regidx 1) (.Regidx 2))) ⟨0, 1⟩ := by
  apply AddSub.Discarded.babyBear_soundness _ _ row
  refine ⟨interfaces _ ?_, satisfies, ?_, rfl⟩
  · refine ⟨123, 4294967295, ?_, ?_⟩
    all_goals apply Sail.read_register
    all_goals simp [input, Std.ExtDHashMap.get?_insert]
  · constructor <;> rfl

example (unsigned : Bool) :
    AddSub.Discarded.spec (input (.remainder unsigned (.Regidx 1) (.Regidx 2))) ⟨0, 1⟩ := by
  apply AddSub.Discarded.babyBear_soundness _ _ row
  refine ⟨interfaces _ ?_, satisfies, ?_, rfl⟩
  · refine ⟨123, 4294967295, ?_, ?_⟩
    all_goals apply Sail.read_register
    all_goals simp [input, Std.ExtDHashMap.get?_insert]
  · constructor <;> rfl

-- The architectural zero register supplies a real zero divisor; both signed
-- and unsigned DIV/REM still discard their exceptional-case result at x0.
example (unsigned remainder : Bool) :
    AddSub.Discarded.spec (input (if remainder then
      .remainder unsigned (.Regidx 1) Sail.zeroRegister
      else .divide unsigned (.Regidx 1) Sail.zeroRegister)) ⟨0, 1⟩ := by
  cases remainder <;> apply AddSub.Discarded.babyBear_soundness _ _ row
  all_goals refine ⟨interfaces _ ?_, satisfies, ?_, rfl⟩
  all_goals first
    | (refine ⟨123, 0, ?_, rfl⟩
       apply Sail.read_register
       simp [input, Std.ExtDHashMap.get?_insert])
    | (constructor <;> rfl)

end Tests.Discarded
