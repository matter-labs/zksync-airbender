import Airbender.Review.AddSub.Theorems

namespace Tests.NonDeterminism
open Airbender
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

private def row : Nat → ZMod babyBearModulus
  | 0 => 65535
  | 4 | 10 | 20 => 1
  | 19 => 3
  | 21 => 4
  | _ => 0

private theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row) AddSub.importedConstraints := by
  simp [AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, row]
  repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains
       decide)

private def input : AddSub.NonDeterminism.WriteInput where
  pc := ⟨65535, 0⟩
  before := { (default : Sail.State) with regs :=
    ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (123 : BitVec 32) |>.insert .PC (65535 : BitVec 32)) }

/-- An original nonzero source hint has no architectural effect; PC crosses a limb
    boundary. The circuit only contains the decoder's zero-operand ADD row. -/
example : AddSub.NonDeterminism.writeSpec input ⟨3, 1⟩ := by
  apply AddSub.NonDeterminism.babyBear_write_soundness input ⟨3, 1⟩ row
  refine ⟨?_, satisfies, ?_, rfl⟩
  · constructor
    · rfl
    · intro k lower upper
      interval_cases k <;> rfl
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · constructor <;> decide
    · apply Sail.read_register
      simp [input, Arithmetic.Word.toBitVec, Arithmetic.Word.value]
  · constructor <;> rfl

end Tests.NonDeterminism
