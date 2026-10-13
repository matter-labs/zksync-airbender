import Airbender.Proofs.AddSub.RowClaims
import Airbender.Review.Circuits.AddSub.Theorems
import Airbender.Proofs.Constraints

namespace Tests.Modular
open Airbender
open Airbender.AddSub
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

private def state (left right : BitVec 32) : Sail.State :=
  { (default : Sail.State) with regs :=
    ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 left |>.insert .x2 right |>.insert .PC (0 : BitVec 32)) }

-- ADDMOD(p-1, 1) = 0, with an actual satisfying assignment at the reduction boundary.
private def row : Nat → ZMod babyBearModulus
  | 4 | 13 | 39 | 40 => 1
  | 7 => 3
  | 19 | 21 => 4
  | 26 => 30720
  | 29 => 1
  | 37 => 65535
  | 38 => 34815
  | 41 => 1069547521
  | _ => 0

private def input : AddSub.Modular.Input where
  opcode := .add
  left := BitVec.ofNat 32 (babyBearModulus - 1)
  right := 1
  oldDestination := 0
  rs1 := .Regidx 1
  rs2 := .Regidx 2
  rd := .Regidx 3
  pc := ⟨0, 0⟩
  before := state (BitVec.ofNat 32 (babyBearModulus - 1)) 1

private theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row) importedConstraints := by
  norm_num [importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, row, babyBearModulus]
  repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, row, Arithmetic.limbBase,
         ZMod.val_ofNat, babyBearModulus])
    | decide

example : AddSub.Modular.spec input ⟨⟨0, 0⟩, ⟨4, 0⟩⟩ := by
  apply AddSub.Modular.soundness input ⟨⟨0, 0⟩, ⟨4, 0⟩⟩ row
  refine ⟨?_, satisfies, ?_⟩
  · constructor
    · rfl
    · intro k lower upper
      interval_cases k <;> rfl
    · constructor <;> decide
    · constructor
      · refine ⟨input.left, ?_, fun _ => rfl⟩
        apply Sail.read_register
        simp [input, state, Std.ExtDHashMap.get?_insert]
      · refine ⟨input.right, ?_, fun _ => rfl⟩
        apply Sail.read_register
        simp [input, state, Std.ExtDHashMap.get?_insert]
      · intro _ condition
        cases condition
      · apply Sail.read_register
        simp [input, state, Arithmetic.Word.toBitVec, Arithmetic.Word.value]
  · constructor
    · intro _; decide
    · intro _; decide
    · intro _ condition; cases condition
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

-- FMAMOD x1,x1,x2 reads x1 before overwriting it: 11 + 11*3/R mod p.
private def fmaRow : Nat → ZMod babyBearModulus
  | 4 | 7 | 16 | 40 => 1
  | 19 | 21 => 4
  | 25 | 31 => 11
  | 29 => 3
  | 33 => 65532
  | 34 => 14399
  | 37 => 65531
  | 38 => 49215
  | 41 => 943718396
  | _ => 0

private def fmaInput : AddSub.Modular.Input where
  opcode := .fma
  left := 11
  right := 3
  oldDestination := 11
  rs1 := .Regidx 1
  rs2 := .Regidx 2
  rd := .Regidx 1
  pc := ⟨0, 0⟩
  before := state 11 3

private theorem fmaSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment fmaRow) importedConstraints := by
  simp [importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, fmaRow]
  repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains; decide)

example : AddSub.Modular.spec fmaInput ⟨⟨65532, 14399⟩, ⟨4, 0⟩⟩ := by
  apply AddSub.Modular.soundness fmaInput ⟨⟨65532, 14399⟩, ⟨4, 0⟩⟩ fmaRow
  refine ⟨?_, fmaSatisfies, ?_⟩
  · constructor
    · rfl
    · intro k lower upper
      interval_cases k <;> rfl
    · constructor <;> decide
    · constructor
      · refine ⟨11, ?_, fun _ => rfl⟩
        apply Sail.read_register
        simp [fmaInput, state, Std.ExtDHashMap.get?_insert]
      · refine ⟨3, ?_, fun _ => rfl⟩
        apply Sail.read_register
        simp [fmaInput, state, Std.ExtDHashMap.get?_insert]
      · intro _ _
        apply Sail.read_register
        simp [fmaInput, state, Std.ExtDHashMap.get?_insert]
      · apply Sail.read_register
        simp [fmaInput, state, Arithmetic.Word.toBitVec, Arithmetic.Word.value]
  · constructor
    · intro _; decide
    · intro _; decide
    · intro _ _; decide
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · decide
    · rfl

private def zeroRow : Nat → ZMod babyBearModulus
  | 4 | 10 => 1
  | 19 | 21 => 4
  | _ => 0

private def zeroInput (opcode : AddSub.Modular.Opcode) : AddSub.Modular.Input where
  opcode := opcode
  left := 123
  right := 456
  oldDestination := 0
  rs1 := .Regidx 1
  rs2 := .Regidx 2
  rd := Sail.zeroRegister
  pc := ⟨0, 0⟩
  before := state 123 456

private theorem zeroSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment zeroRow) importedConstraints := by
  simp [importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, zeroRow]
  repeat' apply And.intro
  all_goals
    apply Verification.range16_contains
    decide

/-- Every custom opcode writing x0 is preprocessed to ADD, but original nonzero
    source reads still occur. Only PC changes; the computed word is discarded. -/
example (opcode : AddSub.Modular.Opcode) : AddSub.Modular.spec (zeroInput opcode) ⟨⟨0, 0⟩, ⟨4, 0⟩⟩ := by
  apply AddSub.Modular.soundness (zeroInput opcode) ⟨⟨0, 0⟩, ⟨4, 0⟩⟩ zeroRow
  refine ⟨?_, zeroSatisfies, ?_⟩
  · constructor
    · rfl
    · intro k lower upper
      interval_cases k <;> rfl
    · change (⟨0, 0⟩ : Arithmetic.Word).Bounded
      constructor <;> decide
    · constructor
      · refine ⟨123, ?_, fun _ => rfl⟩
        apply Sail.read_register
        simp [zeroInput, state, Std.ExtDHashMap.get?_insert]
      · refine ⟨456, ?_, fun _ => rfl⟩
        apply Sail.read_register
        simp [zeroInput, state, Std.ExtDHashMap.get?_insert]
      · intro nonzero
        exact False.elim (nonzero rfl)
      · apply Sail.read_register
        simp [zeroInput, state, Arithmetic.Word.toBitVec, Arithmetic.Word.value]
  · constructor
    · intro nonzero; exact False.elim (nonzero rfl)
    · intro nonzero; exact False.elim (nonzero rfl)
    · intro nonzero; exact False.elim (nonzero rfl)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

end Tests.Modular
