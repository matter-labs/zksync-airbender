import Slop.AddSub.RowClaims
import Slop.Final.Circuits.AddSub.Theorems

namespace Tests.NonDeterminism
open Airbender
open Airbender.Reference.RiscV
open Airbender.Reference.Sail
set_option warningAsError true

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

private def readRow : Nat → ZMod babyBearModulus
  | 0 => 65535
  | 4 | 7 | 18 | 20 => 1
  | 19 => 3
  | 21 => 4
  | 33 => 22136
  | 34 => 4660
  | _ => 0

theorem read_constraints :
    FlatOperation.ConstraintsHoldFlat (Verification.environment readRow) AddSub.importedConstraints := by
  simp [AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, readRow]
  repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains; decide)

private def readInput : AddSub.NonDeterminism.ReadInput where
  stream := [7, 0x12345678]
  position := 1
  rd := .Regidx 1
  pc := ⟨65535, 0⟩
  before := input.before

private def readOutput : Sail.Output := ⟨⟨22136, 4660⟩, ⟨3, 1⟩⟩

private theorem readMapping : AddSub.NonDeterminism.ReadMapping readInput readOutput readRow := by
  refine ⟨?_, rfl, rfl, rfl, 0x12345678, rfl, ?_, ?_⟩
  · constructor <;> rfl
  · decide
  · decide

/-- An independently supplied second response is written through the native
    Sail accessor, with PC carry. The circuit source register is not the oracle. -/
theorem external_response_native_step : AddSub.NonDeterminism.readSpec readInput readOutput := by
  apply AddSub.NonDeterminism.babyBear_read_soundness readInput readOutput readRow
  refine ⟨?_, read_constraints, readMapping⟩
  constructor
  · rfl
  · decide
  · intro k lower upper
    interval_cases k <;> rfl
  · constructor <;> decide
  · apply Sail.read_register
    simp [readInput, input, Arithmetic.Word.toBitVec, Arithmetic.Word.value]

/-- Neither an exhausted stream nor a different independent response may be
    silently replaced by the circuit's chosen output. -/
theorem exhausted_stream_rejected :
    ¬AddSub.NonDeterminism.ReadMapping { readInput with position := 2 } readOutput readRow := by
  rintro ⟨_, _, _, _, response, selected, _⟩
  simp [readInput] at selected

theorem changed_stream_rejected :
    ¬AddSub.NonDeterminism.ReadMapping { readInput with stream := [7, 0] } readOutput readRow := by
  rintro ⟨_, _, _, _, response, selected, low, _⟩
  have zero : response = 0 := by simpa [readInput] using selected.symm
  subst response
  change (22136 : ZMod babyBearModulus) = 0 at low
  exact (by decide : ¬(22136 : ZMod babyBearModulus) = 0) low

private def zeroReadRow (column : Nat) : ZMod babyBearModulus :=
  if column = 33 ∨ column = 34 then 0 else readRow column

/-- Changing only the oracle response is allowed by the original circuit.
    A fixed independent stream is consequently an external binding, not a
    consequence of constraint satisfaction or the honest witness generator. -/
theorem free_response_changes_are_accepted :
    FlatOperation.ConstraintsHoldFlat (Verification.environment zeroReadRow) AddSub.importedConstraints ∧
      ¬AddSub.NonDeterminism.ReadMapping readInput ⟨⟨0, 0⟩, ⟨3, 1⟩⟩ zeroReadRow := by
  constructor
  · simp [AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
      Verification.environment, zeroReadRow, readRow]
    repeat' apply And.intro
    all_goals first
      | decide
      | (apply Verification.range16_contains; decide)
  · rintro ⟨_, _, _, _, response, selected, low, _⟩
    have same : response = 0x12345678 := by simpa [readInput] using selected.symm
    subst response
    change (0 : ZMod babyBearModulus) = 22136 at low
    exact (by decide : ¬(0 : ZMod babyBearModulus) = 22136) low

end Tests.NonDeterminism
