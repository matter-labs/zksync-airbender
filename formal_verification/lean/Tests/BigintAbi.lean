import Airbender.Proofs.Bigint.Claims
import Airbender.Proofs.ExternalBoundary.BigintABI

namespace Tests.BigintAbi
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def row (withOpcode : Bool) (high : Nat) : Nat → ZMod babyBearModulus
  | 0 | 212 | 214 | 215 => 1
  | 55 | 59 => if withOpcode then 1 else 0
  | 56 => high
  | _ => 0

private abbrev setup : Table (ZMod babyBearModulus) (fields 3) := Bigint.setupTable

theorem abiRowsSatisfy (withOpcode : Bool) (high : Nat) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row withOpcode high))
      (Bigint.importedConstraints setup) := by
  cases withOpcode <;> simp [Bigint.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, row, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide
    | (apply Verification.range16_contains; norm_num [Expression.eval, Verification.environment, row, Verification.range16, fromElements, Arithmetic.limbBase])
    | (refine ⟨⟨0, by decide⟩, ?_⟩; norm_num [setup, Bigint.setupTable, Bigint.Proofs.setup_row_characterization, row, Verification.environment, Expression.eval])
    | (refine ⟨⟨262144, by decide⟩, ?_⟩; norm_num [setup, Bigint.setupTable, Bigint.Proofs.setup_row_characterization, row, Verification.environment, Expression.eval])
    | (refine ⟨⟨1310720, by decide⟩, ?_⟩; norm_num [setup, Bigint.setupTable, Bigint.Proofs.setup_row_characterization, row, Verification.environment, Expression.eval])
    | (refine ⟨⟨1312768, by decide⟩, ?_⟩; norm_num [setup, Bigint.setupTable, Bigint.Proofs.setup_row_characterization, row, Verification.environment, Expression.eval])
    | (refine ⟨⟨1316864, by decide⟩, ?_⟩; norm_num [setup, Bigint.setupTable, Bigint.Proofs.setup_row_characterization, row, Verification.environment, Expression.eval])
    | (refine ⟨⟨1325056, by decide⟩, ?_⟩; norm_num [setup, Bigint.setupTable, Bigint.Proofs.setup_row_characterization, row, Verification.environment, Expression.eval])

theorem noOpcodeSatisfies (high : Nat) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row false high))
      (Bigint.importedConstraints setup) := abiRowsSatisfy false high

theorem activeWithoutOpcode :
    row false 0 Bigint.Variables.controlBits[0] = 0 ∧ row false 0 0 = 1 ∧
    (row false 0 55).val = 0 ∧
    (∑ i : Fin 7, (row false 0 Bigint.Variables.operations[i]).val) = 0 := by
  simp [row, Bigint.Variables.controlBits, Bigint.Variables.operations, Fin.sum_univ_succ]

theorem validOpcodeHighAccepted :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row true 1))
      (Bigint.importedConstraints setup) ∧
    (row true 1 55).val = 1 ∧ (row true 1 56).val = 1 :=
  ⟨abiRowsSatisfy true 1, by decide, by decide⟩

theorem no_opcode_requires_temporary_assumption :
    ¬ ∃ command, ExternalBoundary.BigintABI.Binding (row false 0) command := by
  rintro ⟨command, binding⟩
  have equal := congrArg Arithmetic.Word.lo binding
  have positive := ExternalBoundary.BigintABI.Proofs.command_nonzero command
  have zero : (ExternalBoundary.BigintABI.input (row false 0)).lo = 0 := by decide
  omega

theorem high_control_requires_temporary_assumption :
    ¬ ∃ command, ExternalBoundary.BigintABI.Binding (row true 1) command := by
  rintro ⟨command, binding⟩
  have equal := congrArg Arithmetic.Word.hi binding
  have high : (ExternalBoundary.BigintABI.input (row true 1)).hi = 1 := by
    rw [ExternalBoundary.BigintABI.Proofs.input_word]
    decide
  have zero : command.word.hi = 0 := rfl
  omega

theorem valid_control_inhabits_temporary_contract :
    ExternalBoundary.BigintABI.Binding (row true 0) ⟨0, false⟩ := by
  unfold ExternalBoundary.BigintABI.Binding
  rw [ExternalBoundary.BigintABI.Proofs.input_word]
  decide

end Tests.BigintAbi
