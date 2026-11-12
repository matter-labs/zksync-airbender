module
public import Human.Circuits.AddSub.Modular.Model
public import Proven.AddSub.ArtifactChecks
public import Proven.AddSub.OpIndex
public import Proven.Arithmetic.Word
public import Proven.Arithmetic.Lemmas
public import Proven.Constraints
public import Mathlib.Tactic.LinearCombination
public import Proven.AddSub.Modular.Canonical
public import Proven.AddSub.Modular.Equations

@[expose] public section

namespace Airbender.AddSub.Proofs
open Airbender.Arithmetic

theorem modular_result {input : Modular.Input} {output : Circuit.Output}
    {w : Nat → ZMod babyBearModulus}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (interfaces : Modular.InterfaceAssumptions input output w)
    (mapping : Modular.WordMapping input output w) (nonzero : input.rd ≠ 0) :
    output.destination.value = (Modular.arithmeticResult input.opcode input.left input.right input.oldDestination).val := by
  have s10 := interfaces.selection 10 (by omega) (by omega)
  have s11 := interfaces.selection 11 (by omega) (by omega)
  have s12 := interfaces.selection 12 (by omega) (by omega)
  have s13 := interfaces.selection 13 (by omega) (by omega)
  have s14 := interfaces.selection 14 (by omega) (by omega)
  have s15 := interfaces.selection 15 (by omega) (by omega)
  have s16 := interfaces.selection 16 (by omega) (by omega)
  simp only [ite_eq_right nonzero] at s10 s11 s12 s13 s14 s15 s16
  have nonstandard : w 10 = 0 ∧ w 11 = 0 ∧ w 12 = 0 := by
    cases hop : input.opcode <;> simp [hop, Modular.Opcode.selector] at s10 s11 s12
    all_goals exact ⟨s10, s11, s12⟩
  have selected : w 13 + w 14 + w 15 + w 16 = 1 := by
    cases hop : input.opcode <;>
      simp [hop, Modular.Opcode.selector] at s13 s14 s15 s16
    all_goals simp [s13, s14, s15, s16]
  have canonical : output.destination.value < babyBearModulus := by
    simpa [Word.value, limbBase, mapping.outputLo, mapping.outputHi] using
      modular_canonical_output (by decide) constraints nonstandard.1 nonstandard.2.1
        nonstandard.2.2 selected
  apply modular_result_of_equations interfaces mapping nonzero canonical
  · have intermediate := Verification.assertion_of_holds constraints
      ⟨1, by rw [constraint_count]; decide⟩
    op_index at intermediate
    simp [Expression.eval,
      Verification.environment] at intermediate
    linear_combination intermediate
  · have result := Verification.assertion_of_holds constraints
      ⟨2, by rw [constraint_count]; decide⟩
    op_index at result
    simp [Expression.eval,
      Verification.environment] at result
    linear_combination result


end Airbender.AddSub.Proofs
