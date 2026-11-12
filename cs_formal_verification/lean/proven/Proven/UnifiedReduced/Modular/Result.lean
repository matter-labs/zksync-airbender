module
public import Proven.UnifiedReduced.Modular.Canonical
public import Proven.AddSub.Modular.Equations

@[expose] public section

namespace Airbender.UnifiedReduced.Modular.Proofs
open Arithmetic
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The unified field branches reuse the standalone arithmetic equations under the native column map. -/
theorem modular_result {input : AddSub.Modular.Input} {output : Circuit.Output}
    {w : Nat → ZMod babyBearModulus}
    {setup : Table (ZMod babyBearModulus) (fields 10)}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (noTriAdd : w 20 = 0)
    (interfaces : AddSub.Modular.InterfaceAssumptions input output (lift w))
    (mapping : AddSub.Modular.WordMapping input output (lift w)) (nonzero : input.rd ≠ 0) :
    output.destination.value = (AddSub.Modular.arithmeticResult input.opcode input.left input.right input.oldDestination).val := by
  have s10 := interfaces.selection 10 (by omega) (by omega)
  have s11 := interfaces.selection 11 (by omega) (by omega)
  have s12 := interfaces.selection 12 (by omega) (by omega)
  have s13 := interfaces.selection 13 (by omega) (by omega)
  have s14 := interfaces.selection 14 (by omega) (by omega)
  have s15 := interfaces.selection 15 (by omega) (by omega)
  have s16 := interfaces.selection 16 (by omega) (by omega)
  simp only [ite_eq_right nonzero] at s10 s11 s12 s13 s14 s15 s16
  have nonstandard : lift w 10 = 0 ∧ lift w 11 = 0 ∧ lift w 12 = 0 := by
    cases hop : input.opcode <;> simp [hop, AddSub.Modular.Opcode.selector] at s10 s11 s12
    all_goals exact ⟨s10, s11, s12⟩
  have selected : lift w 13 + lift w 14 + lift w 15 + lift w 16 = 1 := by
    cases hop : input.opcode <;>
      simp [hop, AddSub.Modular.Opcode.selector] at s13 s14 s15 s16
    all_goals simp [s13, s14, s15, s16]
  have canonical : output.destination.value < babyBearModulus := by
    simpa [Word.value, limbBase, mapping.outputLo, mapping.outputHi, lift] using
      canonical_output constraints nonstandard.1 nonstandard.2.1
        nonstandard.2.2 noTriAdd selected
  apply AddSub.Proofs.modular_result_of_equations interfaces mapping nonzero canonical
  · have intermediate := Verification.assertion_of_holds constraints
      ⟨1, by rw [constraint_count]; decide⟩
    op_index at intermediate
    simp [Expression.eval,
      Verification.environment] at intermediate
    simp only [lift]
    linear_combination intermediate
  · have result := Verification.assertion_of_holds constraints
      ⟨2, by rw [constraint_count]; decide⟩
    op_index at result
    simp [Expression.eval,
      Verification.environment] at result
    simp only [lift]
    linear_combination result


end Airbender.UnifiedReduced.Modular.Proofs
