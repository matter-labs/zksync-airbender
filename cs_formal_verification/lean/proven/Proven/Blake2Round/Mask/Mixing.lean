module
public import Proven.Blake2Round.Mask.GSound
public import Proven.Blake2Round.Soundness

@[expose] public section
namespace Airbender.Blake2Round.Proofs
open Arithmetic

/-- The raw selected message limbs can contain the sum of ten source limbs. -/
def WideMessage (word : Word) : Prop := word.lo < 655360 ∧ word.hi < 655360

/-- The column G proof admits the complete Boolean-mask message sum. -/
theorem column_g_soundness_wide {p : Nat} [Fact p.Prime] (hp : 786432 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4)
    {w : Nat → ZMod p} {input : Blake2G.Input}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable))
    (mapping : input = (columnTrace call.val w).input)
    (aBound : input.state.a.Bounded) (cBound : input.state.c.Bounded)
    (xBound : WideMessage input.mx) (yBound : WideMessage input.my) :
    Blake2G.spec input (columnTrace call.val w).output := by
  subst mapping
  exact GTrace.sound_wide hp (column_facts (by omega) compatible call holds) aBound cBound xBound yBound

/-- The diagonal G proof reuses the bounds on actual column outputs. -/
theorem diagonal_g_soundness_wide {p : Nat} [Fact p.Prime] (hp : 786432 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4)
    {w : Nat → ZMod p} {input : Blake2G.Input}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable))
    (mapping : input = (diagonalTrace call.val w).input)
    (xBound : WideMessage input.mx) (yBound : WideMessage input.my) :
    Blake2G.spec input (diagonalTrace call.val w).output := by
  subst mapping
  have bounds := diagonal_g_input_bounds (by omega) compatible call holds
  exact GTrace.sound_wide hp (diagonal_facts (by omega) compatible call holds)
    bounds.1 bounds.2 xBound yBound

/-- All eight native G calls compute the reference round for wide mask-selected messages. -/
theorem mixing_soundness_wide {p : Nat} [Fact p.Prime] (hp : 786432 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {input : Mixing.Input} {output : Mixing.Output} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable))
    (mapping : Mixing.WordMapping input output w)
    (stateBounds : ∀ i : Fin 16, input.state[i].Bounded)
    (messageBounds : ∀ i : Fin 16, WideMessage input.message[i]) : Mixing.spec input output := by
  have columnBounds (call : Fin 4) :
      (callInput 0 call input.state input.message).state.a.Bounded ∧
      (callInput 0 call input.state input.message).state.c.Bounded ∧
      WideMessage (callInput 0 call input.state input.message).mx ∧
      WideMessage (callInput 0 call input.state input.message).my := by
    fin_cases call <;> simp only [callInput, callConstants, Specs.BLAKE3.roundConstants,
      Blake2G.State.Proofs.project]
    all_goals exact ⟨stateBounds _, stateBounds _, messageBounds _, messageBounds _⟩
  have diagonalBounds (call : Fin 4) :
      WideMessage (callInput 1 call (phaseUpdate 0 input.state (columnOutputs w)) input.message).mx ∧
      WideMessage (callInput 1 call (phaseUpdate 0 input.state (columnOutputs w)) input.message).my := by
    fin_cases call <;> simp only [callInput, callConstants, Specs.BLAKE3.roundConstants]
    all_goals exact ⟨messageBounds _, messageBounds _⟩
  have columns := phase_reference 0 input.state input.message (columnOutputs w) (fun call =>
    column_g_soundness_wide hp compatible call holds (column_mapping mapping call)
      (columnBounds call).1 (columnBounds call).2.1 (columnBounds call).2.2.1 (columnBounds call).2.2.2)
  have diagonals := phase_reference 1 (phaseUpdate 0 input.state (columnOutputs w))
    input.message (diagonalOutputs w) (fun call =>
      diagonal_g_soundness_wide hp compatible call holds (diagonal_mapping mapping call)
        (diagonalBounds call).1 (diagonalBounds call).2)
  rw [columns] at diagonals
  unfold Mixing.spec
  rw [mapping.output, extended_writes w (phaseUpdate 0 input.state (columnOutputs w))]
  exact diagonals.trans (round_phases _ _).symm

end Airbender.Blake2Round.Proofs
