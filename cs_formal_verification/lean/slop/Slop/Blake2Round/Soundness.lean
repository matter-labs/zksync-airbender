import Human.Circuits.Blake2Round.Mixing
import Slop.Blake2Round.Diagonal
import Slop.Blake2Round.Reference

import Slop.Blake2Round.Soundness.ColumnMapping
import Slop.Blake2Round.Soundness.DiagonalMapping
import Slop.Blake2Round.Soundness.Interfaces

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The diagonal calls write every extended-state word: their outputs are the
    allocated write columns themselves, so no copy equation is involved. -/
theorem extended_writes {p : Nat} (w : Nat → ZMod p) (initial : Vector Arithmetic.Word 16) :
    Preparation.words w Mixing.extendedWrites =
      phaseUpdate 1 initial (diagonalOutputs w) := by
  apply Vector.ext
  intro i hi
  interval_cases i
  all_goals simp [Preparation.words, Mixing.extendedWrites, phaseUpdate, callUpdate,
    callConstants, Specs.BLAKE3.roundConstants, Blake2G.State.Proofs.update, writeLane,
    diagonalOutputs, diagonalTrace_output]

/-- The written extended-state words are 16-bit limbs, from the diagonal queries. -/
theorem extended_words_bounded {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    ∀ i : Fin 16, (Preparation.words w Mixing.extendedWrites)[i].Bounded := by
  have large : 262144 ≤ p := by
    rw [Blake2G.Proofs.serialized_field compatible]
    unfold babyBearModulus
    omega
  have bounds (call : Fin 4) := diagonal_g_output_bounds large compatible call holds
  have b0 := bounds 0
  have b1 := bounds 1
  have b2 := bounds 2
  have b3 := bounds 3
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, diagonalTrace_output] at b0 b1 b2 b3
  intro i
  rw [extended_writes w (Vector.replicate 16 (⟨0, 0⟩ : Arithmetic.Word))]
  fin_cases i
  all_goals simp [phaseUpdate, callUpdate, callConstants, Specs.BLAKE3.roundConstants,
    Blake2G.State.Proofs.update, diagonalOutputs, diagonalTrace_output]
  all_goals first
    | exact b0.1 | exact b0.2.1 | exact b0.2.2.1 | exact b0.2.2.2
    | exact b1.1 | exact b1.2.1 | exact b1.2.2.1 | exact b1.2.2.2
    | exact b2.1 | exact b2.2.1 | exact b2.2.2.1 | exact b2.2.2.2
    | exact b3.1 | exact b3.2.1 | exact b3.2.2.1 | exact b3.2.2.2

/-- Soundness of all eight mixing calls and the allocated 16-word writeback,
    with only the stated initial addition-input and selected-message bounds. -/
theorem mixing_soundness {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (Mixing.circuitModel (p := p)).SoundnessUnder (Mixing.InterfaceAssumptions (p := p)) Mixing.spec := by
  intro input output w ⟨interface, holds, mapping⟩
  have columns := phase_reference 0 input.state input.message (columnOutputs w) (fun call =>
    column_g_soundness hp compatible call holds (column_mapping mapping call)
      (column_interface interface call))
  have diagonals := phase_reference 1 (phaseUpdate 0 input.state (columnOutputs w))
    input.message (diagonalOutputs w) (fun call =>
      diagonal_g_soundness hp compatible call holds (diagonal_mapping mapping call)
        (diagonal_messages interface call).1 (diagonal_messages interface call).2)
  rw [columns] at diagonals
  unfold Mixing.spec
  rw [mapping.output, extended_writes w (phaseUpdate 0 input.state (columnOutputs w))]
  exact diagonals.trans (round_phases _ _).symm

end Airbender.Blake2Round.Proofs
