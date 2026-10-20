import Human.Circuits.Blake2Round.Mixing
import Slop.Blake2Round.Diagonal
import Slop.Blake2Round.Reference

import Slop.Blake2Round.Soundness.ColumnMapping
import Slop.Blake2Round.Soundness.DiagonalMapping
import Slop.Blake2Round.Soundness.Interfaces
import Slop.Blake2Round.Soundness.Writes0
import Slop.Blake2Round.Soundness.Writes1
import Slop.Blake2Round.Soundness.Writes2
import Slop.Blake2Round.Soundness.Writes3

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The 32 imported write equations connect the eight G results to the
    allocated output words. This includes their exact limb values. -/
theorem extended_writes {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (initial : Vector Arithmetic.Word 16) :
    Preparation.words w Mixing.extendedWrites =
      phaseUpdate 1 (phaseUpdate 0 initial (columnOutputs w)) (diagonalOutputs w) := by
  apply Vector.ext
  intro i hi
  have size : i < 16 := hi
  by_cases c0 : i < 4
  · exact extended_words_0 h initial ⟨i, hi⟩ (Nat.zero_le _) c0
  by_cases c1 : i < 8
  · exact extended_words_1 h initial ⟨i, hi⟩ (by show _ ≤ i; omega) c1
  by_cases c2 : i < 12
  · exact extended_words_2 h initial ⟨i, hi⟩ (by show _ ≤ i; omega) c2
  exact extended_words_3 h initial ⟨i, hi⟩ (by show _ ≤ i; omega) size

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
  rw [mapping.output, extended_writes holds input.state]
  exact diagonals.trans (round_phases _ _).symm

end Airbender.Blake2Round.Proofs
