import Airbender.Review.Circuits.Blake2Round.Mixing
import Airbender.Proofs.Blake2Round.Diagonal
import Airbender.Proofs.Blake2Round.Reference

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def gOutput {p : Nat} (w : Nat → ZMod p) : Blake2G.Words :=
  ⟨⟨(w 17).val, (w 18).val⟩, ⟨(w 21).val, (w 22).val⟩,
    ⟨(w 25).val, (w 26).val⟩, ⟨(w 29).val, (w 30).val⟩⟩

def columnOutputs {p : Nat} (w : Nat → ZMod p) (call : Fin 4) : Blake2G.Words :=
  gOutput (columnGAssignment call w)

def diagonalOutputs {p : Nat} (w : Nat → ZMod p) (call : Fin 4) : Blake2G.Words :=
  gOutput (diagonalGAssignment call w)

private theorem column_mapping {p : Nat} {w : Nat → ZMod p}
    {input : Mixing.Input} {output : Mixing.Output}
    (mapping : Mixing.WordMapping input output w) (call : Fin 4) :
    Blake2G.WordMapping (callInput 0 call input.state input.message)
      (columnOutputs w call) (columnGAssignment call w) := by
  rw [mapping.state, mapping.message]
  fin_cases call <;> constructor
  all_goals simp [callInput, callConstants, Specs.BLAKE3.roundConstants,
    Blake2G.State.Proofs.project, Preparation.words, Variables.preparedState,
    Variables.scheduledMessage, columnOutputs, gOutput, columnGAssignment,
    columnGBase, Blake2G.Proofs.assemble, Fin.getElem_fin]

private theorem diagonal_mapping {p : Nat} {w : Nat → ZMod p}
    {input : Mixing.Input} {output : Mixing.Output}
    (mapping : Mixing.WordMapping input output w) (call : Fin 4) :
    Blake2G.WordMapping
      (callInput 1 call (phaseUpdate 0 input.state (columnOutputs w)) input.message)
      (diagonalOutputs w call) (diagonalGAssignment call w) := by
  rw [mapping.message]
  fin_cases call <;> constructor
  all_goals simp [callInput, callConstants, Specs.BLAKE3.roundConstants,
    phaseUpdate, callUpdate, Blake2G.State.Proofs.project, Blake2G.State.Proofs.update,
    Preparation.words, Variables.scheduledMessage, columnOutputs, diagonalOutputs,
    gOutput, columnGAssignment, columnGBase, diagonalGAssignment, diagonalGBase,
    Blake2G.Proofs.assemble, Fin.getElem_fin]

private theorem column_interface {p : Nat} {w : Nat → ZMod p}
    {input : Mixing.Input} {output : Mixing.Output}
    (interface : Mixing.InterfaceAssumptions input output w) (call : Fin 4) :
    Blake2G.InterfaceAssumptions (callInput 0 call input.state input.message)
      (columnOutputs w call) (columnGAssignment call w) := by
  fin_cases call <;> constructor
  all_goals simp only [callInput, callConstants, Specs.BLAKE3.roundConstants,
    Blake2G.State.Proofs.project]
  all_goals first
    | exact (interface.additionInputs 0).1 | exact (interface.additionInputs 1).1
    | exact (interface.additionInputs 2).1 | exact (interface.additionInputs 3).1
    | exact (interface.additionInputs 0).2 | exact (interface.additionInputs 1).2
    | exact (interface.additionInputs 2).2 | exact (interface.additionInputs 3).2
    | exact interface.messages 0 | exact interface.messages 1
    | exact interface.messages 2 | exact interface.messages 3
    | exact interface.messages 4 | exact interface.messages 5
    | exact interface.messages 6 | exact interface.messages 7

private theorem diagonal_messages {p : Nat} {w : Nat → ZMod p}
    {input : Mixing.Input} {output : Mixing.Output}
    (interface : Mixing.InterfaceAssumptions input output w) (call : Fin 4) :
    (callInput 1 call (phaseUpdate 0 input.state (columnOutputs w)) input.message).mx.Bounded ∧
      (callInput 1 call (phaseUpdate 0 input.state (columnOutputs w)) input.message).my.Bounded := by
  fin_cases call <;> constructor
  all_goals simp only [callInput, callConstants, Specs.BLAKE3.roundConstants]
  all_goals first
    | exact interface.messages 8 | exact interface.messages 9
    | exact interface.messages 10 | exact interface.messages 11
    | exact interface.messages 12 | exact interface.messages 13
    | exact interface.messages 14 | exact interface.messages 15

/-- The 32 imported write equations connect the eight G results to the
    allocated output words. This includes their exact limb values. -/
theorem extended_writes {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (initial : Vector Arithmetic.Word 16) :
    Preparation.words w Mixing.extendedWrites =
      phaseUpdate 1 (phaseUpdate 0 initial (columnOutputs w)) (diagonalOutputs w) := by
  have word (i : Fin 16) :
      (Preparation.words w Mixing.extendedWrites)[i] =
        (phaseUpdate 1 (phaseUpdate 0 initial (columnOutputs w)) (diagonalOutputs w))[i] := by
    have low := Verification.assertion_of_holds h
      ⟨120 + 2 * i.val, by rw [constraint_count]; have size := i.isLt; omega⟩
    have high := Verification.assertion_of_holds h
      ⟨121 + 2 * i.val, by rw [constraint_count]; have size := i.isLt; omega⟩
    fin_cases i
    all_goals simp [Preparation.words, Mixing.extendedWrites, phaseUpdate, callUpdate,
      callConstants, Specs.BLAKE3.roundConstants, Blake2G.State.Proofs.update,
      columnOutputs, diagonalOutputs, gOutput, columnGAssignment, diagonalGAssignment,
      diagonalGBase, columnGBase, Blake2G.Proofs.assemble, Fin.getElem_fin,
      Arithmetic.Word.mk.injEq]
    all_goals constructor
    all_goals apply congrArg ZMod.val
    all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, Blake2G.Proofs.secondAlo, Blake2G.Proofs.secondAhi,
      Blake2G.Proofs.secondClo, Blake2G.Proofs.secondChi, Blake2G.Proofs.firstAlo,
      Blake2G.Proofs.firstAhi, Blake2G.Proofs.firstClo, Blake2G.Proofs.firstChi,
      diagonalGBase, columnGAssignment, columnGBase, Blake2G.Proofs.assemble] at low high ⊢
    all_goals solve
      | linear_combination low
      | linear_combination -low
      | linear_combination high
      | linear_combination -high
  apply Vector.ext
  intro i hi
  exact word ⟨i, hi⟩

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
