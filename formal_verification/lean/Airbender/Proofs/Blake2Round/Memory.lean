import Airbender.Proofs.Delegation.Values
import Airbender.Proofs.Blake2Round.Row
import Airbender.Review.Circuits.Blake2Round.Memory

namespace Airbender.Blake2Round.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

theorem extended_write_bounds [Fact p.Prime] (hp : 65536 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    ∀ i : Fin 16, (Preparation.words w Mixing.extendedWrites)[i].Bounded := by
  have bounds (call : Fin 4) := Blake2G.Proofs.mixing_output_bounds hp inverse
    (diagonal_g_holds inverse call holds)
  have b0 := bounds 0
  have b1 := bounds 1
  have b2 := bounds 2
  have b3 := bounds 3
  intro i
  rw [extended_writes holds (Vector.replicate 16 (⟨0, 0⟩ : Word))]
  fin_cases i
  all_goals simp [phaseUpdate, callUpdate, callConstants, Specs.BLAKE3.roundConstants,
    Blake2G.State.Proofs.update, diagonalOutputs, gOutput]
  all_goals first
    | exact b0.1 | exact b0.2.1 | exact b0.2.2.1 | exact b0.2.2.2
    | exact b1.1 | exact b1.2.1 | exact b1.2.2.1 | exact b1.2.2.2
    | exact b2.1 | exact b2.2.1 | exact b2.2.2.1 | exact b2.2.2.2
    | exact b3.1 | exact b3.2.1 | exact b3.2.2.1 | exact b3.2.2.2

private theorem native_write_word (w : Nat → ZMod p) (port : MemoryPort) :
    ((⟨.blakeRound, w⟩ : Delegation.Row p).writeToken port).word =
      ⟨((port.writeValue.getD port.readValue).evaluate w)[0].val,
        ((port.writeValue.getD port.readValue).evaluate w)[1].val⟩ := by
  simp [Delegation.Row.writeToken, MemoryToken.word, MemoryPort.writeCode, WordColumns.code]

theorem state_write_bounds [Fact p.Prime] (hp : 65536 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (final : w 152 = 0 ∨ w 152 = 1)
    (reads : ∀ i : Fin 8, (Preparation.words w Variables.stateReads)[i].Bounded) :
    ∀ i : Fin 8, (Preparation.words w Finalization.stateWrites)[i].Bounded := by
  rcases final with disabled | enabled
  · rw [chaining_preserved holds disabled]
    exact reads
  · have ac (i : Fin 8) := (ac_limb_xor hp inverse i holds enabled).2.2.2.1
    have bd (i : Fin 8) := (bd_limb_xor hp inverse i holds enabled).2.2.2.1
    intro i
    fin_cases i
    all_goals simp only [Preparation.words, Finalization.stateWrites, Vector.getElem_map, Vector.getElem_ofFn,
      Word.Bounded, Fin.getElem_fin]
    all_goals constructor
    all_goals first
      | exact ac 0 | exact ac 1 | exact ac 2 | exact ac 3
      | exact ac 4 | exact ac 5 | exact ac 6 | exact ac 7
      | exact bd 0 | exact bd 1 | exact bd 2 | exact bd 3
      | exact bd 4 | exact bd 5 | exact bd 6 | exact bd 7


theorem final_flag_boolean [Fact p.Prime] {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (round : Fin 10)
    (mask : ∀ i : Fin 10, w Variables.roundBits[i] = if i = round then 1 else 0) :
    w 152 = 0 ∨ w 152 = 1 := by
  have equation := Verification.assertion_of_holds holds ⟨2, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at equation
  have reduced := Control.Proofs.control_bits holds 0
  have six := mask 6
  have nine := mask 9
  simp only [Variables.roundBits, Variables.controlBits] at six nine reduced
  change w 139 = 0 ∨ w 139 = 1 at reduced
  rcases reduced with zero | one
  all_goals fin_cases round
  all_goals norm_num at six nine
  all_goals rw [six, nine] at equation
  all_goals try rw [zero] at equation
  all_goals try rw [one] at equation
  all_goals norm_num [Fin.ext_iff] at equation
  all_goals first | exact Or.inl equation | exact Or.inr (by linear_combination -equation)

theorem memory_write_rule [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (clockConstraints setupTable)) (round : Fin 10)
    (mask : ∀ i : Fin 10, w Variables.roundBits[i] = if i = round then 1 else 0)
    (reads : ∀ port ∈ importedConstraintsMemoryPorts, (readToken w port).word.Bounded) :
    ∀ port ∈ importedConstraintsMemoryPorts,
      ((⟨.blakeRound, w⟩ : Delegation.Row p).writeToken port).word.Bounded := by
  have core := Verification.holds_of_sublist holds (List.sublist_append_left
    (importedConstraints setupTable) importedConstraintsTimestampLookups)
  have incoming : ∀ i : Fin 8, (Preparation.words w Variables.stateReads)[i].Bounded := by
    intro i
    have bounds := reads (importedConstraintsMemoryPorts[1 + i.val]'
      (by change 1 + i.val < 43; have := i.isLt; omega))
      (Array.getElem_mem (by change 1 + i.val < 43; have := i.isLt; omega))
    fin_cases i
    all_goals simpa [Trace.Proofs.read_word, importedConstraintsMemoryPorts,
      Preparation.words, Variables.stateReads, WordColumns.evaluate] using bounds
  have state := state_write_bounds (by omega) inverse core (final_flag_boolean core round mask) incoming
  have extended := extended_write_bounds (by omega) inverse core
  have control := Control.Proofs.soundness (by omega) setupTable
    (⟨(w 135).val, (w 136).val⟩ : Word) ⟨(w 137).val, (w 138).val⟩ w
    ⟨core, ⟨rfl, rfl⟩⟩
  have controlBound : (⟨(w 137).val, (w 138).val⟩ : Word).Bounded := by
    rw [control.2]
    simp only [Control.next, Word.Bounded]
    have low : (w 136).val % 8 < 8 := Nat.mod_lt _ (by decide)
    have high : (w 136).val / 8 % 512 < 512 := Nat.mod_lt _ (by decide)
    constructor <;> unfold limbBase <;> omega
  have readonly (i : Fin 43) (absent : importedConstraintsMemoryPorts[i].writeValue = none) :
      ((⟨.blakeRound, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[i]).word.Bounded := by
    have bound := reads importedConstraintsMemoryPorts[i] (Array.getElem_mem i.isLt)
    simp only [Fin.getElem_fin] at absent bound ⊢
    rw [native_write_word, absent]
    simpa only [Trace.Proofs.read_word, Fin.getElem_fin, Option.getD_none] using bound
  intro port present
  obtain ⟨i, size, same⟩ := Array.mem_iff_getElem.mp present
  subst port
  have index : i < 43 := by simpa [importedConstraintsMemoryPorts] using size
  interval_cases i
  · exact readonly 0 rfl
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Finalization.stateWrites] using state 0
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Finalization.stateWrites] using state 1
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Finalization.stateWrites] using state 2
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Finalization.stateWrites] using state 3
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Finalization.stateWrites] using state 4
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Finalization.stateWrites] using state 5
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Finalization.stateWrites] using state 6
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Finalization.stateWrites] using state 7
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Mixing.extendedWrites] using extended 0
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Mixing.extendedWrites] using extended 1
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Mixing.extendedWrites] using extended 2
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Mixing.extendedWrites] using extended 3
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Mixing.extendedWrites] using extended 4
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Mixing.extendedWrites] using extended 5
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Mixing.extendedWrites] using extended 6
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Mixing.extendedWrites] using extended 7
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Mixing.extendedWrites] using extended 8
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Mixing.extendedWrites] using extended 9
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Mixing.extendedWrites] using extended 10
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Mixing.extendedWrites] using extended 11
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Mixing.extendedWrites] using extended 12
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Mixing.extendedWrites] using extended 13
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Mixing.extendedWrites] using extended 14
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      Preparation.words, Mixing.extendedWrites] using extended 15
  · exact readonly 25 rfl
  · exact readonly 26 rfl
  · exact readonly 27 rfl
  · exact readonly 28 rfl
  · exact readonly 29 rfl
  · exact readonly 30 rfl
  · exact readonly 31 rfl
  · exact readonly 32 rfl
  · exact readonly 33 rfl
  · exact readonly 34 rfl
  · exact readonly 35 rfl
  · exact readonly 36 rfl
  · exact readonly 37 rfl
  · exact readonly 38 rfl
  · exact readonly 39 rfl
  · exact readonly 40 rfl
  · exact readonly 41 rfl
  · simpa [native_write_word, importedConstraintsMemoryPorts, WordColumns.evaluate] using controlBound


theorem memory_rules [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1) {data : Delegation.MemoryData p}
    (accepted : Delegation.MemoryAccepted data)
    (families : ∀ row ∈ data.rows, row.family = .blakeRound)
    (table : data.setup.blakeRound = setupTable)
    (rounds : ∀ row ∈ data.rows, ∃ round, Memory.RoundMask row.assignment round) :
    Delegation.Proofs.WriteBoundsFromReads data := by
  intro row member reads
  cases row with
  | mk family w =>
    have selected := families ⟨family, w⟩ member
    change family = .blakeRound at selected
    subst family
    obtain ⟨round, mask⟩ := rounds ⟨.blakeRound, w⟩ member
    have h := accepted.constraints ⟨.blakeRound, w⟩ member
    change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (clockConstraints data.setup.blakeRound) at h
    rw [table] at h
    exact memory_write_rule hp inverse h round mask reads

end Airbender.Blake2Round.Proofs
