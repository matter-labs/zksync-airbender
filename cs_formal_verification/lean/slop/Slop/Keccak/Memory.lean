import Slop.Delegation.Values
import Slop.Keccak.Theta
import Slop.Keccak.Chi
import Slop.Keccak.Iota
import Slop.Keccak.Mix
import Slop.Keccak.Rho

namespace Airbender.Keccak.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem written_limb_bounds [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) (active : w 0 = 1)
    (reads : ∀ lane : Fin 6, ∀ limb : Fin 4,
      (w (15 + 8 * lane.val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb])).val < 65536) :
    ∀ lane : Fin 6, ∀ limb : Fin 4,
      (w (17 + 8 * lane.val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb])).val < 65536 := by
  obtain ⟨s, input, _⟩ := (control_update_checks (by omega) h).active active
  have selected := (decoded_control (by omega) s h active input).1 s.mode
  simp only [ite_true] at selected
  cases s with
  | mk mode iteration round =>
    fin_cases mode
    · exact iota_written_bounds hp h active selected reads
    · exact mix_written_bounds hp false h active selected reads
    · exact mix_written_bounds hp true h active selected reads
    · exact theta_written_bounds (by omega) h active selected reads
    · exact rho_written_bounds hp h active selected reads
    · exact chi_written_bounds hp false h active selected reads
    · exact chi_written_bounds hp true h active selected reads

theorem returned_control_bounds [Fact p.Prime] (hp : 4096 ≤ p)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 0 = 1) : (w 5).val < limbBase ∧ (w 6).val < limbBase := by
  obtain ⟨s, _, output⟩ := (control_update_checks hp h).active active
  have bound : s.nextPacked < 4096 := by
    cases s with
    | mk mode iteration round =>
      have := round.isLt
      fin_cases mode <;> fin_cases iteration <;> simp [ControlState.nextPacked] <;> omega
  rw [output, (control_high_zero h).2]
  simp only [ZMod.val_zero, limbBase]
  omega

private theorem native_write_word (w : Nat → ZMod p) (port : MemoryPort) :
    ((⟨.keccak, w⟩ : Delegation.Row p).writeToken port).word =
      ⟨((port.writeValue.getD port.readValue).evaluate w)[0].val,
        ((port.writeValue.getD port.readValue).evaluate w)[1].val⟩ := by
  simp [Delegation.Row.writeToken, MemoryToken.word, MemoryPort.writeCode, WordColumns.code]

theorem memory_write_rule [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (clockConstraints (setupTable control))) (active : w 0 = 1)
    (reads : ∀ port ∈ importedConstraintsMemoryPorts, (readToken w port).word.Bounded) :
    ∀ port ∈ importedConstraintsMemoryPorts,
      ((⟨.keccak, w⟩ : Delegation.Row p).writeToken port).word.Bounded := by
  have core := Verification.holds_of_sublist holds (List.sublist_append_left
    (importedConstraints (setupTable control)) importedConstraintsTimestampLookups)
  have incoming (i : Fin 12) := reads
    (importedConstraintsMemoryPorts[2 + i.val]'(by change 2 + i.val < 14; omega))
    (Array.getElem_mem (by change 2 + i.val < 14; omega))
  have limbReads (lane : Fin 6) (limb : Fin 4) :
      (w (15 + 8 * lane.val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb])).val < 65536 := by
    have low := incoming ⟨2 * lane.val, by omega⟩
    have high := incoming ⟨2 * lane.val + 1, by omega⟩
    fin_cases lane <;> fin_cases limb
    all_goals simp [Trace.Proofs.read_word, importedConstraintsMemoryPorts,
      WordColumns.evaluate, Word.Bounded, limbBase] at low high ⊢
    all_goals first | exact low.1 | exact low.2 | exact high.1 | exact high.2
  have limbs := written_limb_bounds hp core active limbReads
  have words (i : Fin 12) :
      (⟨(w (17 + 4 * i.val)).val, (w (18 + 4 * i.val)).val⟩ : Word).Bounded := by
    fin_cases i
    all_goals constructor
    all_goals first
      | exact limbs 0 0 | exact limbs 0 1 | exact limbs 0 2 | exact limbs 0 3
      | exact limbs 1 0 | exact limbs 1 1 | exact limbs 1 2 | exact limbs 1 3
      | exact limbs 2 0 | exact limbs 2 1 | exact limbs 2 2 | exact limbs 2 3
      | exact limbs 3 0 | exact limbs 3 1 | exact limbs 3 2 | exact limbs 3 3
      | exact limbs 4 0 | exact limbs 4 1 | exact limbs 4 2 | exact limbs 4 3
      | exact limbs 5 0 | exact limbs 5 1 | exact limbs 5 2 | exact limbs 5 3
  have control := returned_control_bounds (by omega) core active
  have pointer := reads importedConstraintsMemoryPorts[1] (by simp [importedConstraintsMemoryPorts])
  intro port member
  simp [importedConstraintsMemoryPorts] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | simpa [native_write_word, WordColumns.evaluate, Word.Bounded] using control
    | simpa [native_write_word, Trace.Proofs.read_word, importedConstraintsMemoryPorts,
        WordColumns.evaluate] using pointer
    | simpa [native_write_word, WordColumns.evaluate] using words 0
    | simpa [native_write_word, WordColumns.evaluate] using words 1
    | simpa [native_write_word, WordColumns.evaluate] using words 2
    | simpa [native_write_word, WordColumns.evaluate] using words 3
    | simpa [native_write_word, WordColumns.evaluate] using words 4
    | simpa [native_write_word, WordColumns.evaluate] using words 5
    | simpa [native_write_word, WordColumns.evaluate] using words 6
    | simpa [native_write_word, WordColumns.evaluate] using words 7
    | simpa [native_write_word, WordColumns.evaluate] using words 8
    | simpa [native_write_word, WordColumns.evaluate] using words 9
    | simpa [native_write_word, WordColumns.evaluate] using words 10
    | simpa [native_write_word, WordColumns.evaluate] using words 11

end Airbender.Keccak.Proofs
