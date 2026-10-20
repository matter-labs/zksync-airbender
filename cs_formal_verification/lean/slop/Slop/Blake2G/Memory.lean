import Slop.Delegation.Values
import Slop.Blake2G.Soundness
import Slop.Blake2G.Control

namespace Airbender.Blake2G.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

private theorem native_write_word (w : Nat → ZMod p) (port : MemoryPort) :
    ((⟨.blakeG, w⟩ : Delegation.Row p).writeToken port).word =
      ⟨((port.writeValue.getD port.readValue).evaluate w)[0].val,
        ((port.writeValue.getD port.readValue).evaluate w)[1].val⟩ := by
  simp [Delegation.Row.writeToken, MemoryToken.word, MemoryPort.writeCode, WordColumns.code]

theorem memory_write_rule [Fact p.Prime] (hp : 4194304 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (clockConstraints (setupTable Control.controllerRows)))
    (reads : ∀ port ∈ importedConstraintsMemoryPorts, (readToken w port).word.Bounded) :
    ∀ port ∈ importedConstraintsMemoryPorts,
      ((⟨.blakeG, w⟩ : Delegation.Row p).writeToken port).word.Bounded := by
  have core := Verification.holds_of_sublist holds (List.sublist_append_left
    (importedConstraints (setupTable Control.controllerRows)) importedConstraintsTimestampLookups)
  have state := mixing_output_bounds (by omega) inverse (mixing_holds core)
  obtain ⟨key, _, outputs⟩ := Control.Proofs.control_columns (by omega) core
  have control := outputs 0
  change w 5 = ((Control.controllerRows key)[0] : ZMod p) at control
  have cb : (w 5).val < limbBase := by
    have canonical : (Control.controllerRows key)[0] < p :=
      lt_of_lt_of_le (Control.Proofs.controller_bounded key 0) (by omega)
    rw [control, ZMod.val_natCast, Nat.mod_eq_of_lt canonical]
    exact lt_trans (Control.Proofs.controller_bounded key 0) (by decide)
  have high := (control_high_zero core).2
  have cbHigh : (w 6).val < limbBase := by simp [show w 6 = 0 from high, limbBase]
  intro port member
  simp [importedConstraintsMemoryPorts] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (simpa [native_write_word, Trace.Proofs.read_word, WordColumns.evaluate,
         importedConstraintsMemoryPorts] using
         reads importedConstraintsMemoryPorts[0] (by simp [importedConstraintsMemoryPorts]))
    | (simpa [native_write_word, Trace.Proofs.read_word, WordColumns.evaluate,
         importedConstraintsMemoryPorts] using
         reads importedConstraintsMemoryPorts[5] (by simp [importedConstraintsMemoryPorts]))
    | (simpa [native_write_word, Trace.Proofs.read_word, WordColumns.evaluate,
         importedConstraintsMemoryPorts] using
         reads importedConstraintsMemoryPorts[6] (by simp [importedConstraintsMemoryPorts]))
    | (simpa [native_write_word, Trace.Proofs.read_word, WordColumns.evaluate,
         importedConstraintsMemoryPorts] using
         reads importedConstraintsMemoryPorts[7] (by simp [importedConstraintsMemoryPorts]))
    | simpa [native_write_word, WordColumns.evaluate] using state.1
    | simpa [native_write_word, WordColumns.evaluate] using state.2.1
    | simpa [native_write_word, WordColumns.evaluate] using state.2.2.1
    | simpa [native_write_word, WordColumns.evaluate] using state.2.2.2
    | (simpa [native_write_word, WordColumns.evaluate, Word.Bounded,
         Variables.controlWriteHi, high] using
         (And.intro cb cbHigh))

theorem memory_rules [Fact p.Prime] (hp : 4194304 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1) {data : Delegation.MemoryData p}
    (accepted : Delegation.MemoryAccepted data)
    (families : ∀ row ∈ data.rows, row.family = .blakeG)
    (table : data.setup.blakeG = setupTable Control.controllerRows) :
    Delegation.Proofs.WriteBoundsFromReads data := by
  intro row member reads
  cases row with
  | mk family w =>
    have selected := families ⟨family, w⟩ member
    change family = .blakeG at selected
    subst family
    have h := accepted.constraints ⟨.blakeG, w⟩ member
    change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (clockConstraints data.setup.blakeG) at h
    rw [table] at h
    exact memory_write_rule hp inverse h reads

end Airbender.Blake2G.Proofs
