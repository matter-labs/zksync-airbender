module
public import Slop.Delegation.Values
public import Slop.Blake2G.Soundness
public import Slop.Blake2G.Control
public import Mathlib.Tactic.IntervalCases
public import Slop.Trace.Values

@[expose] public section

namespace Airbender.Blake2G.Proofs
open Trace Arithmetic
set_option warningAsError true

private theorem native_write_word (w : Nat → ZMod p) (port : MemoryPort) :
    ((⟨.blakeG, w⟩ : Delegation.Row p).writeToken port).word =
      ⟨((port.writeValue.getD port.readValue).evaluate w)[0].val,
        ((port.writeValue.getD port.readValue).evaluate w)[1].val⟩ := by
  simp [Delegation.Row.writeToken, MemoryToken.word, MemoryPort.writeCode, WordColumns.code]

/-- The written columns of port `k`: the four state words (ports 1 to 4), x12 (port 8), or none. -/
private def portWrite : Nat → Option WordColumns
  | 1 => some (.u16 #v[17, 18])
  | 2 => some (.u16 #v[21, 22])
  | 3 => some (.u16 #v[25, 26])
  | 4 => some (.u16 #v[29, 30])
  | 8 => some (.u16 #v[5, 6])
  | _ => none

private theorem ports_size : importedConstraintsMemoryPorts.size = 9 := rfl

private theorem port_writes (k : Nat) (hk : k < importedConstraintsMemoryPorts.size) :
    importedConstraintsMemoryPorts[k].writeValue = portWrite k := by
  rw [ports_size] at hk
  interval_cases k <;> rfl

theorem memory_write_rule [Fact p.Prime] (hp : 33554432 ≤ p)
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
  have bound := reads port member
  obtain ⟨k, size, rfl⟩ := Array.mem_iff_getElem.mp member
  rw [native_write_word, port_writes k size]
  have index : k < 9 := by rwa [ports_size] at size
  interval_cases k
  · simpa only [Trace.Proofs.read_word, portWrite, Option.getD_none] using bound
  · exact state.1
  · exact state.2.1
  · exact state.2.2.1
  · exact state.2.2.2
  · simpa only [Trace.Proofs.read_word, portWrite, Option.getD_none] using bound
  · simpa only [Trace.Proofs.read_word, portWrite, Option.getD_none] using bound
  · simpa only [Trace.Proofs.read_word, portWrite, Option.getD_none] using bound
  · exact ⟨cb, cbHigh⟩

theorem memory_rules [Fact p.Prime] (hp : 33554432 ≤ p)
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
