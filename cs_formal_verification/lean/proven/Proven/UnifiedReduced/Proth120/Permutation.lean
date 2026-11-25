module
public import Human.Trace.UnifiedReduced.Proth120Permutation
public import Proven.UnifiedReduced
public import Proven.Trace.RVHistory

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Trace Compiler.NativeMemory Verification

private def pcToken (t : MemoryToken proth120Modulus) : Bool := (Nat.unpair t.address).1 == 2

private theorem pc_filter (l : List (PCState.State proth120Modulus)) :
    (l.map stateToken).filter pcToken = l.map stateToken := by
  apply List.filter_eq_self.mpr
  simp [stateToken, pcToken]

set_option maxRecDepth 8192 in
private theorem no_pc_writes {t : WrapTrace} {r : Row proth120Modulus Kind}
    (holds : FlatOperation.ConstraintsHoldFlat (environment r.assignment) (r.constraints t.rom)) :
    ∀ token ∈ r.writes, pcToken token = false := by
  change FlatOperation.ConstraintsHoldFlat _ (importedConstraints t.rom ++ importedConstraintsTimestampLookups) at holds
  have core := Standard.holds (holds_of_sublist holds (List.sublist_append_left (importedConstraints t.rom) importedConstraintsTimestampLookups))
  let w := r.assignment
  have hb : w 28 = 0 ∨ w 28 = 1 := UnifiedReduced.Standard.Proofs.local_flags (profile := .proth120) core 18
  have hc : w 29 = 0 ∨ w 29 = 1 := UnifiedReduced.Standard.Proofs.local_flags (profile := .proth120) core 19
  intro tok mem
  obtain ⟨port, present, rfl⟩ := List.mem_map.mp mem
  simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · simp [pcToken, writeToken, MemoryAddress.code]
  · rcases hb with h | h <;> simp [pcToken, writeToken, MemoryAddress.code, ← show w = r.assignment from rfl, h]
    decide
  · rcases hc with h | h <;> simp [pcToken, writeToken, MemoryAddress.code, ← show w = r.assignment from rfl, h]
    decide

theorem WrapPermutation.of_parts {t : WrapTrace}
    (states : (t.initial :: t.rows.map Row.finish).Perm (t.terminal :: t.rows.map Row.start))
    (memory : (t.initialMemory ++ t.rows.flatMap Row.writes).Perm (t.terminalMemory ++ t.rows.flatMap Row.reads)) :
    WrapPermutation t := by
  simpa [WrapPermutation, List.append_assoc] using (states.map stateToken).append memory

/-- The PC address tag cannot occur among boot cells or architectural writes. Both sides have
    the same number of PC states, which also rules out PC tokens among the terminal memory. -/
theorem WrapPermutation.split {t : WrapTrace} {initial cells} (perm : WrapPermutation t)
    (image : initialImageRV initial cells = some t.initialMemory)
    (holds : ∀ r ∈ t.rows, FlatOperation.ConstraintsHoldFlat (environment r.assignment) (r.constraints t.rom)) :
    (t.initial :: t.rows.map Row.finish).Perm (t.terminal :: t.rows.map Row.start) ∧
    (t.initialMemory ++ t.rows.flatMap Row.writes).Perm (t.terminalMemory ++ t.rows.flatMap Row.reads) := by
  let left := t.initial :: t.rows.map Row.finish
  let right := t.terminal :: t.rows.map Row.start
  let writes := t.initialMemory ++ t.rows.flatMap Row.writes
  let reads := t.terminalMemory ++ t.rows.flatMap Row.reads
  have total : (left.map stateToken ++ writes).Perm (right.map stateToken ++ reads) := by
    simpa [WrapPermutation, left, right, writes, reads, List.append_assoc] using perm
  have empty : writes.filter pcToken = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro tok mem
    rcases List.mem_append.mp mem with seed | written
    · have addr : tok.address ∈ cells.map Cell.addressCode := by
        rw [← Trace.Proofs.rvImage_addresses image]
        exact List.mem_map_of_mem seed
      obtain ⟨cell, _, same⟩ := List.mem_map.mp addr
      cases cell <;> simp [pcToken, ← same, Cell.addressCode]
    · obtain ⟨row, hr, hw⟩ := List.mem_flatMap.mp written
      simp [no_pc_writes (holds row hr) tok hw]
  have filtered := total.filter pcToken
  rw [List.filter_append _ writes, List.filter_append _ reads, pc_filter, pc_filter, empty, List.append_nil] at filtered
  have len := filtered.length_eq
  simp [left, right] at len
  have rightEmpty : reads.filter pcToken = [] := List.filter_eq_nil_iff.mpr fun tok mem => by simp [len tok mem]
  rw [rightEmpty, List.append_nil] at filtered
  let recover (tok : MemoryToken proth120Modulus) : PCState.State proth120Modulus :=
    ⟨((Nat.unpair tok.value).1, (Nat.unpair tok.value).2), tok.time⟩
  have unmap : recover ∘ stateToken = id := by funext st; simp [recover, stateToken]
  exact ⟨by simpa [List.map_map, unmap] using filtered.map recover,
    (List.perm_append_left_iff _).mp ((filtered.symm.append (List.Perm.refl writes)).trans total)⟩

end Airbender.UnifiedReduced.Proth120
