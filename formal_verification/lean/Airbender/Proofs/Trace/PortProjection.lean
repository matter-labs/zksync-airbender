import Airbender.Proofs.Trace.PortReads

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail

/-- Any list of native readonly refreshes stutters. Every retained read uses
    the original Sail pre-state, including aliases and filtered address domains. -/
theorem readonly_history_reads {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after)
    (readonly : ∀ event ∈ events, event.2.2.1 = event.2.2.2) :
    after = before ∧ ∀ event ∈ events, ∃ cell ∈ cells, cell.addressCode = event.2.1 ∧
      cell.read before = .ok (memoryWord event.2.2.1) before := by
  induction history with
  | nil => exact ⟨rfl, by simp⟩
  | @cons event rest before middle after past cell member address read written ih =>
    obtain ⟨same, reads⟩ := ih (fun previous present => readonly previous (List.mem_cons_of_mem _ present))
    subst middle
    have refresh := cell_write_same read
    rw [readonly event (List.mem_cons_self)] at refresh
    have same := (EStateM.Result.ok.inj (refresh.symm.trans written)).2
    subst after
    refine ⟨rfl, ?_⟩
    intro previous present
    rcases List.mem_cons.mp present with rfl | earlier
    · exact ⟨cell, member, address, read⟩
    · exact reads previous earlier

/-- Whole-address filtering may remove either readonly input port. The final
    kept port still writes the original pre-state and all kept reads use it. -/
theorem projected_row_reads {cells : List Cell} {a b c : MemoryAccess}
    {before after : State} (keep : Nat → Bool)
    (history : SailHistory cells ([c, b, a].filter fun event => keep event.2.1) before after)
    (firstReadonly : a.2.2.1 = a.2.2.2) (secondReadonly : b.2.2.1 = b.2.2.2)
    (destination : keep c.2.1 = true) :
    (∀ event ∈ [c, b, a], keep event.2.1 = true →
      ∃ cell ∈ cells, cell.addressCode = event.2.1 ∧
        cell.read before = .ok (memoryWord event.2.2.1) before) ∧
    ∃ cell ∈ cells, cell.addressCode = c.2.1 ∧
      run (cell.write (memoryWord c.2.2.2)) before = .ok () after := by
  have shape : ([c, b, a].filter fun event => keep event.2.1) =
      c :: ([b, a].filter fun event => keep event.2.1) := by
    simp only [List.filter_cons, destination, ↓reduceIte]
  rw [shape] at history
  cases history with
  | cons past target member address read written =>
    have readonly : ∀ event ∈ ([b, a].filter fun event => keep event.2.1),
        event.2.2.1 = event.2.2.2 := by
      intro event present
      have actual := (List.mem_filter.mp present).1
      simp at actual
      rcases actual with rfl | rfl
      · exact secondReadonly
      · exact firstReadonly
    obtain ⟨same, reads⟩ := readonly_history_reads past readonly
    subst_vars
    refine ⟨?_, target, member, address, written⟩
    intro event present selected
    rcases List.mem_cons.mp present with rfl | earlier
    · exact ⟨target, member, address, read⟩
    · exact reads event (List.mem_filter.mpr ⟨earlier, selected⟩)

/-- Recover each retained native port read through its actual imported address.
    All premises here are discharged by family-specific native metadata laws. -/
theorem projected_native_read {cells : List Cell} {columns : TraceColumns}
    {ports : Array MemoryPort} {w : Nat → ZMod p} (epoch : Nat) (keep : Nat → Bool)
    {first second destination : MemoryPort} (shape : ports = #[first, second, destination])
    (firstReadonly : first.writeValue = none) (secondReadonly : second.writeValue = none)
    (destinationKept : keep (destination.address.code w) = true)
    {before after : State}
    (history : SailHistory cells
      ((nativeRowEvents epoch columns ports w).reverse.filter fun event => keep event.2.1) before after)
    {port : MemoryPort} (present : port ∈ ports) (kept : keep (port.address.code w) = true)
    {cell : Cell} (address : port.address.code w = cell.addressCode) :
    cell.read before = .ok (memoryWord (port.readCode w)) before := by
  rw [shape] at history present
  dsimp [nativeRowEvents] at history
  have reads := (projected_row_reads keep history
    (by simp [MemoryPort.readCode, MemoryPort.writeCode, firstReadonly])
    (by simp [MemoryPort.readCode, MemoryPort.writeCode, secondReadonly]) destinationKept).1
  simp at present
  rcases present with rfl | rfl | rfl
  all_goals
    obtain ⟨actual, _, same, read⟩ := reads
      ((epoch + (port.event columns w).1, port.address.code w, port.readCode w, port.writeCode w) : MemoryAccess)
      (by simp) kept
    have equal := cell_address_injective (same.trans address)
    subst actual
    exact read

theorem projected_native_write {cells : List Cell} {columns : TraceColumns}
    {ports : Array MemoryPort} {w : Nat → ZMod p} (epoch : Nat) (keep : Nat → Bool)
    {first second destination : MemoryPort} (shape : ports = #[first, second, destination])
    (firstReadonly : first.writeValue = none) (secondReadonly : second.writeValue = none)
    (destinationKept : keep (destination.address.code w) = true)
    {before after : State}
    (history : SailHistory cells
      ((nativeRowEvents epoch columns ports w).reverse.filter fun event => keep event.2.1) before after)
    {cell : Cell} (address : destination.address.code w = cell.addressCode) :
    run (cell.write (memoryWord (destination.writeCode w))) before = .ok () after := by
  rw [shape] at history
  dsimp [nativeRowEvents] at history
  obtain ⟨actual, _, same, written⟩ := (projected_row_reads keep history
    (by simp [MemoryPort.readCode, MemoryPort.writeCode, firstReadonly])
    (by simp [MemoryPort.readCode, MemoryPort.writeCode, secondReadonly]) destinationKept).2
  have equal := cell_address_injective (same.trans address)
  subst actual
  exact written

end Airbender.Trace.Proofs
