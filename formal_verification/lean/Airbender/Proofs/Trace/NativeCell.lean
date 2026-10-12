import Airbender.Proofs.Trace.PortReads

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail

theorem native_history_cell {cells : List Cell} {columns : TraceColumns}
    {ports : Array MemoryPort} {w : Nat → ZMod p} (epoch : Nat)
    {first second destination : MemoryPort}
    (shape : ports = #[first, second, destination])
    (firstReadonly : first.writeValue = none) (secondReadonly : second.writeValue = none)
    {before after : State}
    (history : SailHistory cells (nativeRowEvents epoch columns ports w).reverse before after)
    {port : MemoryPort} (present : port ∈ ports) :
    ∃ cell ∈ cells, port.address.code w = cell.addressCode := by
  rw [shape] at history present
  dsimp [nativeRowEvents] at history
  obtain ⟨left, right, target, lm, rm, tm, la, ra, ta, _, _, _, _⟩ :=
    sail_history_row_reads history
      (by simp [MemoryPort.readCode, MemoryPort.writeCode, firstReadonly])
      (by simp [MemoryPort.readCode, MemoryPort.writeCode, secondReadonly])
  simp at present
  rcases present with rfl | rfl | rfl
  · exact ⟨left, lm, la.symm⟩
  · exact ⟨right, rm, ra.symm⟩
  · exact ⟨target, tm, ta.symm⟩

end Airbender.Trace.Proofs
