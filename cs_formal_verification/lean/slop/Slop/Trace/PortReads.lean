import Slop.Trace.RowHistory

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail

/-- A three-port instruction reads one pre-state when its first two ports
    only refresh clocks. This depends on imported port shape, not ISA behavior. -/
theorem native_history_read {cells : List Cell} {columns : TraceColumns}
    {ports : Array MemoryPort} {w : Nat → ZMod p} (epoch : Nat)
    {first second destination : MemoryPort}
    (shape : ports = #[first, second, destination])
    (firstReadonly : first.writeValue = none) (secondReadonly : second.writeValue = none)
    {before after : State}
    (history : SailHistory cells (nativeRowEvents epoch columns ports w).reverse before after)
    {port : MemoryPort} (present : port ∈ ports) {cell : Cell}
    (address : port.address.code w = cell.addressCode) :
    cell.read before = .ok (memoryWord (port.readCode w)) before := by
  rw [shape] at history present
  dsimp [nativeRowEvents] at history
  obtain ⟨left, right, target, _, _, _, leftAddress, rightAddress, targetAddress,
    leftRead, rightRead, targetRead, _⟩ := sail_history_row_reads history
      (by simp [MemoryPort.readCode, MemoryPort.writeCode, firstReadonly])
      (by simp [MemoryPort.readCode, MemoryPort.writeCode, secondReadonly])
  simp at present
  rcases present with rfl | rfl | rfl
  · have same := cell_address_injective (leftAddress.trans address)
    subst left
    exact leftRead
  · have same := cell_address_injective (rightAddress.trans address)
    subst right
    exact rightRead
  · have same := cell_address_injective (targetAddress.trans address)
    subst target
    exact targetRead

theorem native_history_write {cells : List Cell} {columns : TraceColumns}
    {ports : Array MemoryPort} {w : Nat → ZMod p} (epoch : Nat)
    {first second destination : MemoryPort}
    (shape : ports = #[first, second, destination])
    (firstReadonly : first.writeValue = none) (secondReadonly : second.writeValue = none)
    {before after : State}
    (history : SailHistory cells (nativeRowEvents epoch columns ports w).reverse before after)
    {port : MemoryPort} (last : ports.toList.getLast? = some port) {cell : Cell}
    (address : port.address.code w = cell.addressCode) :
    run (cell.write (memoryWord (port.writeCode w))) before = .ok () after := by
  rw [shape] at history last
  dsimp [nativeRowEvents] at history
  obtain ⟨_, _, target, _, _, _, _, _, targetAddress, _, _, _, written⟩ :=
    sail_history_row_reads history
      (by simp [MemoryPort.readCode, MemoryPort.writeCode, firstReadonly])
      (by simp [MemoryPort.readCode, MemoryPort.writeCode, secondReadonly])
  simp at last
  subst port
  have same := cell_address_injective (targetAddress.trans address)
  subst target
  exact written

/-- A native RAM address is canonical because its token comes from the public
    initial image. This derives the actual Sail byte address and domain member. -/
theorem row_ram_cell {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    [ClockLaws Kind p] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    {row : Row p Kind} (member : row ∈ trace.rows) {port : MemoryPort} (present : port ∈ row.ports)
    (ram : ∃ code, port.address.code row.assignment = Nat.pair 1 code) :
    Cell.ram (port.address.word row.assignment).toBitVec ∈ cells ∧
      port.address.code row.assignment =
        (Cell.ram (port.address.word row.assignment).toBitVec).addressCode := by
  obtain ⟨cell, belongs, equal⟩ := initialized_cells hp inverse accepted boundary image
    row member port present
  cases cell with
  | register index =>
    obtain ⟨code, actual⟩ := ram
    have impossible := actual.symm.trans equal
    simp [Cell.addressCode, Nat.pair_eq_pair] at impossible
  | ram address =>
    have canonical := address_word equal
    have same : (port.address.word row.assignment).toBitVec = address :=
      (congrArg Arithmetic.Word.toBitVec canonical).trans (Arithmetic.Word.ofBitVec_roundtrip address)
    rw [same]
    exact ⟨belongs, equal⟩

end Airbender.Trace.Proofs
