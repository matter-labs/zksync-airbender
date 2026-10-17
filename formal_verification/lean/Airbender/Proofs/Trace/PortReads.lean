import Airbender.Proofs.Trace.RowHistory

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

/-- Every imported port reads the instruction pre-state, including aliases. -/
theorem row_history_read {cells : List Cell} {row : Row p} (epoch : Nat)
    {before after : State}
    (history : SailHistory cells (rowEvents epoch row).reverse before after)
    {port : MemoryPort} (present : port ∈ row.ports) {cell : Cell}
    (address : port.address.code row.assignment = cell.addressCode) :
    cell.read before = .ok (memoryWord (port.readCode row.assignment)) before := by
  cases row with
  | mk family w =>
    cases family
    all_goals exact native_history_read epoch rfl rfl rfl history present address

/-- The final port writes the native state; the first two refresh only clocks. -/
theorem row_history_write {cells : List Cell} {row : Row p} (epoch : Nat)
    {before after : State}
    (history : SailHistory cells (rowEvents epoch row).reverse before after)
    {port : MemoryPort} (last : row.ports.toList.getLast? = some port) {cell : Cell}
    (address : port.address.code row.assignment = cell.addressCode) :
    run (cell.write (memoryWord (port.writeCode row.assignment))) before = .ok () after := by
  cases row with
  | mk family w =>
    cases family
    all_goals exact native_history_write epoch rfl rfl rfl history last address


/-- The ten-column decoder identifies both actual Sail source registers.
    Their values come from the grouped native history, including aliases. -/
theorem addsub_history_register_reads (hp : Arithmetic.limbBase < p)
    {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.addSub, w⟩ : Row p)).reverse before after)
    {entry : ProgramEntry} (query : (⟨.addSub, w⟩ : Row p).decoderQuery = entry.query) :
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before =
      .ok (memoryWord (AddSub.importedConstraintsMemoryPorts[0].readCode w)) before ∧
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before =
      .ok (memoryWord (AddSub.importedConstraintsMemoryPorts[1].readCode w)) before := by
  obtain ⟨left, right, _⟩ := native_query_indices hp query
  change (w 5).val = entry.data.rs1.toNat at left
  change (w 6).val = entry.data.rs2.toNat at right
  constructor
  · exact row_history_read epoch history
      (port := AddSub.importedConstraintsMemoryPorts[0])
      (by change AddSub.importedConstraintsMemoryPorts[0] ∈ AddSub.importedConstraintsMemoryPorts
          simp [AddSub.importedConstraintsMemoryPorts])
      (cell := Cell.register entry.data.rs1)
      (by change Nat.pair 0 (Nat.pair (w 5).val 0) = Nat.pair 0 (Nat.pair entry.data.rs1.toNat 0)
          rw [left])
  · exact row_history_read epoch history
      (port := AddSub.importedConstraintsMemoryPorts[1])
      (by change AddSub.importedConstraintsMemoryPorts[1] ∈ AddSub.importedConstraintsMemoryPorts
          simp [AddSub.importedConstraintsMemoryPorts])
      (cell := Cell.register entry.data.rs2)
      (by change Nat.pair 0 (Nat.pair (w 6).val 0) = Nat.pair 0 (Nat.pair entry.data.rs2.toNat 0)
          rw [right])

/-- The decoded destination register receives the actual masked native write. -/
theorem addsub_history_register_write (hp : Arithmetic.limbBase < p)
    {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.addSub, w⟩ : Row p)).reverse before after)
    {entry : ProgramEntry} (query : (⟨.addSub, w⟩ : Row p).decoderQuery = entry.query) :
    run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (memoryWord (AddSub.importedConstraintsMemoryPorts[2].writeCode w))) before = .ok () after := by
  have destination := (native_query_indices hp query).2.2
  change (w 7).val = entry.data.rd.toNat at destination
  exact row_history_write epoch history
    (port := AddSub.importedConstraintsMemoryPorts[2]) (by rfl)
    (cell := Cell.register entry.data.rd)
    (by change Nat.pair 0 (Nat.pair (w 7).val 0) = Nat.pair 0 (Nat.pair entry.data.rd.toNat 0)
        rw [destination])

end Airbender.Trace.Proofs
