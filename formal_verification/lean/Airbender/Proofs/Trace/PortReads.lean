import Airbender.Proofs.Trace.RowHistory

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail

/-- Every imported port reads the instruction pre-state. Canonical cell coding
    identifies the actual Sail register/RAM accessor, including aliased ports. -/
theorem row_history_read {cells : List Cell} {row : Row p} (epoch : Nat)
    {before after : State}
    (history : SailHistory cells (rowEvents epoch row).reverse before after)
    {port : MemoryPort} (present : port ∈ row.ports) {cell : Cell}
    (address : port.address.code row.assignment = cell.addressCode) :
    cell.read before = .ok (memoryWord (port.readCode row.assignment)) before := by
  cases row with
  | mk family w =>
    cases family
    all_goals
      dsimp [rowEvents, Row.ports, AddSub.importedConstraintsMemoryPorts,
        WordMemory.importedConstraintsMemoryPorts] at history
      obtain ⟨left, right, destination, _, _, _, leftAddress, rightAddress, destinationAddress,
        leftRead, rightRead, destinationRead, _⟩ := sail_history_row_reads history rfl rfl
      simp [Row.ports, AddSub.importedConstraintsMemoryPorts,
        WordMemory.importedConstraintsMemoryPorts] at present
      rcases present with rfl | rfl | rfl
      · have same := cell_address_injective (leftAddress.trans address)
        subst left
        exact leftRead
      · have same := cell_address_injective (rightAddress.trans address)
        subst right
        exact rightRead
      · have same := cell_address_injective (destinationAddress.trans address)
        subst destination
        exact destinationRead

/-- The final imported port supplies the actual native state update. The other
    two ports only refresh timestamps and leave the Sail state unchanged. -/
theorem row_history_write {cells : List Cell} {row : Row p} (epoch : Nat)
    {before after : State}
    (history : SailHistory cells (rowEvents epoch row).reverse before after)
    {port : MemoryPort} (last : row.ports.toList.getLast? = some port) {cell : Cell}
    (address : port.address.code row.assignment = cell.addressCode) :
    run (cell.write (memoryWord (port.writeCode row.assignment))) before = .ok () after := by
  cases row with
  | mk family w =>
    cases family
    all_goals
      dsimp [rowEvents, Row.ports, AddSub.importedConstraintsMemoryPorts,
        WordMemory.importedConstraintsMemoryPorts] at history
      obtain ⟨_, _, destination, _, _, _, _, _, destinationAddress, _, _, _, written⟩ :=
        sail_history_row_reads history rfl rfl
      simp [Row.ports, AddSub.importedConstraintsMemoryPorts,
        WordMemory.importedConstraintsMemoryPorts] at last
      subst port
      have same := cell_address_injective (destinationAddress.trans address)
      subst destination
      exact written

/-- Both selected circuit families use their first native port for rs1.
    Decoder membership identifies its actual Sail register index. -/
theorem row_history_source_read (hp : Arithmetic.limbBase < p)
    {cells : List Cell} {row : Row p} (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch row).reverse before after)
    {entry : ProgramEntry} (query : row.decoderQuery = entry.query)
    {port : MemoryPort} (first : row.ports.toList.head? = some port) :
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before =
      .ok (memoryWord (port.readCode row.assignment)) before := by
  have index := (query_register_indices hp query).1
  have address : port.address = .register row.decoderColumns.rs1 := by
    cases row with
    | mk family w =>
      cases family
      all_goals
        simp [Row.ports, AddSub.importedConstraintsMemoryPorts,
          WordMemory.importedConstraintsMemoryPorts] at first
        subst port
        rfl
  have present : port ∈ row.ports := by
    cases row with
    | mk family w =>
      cases family
      all_goals
        simp [Row.ports, AddSub.importedConstraintsMemoryPorts,
          WordMemory.importedConstraintsMemoryPorts] at first
        subst port
        simp [Row.ports, AddSub.importedConstraintsMemoryPorts,
          WordMemory.importedConstraintsMemoryPorts]
  have same : port.address.code row.assignment = (Cell.register entry.data.rs1).addressCode := by
    rw [address]
    simp [MemoryAddress.code, Cell.addressCode, index]
  exact row_history_read epoch history present same

end Airbender.Trace.Proofs
