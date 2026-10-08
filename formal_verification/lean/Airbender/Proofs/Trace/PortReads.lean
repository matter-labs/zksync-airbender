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

/-- A native RAM address is canonical because its token comes from the public
    initial image. This derives the actual Sail byte address and domain member. -/
theorem row_ram_cell [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    {row : Row p} (member : row ∈ trace.rows) {port : MemoryPort} (present : port ∈ row.ports)
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

theorem row_history_ram_read [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    {row : Row p} (member : row ∈ trace.rows) {port : MemoryPort} (present : port ∈ row.ports)
    (ram : ∃ code, port.address.code row.assignment = Nat.pair 1 code)
    {before after : State}
    (history : SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after) :
    (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4
      (port.address.word row.assignment).toBitVec.toNat).run before =
        .ok (memoryWord (port.readCode row.assignment)) before :=
  row_history_read trace.memoryEpoch history present
    (row_ram_cell hp inverse accepted boundary image member present ram).2

theorem row_history_ram_write [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    {row : Row p} (member : row ∈ trace.rows) {port : MemoryPort} (present : port ∈ row.ports)
    (last : row.ports.toList.getLast? = some port)
    (ram : ∃ code, port.address.code row.assignment = Nat.pair 1 code)
    {before after : State}
    (history : SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after) :
    run (writeMemory (size := 4) (port.address.word row.assignment).toBitVec
      (memoryWord (port.writeCode row.assignment))) before = .ok () after :=
  row_history_write trace.memoryEpoch history last
    (row_ram_cell hp inverse accepted boundary image member present ram).2

/-- The second SW port reads rs2; the final LW port reads rd before its update.
    Both identities follow from native equations and the same decoder query. -/
theorem word_history_register_read [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {rom : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} (store : Bool)
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (WordMemory.importedConstraints rom))
    (selected : w 10 = if store then 1 else 0)
    {entry : ProgramEntry} (query : (⟨.wordMemory, w⟩ : Row p).decoderQuery = entry.query)
    {cells : List Cell} (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.wordMemory, w⟩ : Row p)).reverse before after) :
    run (SailRV32.Functions.rX_bits (.Regidx (if store then entry.data.rs2 else entry.data.rd))) before =
      .ok (Arithmetic.Word.mk (w (if store then 23 else 29)).val
        (w (if store then 24 else 30)).val).toBitVec before := by
  have indices := query_register_indices hp query
  change (w 5).val = entry.data.rs1.toNat ∧ (w 6).val = entry.data.rs2.toNat ∧
    (w 7).val = entry.data.rd.toNat at indices
  have wiring := WordMemory.Proofs.register_address store constraints selected
  cases store
  · have address : WordMemory.importedConstraintsMemoryPorts[2].address.code w =
        (Cell.register entry.data.rd).addressCode := by
      simp only [Bool.false_eq_true, if_false] at selected wiring
      simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode,
        Cell.addressCode, selected, wiring.1, wiring.2, indices.2.2]
    have read := row_history_read epoch history
      (port := WordMemory.importedConstraintsMemoryPorts[2]) (by
        simp [Row.ports, WordMemory.importedConstraintsMemoryPorts]) address
    simpa [WordMemory.importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode,
      memoryWord, Nat.unpair_pair, Cell.read] using read
  · have address : WordMemory.importedConstraintsMemoryPorts[1].address.code w =
        (Cell.register entry.data.rs2).addressCode := by
      simp only [if_true] at selected wiring
      simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode,
        Cell.addressCode, selected, wiring.1, wiring.2, indices.2.1]
    have read := row_history_read epoch history
      (port := WordMemory.importedConstraintsMemoryPorts[1]) (by
        simp [Row.ports, WordMemory.importedConstraintsMemoryPorts]) address
    simpa [WordMemory.importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode,
      memoryWord, Nat.unpair_pair, Cell.read] using read

/-- Native LW's final write is the actual decoded destination-register update. -/
theorem word_history_load_write [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {rom : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (WordMemory.importedConstraints rom)) (selected : w 10 = 0)
    {entry : ProgramEntry} (query : (⟨.wordMemory, w⟩ : Row p).decoderQuery = entry.query)
    {cells : List Cell} (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.wordMemory, w⟩ : Row p)).reverse before after) :
    run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (Arithmetic.Word.mk (w 31).val (w 32).val).toBitVec) before = .ok () after := by
  have indices := query_register_indices hp query
  change (w 5).val = entry.data.rs1.toNat ∧ (w 6).val = entry.data.rs2.toNat ∧
    (w 7).val = entry.data.rd.toNat at indices
  have wiring := WordMemory.Proofs.register_address false constraints selected
  simp only [Bool.false_eq_true, if_false] at wiring
  have address : WordMemory.importedConstraintsMemoryPorts[2].address.code w =
      (Cell.register entry.data.rd).addressCode := by
    simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode,
      Cell.addressCode, selected, wiring.1, wiring.2, indices.2.2]
  have write := row_history_write epoch history
    (port := WordMemory.importedConstraintsMemoryPorts[2]) rfl address
  simpa [WordMemory.importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode,
    memoryWord, Cell.write] using write

/-- Arithmetic rs2 and destination effects use the same native-port semantics
    as LW/SW. The public decoder query supplies the actual register indices. -/
theorem addsub_history_registers (hp : Arithmetic.limbBase < p)
    {w : Nat → ZMod p} {entry : ProgramEntry}
    (query : (⟨.addSub, w⟩ : Row p).decoderQuery = entry.query)
    {cells : List Cell} (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.addSub, w⟩ : Row p)).reverse before after) :
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before =
      .ok (Arithmetic.Word.mk (w 29).val (w 30).val).toBitVec before ∧
    run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (Arithmetic.Word.mk (w 33).val (w 34).val).toBitVec) before = .ok () after := by
  have indices := query_register_indices hp query
  change (w 5).val = entry.data.rs1.toNat ∧ (w 6).val = entry.data.rs2.toNat ∧
    (w 7).val = entry.data.rd.toNat at indices
  have rightAddress : AddSub.importedConstraintsMemoryPorts[1].address.code w =
      (Cell.register entry.data.rs2).addressCode := by
    simp [AddSub.importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, indices.2.1]
  have destinationAddress : AddSub.importedConstraintsMemoryPorts[2].address.code w =
      (Cell.register entry.data.rd).addressCode := by
    simp [AddSub.importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, indices.2.2]
  have right := row_history_read epoch history
    (port := AddSub.importedConstraintsMemoryPorts[1])
    (by simp [Row.ports, AddSub.importedConstraintsMemoryPorts]) rightAddress
  have written := row_history_write epoch history
    (port := AddSub.importedConstraintsMemoryPorts[2]) rfl destinationAddress
  constructor
  · simpa [AddSub.importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode,
      memoryWord, Cell.read] using right
  · simpa [AddSub.importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode,
      memoryWord, Cell.write] using written

end Airbender.Trace.Proofs
