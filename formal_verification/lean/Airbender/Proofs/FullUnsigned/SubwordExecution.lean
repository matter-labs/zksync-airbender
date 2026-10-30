import Airbender.Proofs.FullUnsigned.OrdinaryHistory
import Airbender.Proofs.FullUnsigned.CPUWriteRules
import Airbender.Proofs.SubwordMemory.Execution
import Airbender.Proofs.Trace.NativeCell

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

private theorem subword_source {initial : State} {entry : PooledProgramEntry}
    (source : entry.SourceWith initial AddSub.Modular.External.decoderFields)
    (family : entry.data.family = .subwordMemory) :
    ∃ original : SubwordMemory.ProgramEntry,
      original.SourceWith initial SubwordMemory.decoderFields ∧
      entry = original.mapFamily (fun _ => .subwordMemory) := by
  rcases AddSub.Modular.External.Proofs.source_cases source with
    ⟨original, _, equal⟩ | ⟨_, _, equal⟩ | ⟨_, _, equal⟩ | ⟨_, _, equal⟩ | original
  · cases kind : original.data.family <;>
      simp [equal, ProgramEntry.mapFamily, DecoderData.mapFamily, pooledArithmeticFamily, kind] at family
  · simp [equal, ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [equal, ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [equal, ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · exact original

private theorem subword_ram_cell {cells : List Cell} {w : Nat → ZMod babyBearModulus}
    {port : MemoryPort}
    (located : ∃ cell ∈ cells, port.address.code w = cell.addressCode)
    (ram : ∃ code, port.address.code w = Nat.pair 1 code) :
    (port.address.word w).Bounded ∧ Cell.ram (port.address.word w).toBitVec ∈ cells ∧
      port.address.code w = (Cell.ram (port.address.word w).toBitVec).addressCode := by
  obtain ⟨cell, member, equal⟩ := located
  cases cell with
  | register index =>
    obtain ⟨code, actual⟩ := ram
    have impossible := actual.symm.trans equal
    simp [Cell.addressCode, Nat.pair_eq_pair] at impossible
  | ram address =>
    have word := address_word equal
    have same := (congrArg Word.toBitVec word).trans (Word.ofBitVec_roundtrip address)
    refine ⟨word.symm ▸ Word.ofBitVec_bound address, ?_⟩
    rw [same]
    exact ⟨member, equal⟩

variable [Fact babyBearModulus.Prime]
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Native subword execution uses operands and addresses from one shared window. -/
theorem unrolled_subword_execution_from_shared_history
    {initial before after : State} {cells : List Cell}
    {physicalImage : List (MemoryToken babyBearModulus)} {trace : PooledTrace babyBearModulus}
    (image : initialImage initial cells = some physicalImage)
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinaryCells : ∀ address, Cell.ram address ∈ cells → PlatformWordAddress address)
    (configuration : FlatMemoryConfiguration initial)
    {w : Nat → ZMod babyBearModulus} {entry : PooledProgramEntry}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      ((⟨.subwordMemory, w⟩ : Row babyBearModulus PooledFamily).constraints trace.rom))
    (enabled : w SubwordMemory.importedConstraintsTraceColumns.execute = 1)
    (ranges : ∀ port ∈ SubwordMemory.importedConstraintsMemoryPorts, (readToken w port).word.Bounded)
    (source : entry.SourceWith initial AddSub.Modular.External.decoderFields)
    (family : entry.data.family = .subwordMemory)
    (query : (⟨.subwordMemory, w⟩ : Row babyBearModulus PooledFamily).decoderQuery = entry.query)
    {events : List MemoryAccess}
    (past : SailHistory cells events initial before)
    (readonly : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    (native : SailHistory cells
      (rowEvents 1 (⟨.subwordMemory, w⟩ : Row babyBearModulus PooledFamily)).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (Word.mk (w 13).val (w 14).val).toBitVec) := by
  let row : Trace.Row babyBearModulus PooledFamily := ⟨.subwordMemory, w⟩
  obtain ⟨original, originalSource, equal⟩ := subword_source source family
  have originalQuery : SubwordMemory.decoderQuery w = original.query := by
    rw [equal, mapped_query] at query
    exact query
  have core := Verification.holds_of_sublist constraints
    (List.sublist_append_left (SubwordMemory.importedConstraints trace.rom.subwordMemory)
      SubwordMemory.importedConstraintsTimestampLookups)
  rw [subwordSetup] at core
  have addresses : ∀ port ∈ SubwordMemory.importedConstraintsMemoryPorts,
      ∃ cell ∈ cells, port.address.code w = cell.addressCode :=
    fun _ present => native_history_cell 1 rfl rfl rfl native present
  have romReads (cell : Word) (bounded : cell.Bounded) (low : cell.hi < 64)
      (present : Cell.ram cell.toBitVec ∈ cells) :
      (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 cell.toBitVec.toNat).run before =
        .ok (ROM.words initial (cell.value / 4)) before := by
    obtain ⟨_, _, bits, read, _⟩ := image_cell_source image _ present
    have inROM : cell.toBitVec.toNat < ROM.limit := by
      rw [Word.toBitVec_toNat bounded]
      have loBound := bounded.1
      dsimp [ROM.limit, Word.value, limbBase] at *
      omega
    have preserved := sail_history_code_frame past
      (fun event present => readonly event present)
      cell.toBitVec inROM (aligned _ present) read
    have value := ROM.Proofs.words_at_address (aligned _ present) read
    rw [Word.toBitVec_toNat bounded] at value
    rw [value]
    exact preserved
  have operation (store byte signed : Bool) (imm : BitVec 12) (rs1 rs2 rd : BitVec 5)
      (encoding : original.instruction = SubwordMemory.Proofs.rowInstruction store byte signed imm rs1 rs2 rd) :
      ∃ clause, instructionClause original.instruction = some clause ∧
        run (normalStep clause) (retiredState before row.start.word.toBitVec) =
          .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after row.finish.word.toBitVec) := by
    have shape := SubwordMemory.Proofs.row_decoder_shape store byte signed imm rs1 rs2 rd encoding originalSource.fields
    have flags := SubwordMemory.Proofs.decoder_selectors (by decide) core
      (SubwordMemory.Proofs.decoder_field_bounds originalSource.fields).2.1 originalQuery
    have selected : w 10 = if store then 1 else 0 := by
      have flag := flags 0
      cases store <;> cases byte <;> cases signed <;>
        simpa [shape, SubwordMemory.Proofs.rowData, SubwordMemory.importedConstraintsDecoderColumns, Nat.testBit] using flag
    let port := if store then SubwordMemory.importedConstraintsMemoryPorts[2]
      else SubwordMemory.importedConstraintsMemoryPorts[1]
    have portMember : port ∈ SubwordMemory.importedConstraintsMemoryPorts := by
      cases store <;> simp [port, SubwordMemory.importedConstraintsMemoryPorts]
    have ram : ∃ code, port.address.code w = Nat.pair 1 code := by
      cases store with
      | false =>
        refine ⟨Nat.pair (w 21).val (w 22).val, ?_⟩
        simp [port, SubwordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode, selected, ZMod.val_one]
      | true =>
        refine ⟨Nat.pair (w 27).val (w 28).val, ?_⟩
        simp [port, SubwordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode, selected, ZMod.val_one]
    have cell := subword_ram_cell (addresses port portMember) ram
    have immediate := native_query_immediate_word (by decide)
      (SubwordMemory.Proofs.decoder_field_bounds originalSource.fields).1 originalQuery
    change Word.mk (w 8).val (w 9).val = original.data.immediate at immediate
    have sourceBound := ranges SubwordMemory.importedConstraintsMemoryPorts[0]
      (Array.getElem_mem (by change 0 < 3; decide))
    have address := SubwordMemory.Proofs.local_address (by decide)
      (by decide +kernel : SerializedInverse.Clock babyBearModulus) core store selected
      (by simpa [read_word, SubwordMemory.importedConstraintsMemoryPorts] using sourceBound)
      (immediate.symm ▸ (SubwordMemory.Proofs.decoder_field_bounds originalSource.fields).1)
      (by cases store <;> simpa [port, SubwordMemory.importedConstraintsMemoryPorts, MemoryAddress.word] using cell.1)
      (by cases store <;> simpa [port, SubwordMemory.importedConstraintsMemoryPorts, MemoryAddress.word] using cell.2.1)
    apply SubwordMemory.Proofs.local_execution (by decide)
      (by decide +kernel : SerializedInverse.Clock babyBearModulus) core enabled
      1 ordinaryCells originalSource.fields originalQuery store byte signed imm rs1 rs2 rd encoding selected
      ranges address cell.2.2 (history_configuration past configuration) ?_ native
    intro cell bounded low present
    exact cell_read_PC (.ram cell.toBitVec)
      (cell_read_nextPC (.ram cell.toBitVec) (romReads cell bounded low present) row.start.word.toBitVec)
      row.start.word.toBitVec
  obtain ⟨clause, selected, executed⟩ : ∃ clause, instructionClause original.instruction = some clause ∧
      run (normalStep clause) (retiredState before row.start.word.toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after row.finish.word.toBitVec) := by
    have fields := originalSource.fields
    unfold SubwordMemory.decoderFields at fields
    split at fields
    case h_1 => rename_i _ imm rs1 rd encoding; exact operation false true true imm rs1 0 rd encoding
    case h_2 => rename_i _ imm rs1 rd encoding; exact operation false true false imm rs1 0 rd encoding
    case h_3 => rename_i _ imm rs1 rd encoding; exact operation false false true imm rs1 0 rd encoding
    case h_4 => rename_i _ imm rs1 rd encoding; exact operation false false false imm rs1 0 rd encoding
    case h_5 => rename_i _ imm rs2 rs1 encoding; exact operation true true false imm rs1 rs2 0 encoding
    case h_6 => rename_i _ imm rs2 rs1 encoding; exact operation true false false imm rs1 rs2 0 encoding
    case h_7 => cases fields
  refine ⟨clause, ?_, executed⟩
  simpa only [equal, ProgramEntry.mapFamily] using selected


/-- All six subword instructions execute at their exact full-pool boundaries.
The shared history supplies each native address and operand. Public bytes
supply ROM reads after the same readonly history. -/
theorem unrolled_full_subword_execution
    {initial finalState : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial))
    {cells : List Cell} {physicalImage : List (MemoryToken babyBearModulus)}
    (image : initialImage initial cells = some physicalImage)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinaryCells : ∀ address, Cell.ram address ∈ cells → PlatformWordAddress address)
    (configuration : FlatMemoryConfiguration initial)
    (w : Nat → ZMod babyBearModulus)
    (member : (⟨.subwordMemory, w⟩ : Trace.Row babyBearModulus PooledFamily) ∈ trace.rows)
    {events : List MemoryAccess}
    (permutation : events.Perm ((unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (readonly : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    (reads : ∀ edge ∈ (unrolledFullMemoryData trace workers splitWorkers).steps, edge.1.word.Bounded) :
    let row : Trace.Row babyBearModulus PooledFamily := ⟨.subwordMemory, w⟩
    let low := (decodeTimestamp row.assignment row.columns.initialTime).value
    ∃ entry ∈ NativeDecoder.ProgramRows.programOf .fullUnsigned initial text,
      entry.SourceWith initial AddSub.Modular.External.decoderFields ∧
      entry.data.family = .subwordMemory ∧ row.decoderQuery = entry.query ∧
      ∃ clause before after, instructionClause entry.instruction = some clause ∧
        SailHistory cells (events.filter fun event => decide (event.1 ≤ low)) initial before ∧
        run (normalStep clause) (retiredState before row.start.word.toBitVec) =
          .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after row.finish.word.toBitVec) ∧
        SailHistory cells (events.filter fun event => decide (low + 4 < event.1)) after finalState := by
  let row : Trace.Row babyBearModulus PooledFamily := ⟨.subwordMemory, w⟩
  have ordinary : ¬ (row.family = .addSub ∧ Delegation.Requests.Selected row.assignment) := by simp [row]
  obtain ⟨entry, included, source, family, query⟩ :=
    unrolled_full_ordinary_source setup lookup accepted excluded initialPC row member ordinary
  obtain ⟨before, after, past, native, ranges, future⟩ :=
    unrolled_full_ordinary_history accepted equations active initialClock initialAligned row member ordinary
      permutation ordered history reads
  obtain ⟨clause, selected, executed⟩ := unrolled_subword_execution_from_shared_history image subwordSetup
    aligned ordinaryCells configuration (accepted.cpuEquations row member) (accepted.cpuActive row member)
    ranges source family query past
    (fun event present => readonly event (List.mem_filter.mp present).1) native
  exact ⟨entry, included, source, family, query, clause, before, after, selected, past, executed, future⟩

end Airbender.Compiler.MachineTargets.Proofs
