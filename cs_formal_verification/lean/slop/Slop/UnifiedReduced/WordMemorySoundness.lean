import Slop.Trace.NativeCell
import Human.Circuits.UnifiedReduced.WordMemory
import Slop.UnifiedReduced.WordMemory
import Slop.UnifiedReduced.History
import Slop.WordMemory.MemoryAccess
import Slop.Sail.Memory
import Slop.UnifiedReduced.WordROM

namespace Airbender.UnifiedReduced.WordMemory.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
open _root_.Sail.ArchSem
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def metadata (input : Airbender.WordMemory.Input) : DecoderData UnifiedFamily :=
  ⟨.machine,
    match input.rs1 with | .Regidx index => index,
    if input.store then (match input.rs2 with | .Regidx index => index) else 0,
    if input.store then 0 else (match input.rd with | .Regidx index => index),
    Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate),
    if input.store then 262144 else 131072, 0⟩

theorem decoded_metadata {input : Airbender.WordMemory.Input} {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data)
    (encoding : entry.instruction = if input.store then
      .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
      else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4))
    (destination : input.store = false → input.rd ≠ zeroRegister) : entry.data = metadata input := by
  rw [encoding] at fields
  rcases input with ⟨store, source, immediate, readData, pc, ⟨rs1⟩, ⟨rs2⟩, ⟨rd⟩, encoded, before⟩
  change BitVec 5 at rs1 rs2 rd
  cases store
  · have nonzero : rd ≠ 0 := by simpa [zeroRegister] using destination rfl
    change rd ≠ (0#5) at nonzero
    simpa [decoderFields, Trace.decoderFields, arithmeticFields, DecoderData.mapFamily,
      metadata, nonzero] using fields.symm
  · simpa [decoderFields, Trace.decoderFields, arithmeticFields, DecoderData.mapFamily,
      metadata] using fields.symm

private theorem retire_ram
    (input : Airbender.WordMemory.Input) (output : Airbender.WordMemory.Output)
    (address : output.address.toBitVec = input.source.toBitVec + input.immediate.toBitVec)
    (successor : output.pc.toBitVec = input.pc.toBitVec + 4)
    (copied : output.data.toBitVec = input.readData.toBitVec)
    (sourceRead : run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok input.source.toBitVec input.before)
    (storeRead : input.store = true → run (SailRV32.Functions.rX_bits input.rs2) input.before =
      .ok input.readData.toBitVec input.before)
    (loadRead : input.store = false → readBytes (ue := SailRV32.exception) 4 output.address.toBitVec.toNat
      input.before = .ok input.readData.toBitVec input.before)
    (extension : input.immediate.toBitVec = SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate)
    (pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before)
    (access : Airbender.WordMemory.MemoryAccess input) : Airbender.WordMemory.spec input output := by
  refine ⟨address, ?_⟩
  let prepared : State := { input.before with regs := input.before.regs.insert .nextPC output.pc.toBitVec }
  have register := rX_nextPC (pc := output.pc.toBitVec) input.rs1 sourceRead
  cases mode : input.store
  · simp only [Bool.false_eq_true, ite_false]
    apply retire_of_destination pcRead successor
    have bytes := loadRead mode
    rw [address, ← copied] at bytes
    have virtual := access.load mode output.pc.toBitVec output.data.toBitVec register bytes
    rw [extension] at virtual
    have executed := load_word (rd := input.rd) virtual
    obtain ⟨written, writeRun, _⟩ := gpr_write_nextPC input.rd output.data.toBitVec prepared
    have projected : run (writeResult input.rd output.data) prepared =
        .ok SailRV32.Functions.RETIRE_SUCCESS written := by
      simp only [writeResult]
      rw [run_bind_of_ok _ _ _ _ _ writeRun]
      rfl
    exact ⟨written, by simpa [Airbender.WordMemory.execution, Airbender.WordMemory.instruction, Trace.instructionClause, mode]
      using executed.trans (by simpa only [writeResult] using projected), projected⟩
  · simp only [ite_true]
    apply retire_with_memory pcRead
    obtain ⟨written, memoryRun, registers⟩ := write_word_frame output.address.toBitVec input.readData.toBitVec prepared
    have virtual := access.store mode output.pc.toBitVec input.readData.toBitVec register
    rw [← address, run_bind_of_ok _ _ _ _ _ memoryRun] at virtual
    rw [extension] at virtual
    have executed := store_word (rX_nextPC (pc := output.pc.toBitVec) input.rs2 (storeRead mode)) virtual
    refine ⟨written, ?_, ?_, ?_⟩
    · simpa [Airbender.WordMemory.execution, Airbender.WordMemory.instruction, Trace.instructionClause, mode, successor] using executed
    · simp only [writeResult, write_zero, freeM_pure_bind, copied]
      rw [run_bind_of_ok _ _ _ _ _ memoryRun]
      rfl
    · rw [registers]
      simp [prepared]


theorem row_soundness_from_history [Fact p.Prime]
    (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {initial : State} {cells : List Cell} {events : List MemoryAccess}
    {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output} {w : Nat → ZMod p}
    {after : State} {epoch : Nat}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w importedConstraintsTraceColumns.execute = 1)
    (past : SailHistory cells events (retiredState initial input.pc.toBitVec) input.before)
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse input.before after)
    (sourceRange : (readToken w importedConstraintsMemoryPorts[0]).word.Bounded)
    (words : UnifiedReduced.WordMemory.WordMapping input output w)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = if input.store then .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
      else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4))
    (configuration : Configured initial)
    (aligned : ∀ address, Cell.ram address ∈ cells → address.toNat % 4 = 0)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (destination : input.store = false → input.rd ≠ zeroRegister)
    (copiedWord : output.data.toBitVec = input.readData.toBitVec)
    (pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before) :
    Airbender.WordMemory.spec input output := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have decoderSize : 524288 < p := by omega
  have size : 196608 < p := by omega
  have dataFields := decoded_metadata fields encoding destination
  have flags := UnifiedReduced.Proofs.decoder_selectors decoderSize core
    (UnifiedReduced.Proofs.decoder_field_bounds fields).2.1 query
  have selected : w 28 = if input.store then 0 else 1 := by
    have bit := flags 17
    rw [dataFields] at bit
    cases mode : input.store <;> simpa [metadata, mode, importedConstraintsDecoderColumns, Nat.testBit,
      Nat.shiftRight_eq_div_pow] using bit
  have other : w 29 = if input.store then 1 else 0 := by
    have bit := flags 18
    rw [dataFields] at bit
    cases mode : input.store <;> simpa [metadata, mode, importedConstraintsDecoderColumns, Nat.testBit,
      Nat.shiftRight_eq_div_pow] using bit
  have ignored (i : Fin 4) : w (21 + i.val) = 0 := by
    have bit := flags ⟨10 + i.val, by have := i.isLt; omega⟩
    rw [dataFields] at bit
    cases mode : input.store <;> fin_cases i
    all_goals simpa [metadata, mode, importedConstraintsDecoderColumns, Nat.testBit,
      Nat.shiftRight_eq_div_pow] using bit
  have sourceWord : input.source = Word.mk (w 36).val (w 37).val :=
    congrArg₂ Word.mk words.sourceLo words.sourceHi
  have immediateWord : input.immediate = Word.mk (w 8).val (w 9).val :=
    congrArg₂ Word.mk words.immediateLo words.immediateHi
  have readWord : input.readData = Word.mk (w 42).val (w 43).val :=
    congrArg₂ Word.mk words.readLo words.readHi
  have addressWord : output.address = Word.mk (w (if input.store then 44 else 38)).val
      (w (if input.store then 45 else 39)).val :=
    congrArg₂ Word.mk words.addressLo words.addressHi
  have inputPC : input.pc = Word.mk (w 0).val (w 1).val :=
    congrArg₂ Word.mk words.pcLo words.pcHi
  have immediate : input.immediate = (metadata input).immediate := by
    rw [immediateWord]
    exact (native_query_immediate_word limbSize (UnifiedReduced.Proofs.decoder_field_bounds fields).1 query).trans
      (congrArg DecoderData.immediate dataFields)
  have extension : input.immediate.toBitVec = SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate := by
    rw [immediate]
    exact Word.ofBitVec_roundtrip _
  have pcBound : input.pc.Bounded := by
    have canonical := native_query_pc_word limbSize query
    change Word.mk (w 0).val (w 1).val = Word.ofBitVec entry.pc at canonical
    rw [inputPC, canonical]
    exact Word.ofBitVec_bound _
  have sourceBound : input.source.Bounded := by
    simpa [sourceWord, readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code,
      pairCode, importedConstraintsMemoryPorts] using sourceRange
  let port := importedConstraintsMemoryPorts[if input.store then 2 else 1]'
    (by change (if input.store then 2 else 1) < 3; split <;> decide)
  have portMember : port ∈ (⟨.machine, w⟩ : Row p UnifiedFamily).ports := by
    cases input.store <;> simp [port, Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]
  obtain ⟨cell, cellMember, cellAddress⟩ := native_history_cell epoch (columns := importedConstraintsTraceColumns)
    (ports := importedConstraintsMemoryPorts) (port := port) rfl rfl rfl history
    (by simpa only [Row.ports, CircuitLayout.ports] using portMember)
  have addressBound : output.address.Bounded := by
    have bound : (port.address.word w).Bounded := by
      rw [address_word cellAddress]
      exact cell_address_bound cell
    cases mode : input.store
    all_goals simpa [port, MemoryAddress.word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      addressWord, mode] using bound
  have ramSpace : ∃ code, port.address.code w = Nat.pair 1 code := by
    cases mode : input.store
    all_goals simp [mode] at selected other
    all_goals refine ⟨Nat.pair (w (if input.store then 44 else 38)).val
      (w (if input.store then 45 else 39)).val, ?_⟩
    all_goals simp [port, mode, importedConstraintsMemoryPorts, MemoryAddress.code, selected, other,
      pairCode, ZMod.val_one'' (by omega : p ≠ 1)]
  have ramCell : Cell.ram (port.address.word w).toBitVec ∈ cells ∧
      port.address.code w = (Cell.ram (port.address.word w).toBitVec).addressCode := by
    cases cell with
    | register index =>
      obtain ⟨code, actual⟩ := ramSpace
      have impossible := actual.symm.trans cellAddress
      simp [Cell.addressCode, Nat.pair_eq_pair] at impossible
    | ram address =>
      have canonical := address_word cellAddress
      have same : (port.address.word w).toBitVec = address :=
        (congrArg Word.toBitVec canonical).trans (Word.ofBitVec_roundtrip address)
      rw [same]
      exact ⟨cellMember, cellAddress⟩
  have physical : Cell.ram output.address.toBitVec ∈ cells ∧
      port.address.code w = (Cell.ram output.address.toBitVec).addressCode := by
    cases mode : input.store
    all_goals simpa [port, mode, addressWord, importedConstraintsMemoryPorts, MemoryAddress.word,
      WordColumns.evaluate] using ramCell
  have effective : output.address.toBitVec = input.source.toBitVec + input.immediate.toBitVec := by
    rw [addressWord, sourceWord, immediateWord]
    exact UnifiedReduced.Proofs.word_memory_address size input.store core selected other
      (sourceWord ▸ sourceBound) (immediateWord ▸ (immediate.symm ▸ Word.ofBitVec_bound _))
      (addressWord ▸ addressBound)
  have successor := UnifiedReduced.Proofs.pc_successor (by omega) core active
    ⟨ignored 0, ignored 1, ignored 2, ignored 3⟩
    (initial := input.pc) (final := output.pc)
    ⟨words.pcLo ▸ (ZMod.natCast_zmod_val _).symm,
      words.pcHi ▸ (ZMod.natCast_zmod_val _).symm,
      words.finalPCLo, words.finalPCHi⟩ pcBound
  have indices := native_query_indices limbSize query
  have read (i : Fin 3) (cell : Cell)
      (address : importedConstraintsMemoryPorts[i].address.code w = cell.addressCode) :=
    native_history_read epoch (columns := importedConstraintsTraceColumns)
      (ports := importedConstraintsMemoryPorts) rfl rfl rfl history
      (Array.getElem_mem i.isLt) address
  have sourceRead : run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok input.source.toBitVec input.before := by
    have actual := read 0 (.register entry.data.rs1) (by
      simpa [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode,
        importedConstraintsDecoderColumns] using congrArg (Nat.pair 0) indices.1)
    rw [dataFields] at actual
    cases index : input.rs1
    simpa [metadata, index, importedConstraintsMemoryPorts, MemoryPort.readCode, WordColumns.code,
      pairCode, memoryWord, Cell.read, ← sourceWord] using actual
  have storeRead (mode : input.store = true) :
      run (SailRV32.Functions.rX_bits input.rs2) input.before = .ok input.readData.toBitVec input.before := by
    have low := Verification.assertion_of_holds core ⟨29, by rw [constraint_count]; decide⟩
    have high := Verification.assertion_of_holds core ⟨30, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
      selected, mode] at low high
    have location : w 38 = w 6 := by linear_combination low
    have upper : w 39 = 0 := high
    have actual := read 1 (.register entry.data.rs2) (by
      simpa [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, selected, mode,
        location, upper, importedConstraintsDecoderColumns, pairCode] using congrArg (Nat.pair 0) indices.2.1)
    rw [dataFields] at actual
    cases index : input.rs2
    simpa [metadata, mode, index, importedConstraintsMemoryPorts, MemoryPort.readCode, WordColumns.code,
      pairCode, memoryWord, Cell.read, ← readWord] using actual
  have loadRead (mode : input.store = false) :
      readBytes (ue := SailRV32.exception) 4 output.address.toBitVec.toNat input.before =
        .ok input.readData.toBitVec input.before := by
    have actual := read ⟨1, by decide⟩ (.ram output.address.toBitVec) (by simpa [port, mode] using physical.2)
    simpa [EStateM.run, Cell.read, importedConstraintsMemoryPorts, MemoryPort.readCode, WordColumns.code,
      pairCode, memoryWord, ← readWord] using actual
  have configuration := history_configuration past (retired_state_configuration configuration _)
  -- The circuit rejects stores into ROM (`word_rom_selection`): a store address is in RAM.
  have ramStore (mode : input.store = true) :
      Configuration.ROM_END ≤ (input.source.toBitVec + input.immediate.toBitVec).toNat := by
    have high := (Airbender.UnifiedReduced.Proofs.word_rom_selection (by omega) input.store core selected other).2 mode
    rw [← effective, Word.toBitVec_toNat addressBound, addressWord]
    simp only [mode, ite_true] at high ⊢
    simp only [Word.value, limbBase, Configuration.ROM_END]
    omega
  have access := Airbender.WordMemory.Proofs.memory_access configuration
    (by rw [← effective]; exact aligned _ physical.1)
    (by rw [← effective]; exact ordinary _ physical.1) ramStore
  exact retire_ram input output effective successor.2.2 copiedWord
    sourceRead storeRead loadRead extension pcRead access

theorem ram_copy_from_history [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {cells : List Cell} {w : Nat → ZMod p} {epoch : Nat}
    {before after : State} {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after)
    (words : UnifiedReduced.WordMemory.WordMapping input output w)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = if input.store then .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
      else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4))
    (destination : input.store = false → input.rd ≠ zeroRegister)
    (ram : ∀ address, Cell.ram address ∈ cells → 4194304 ≤ address.toNat) :
    output.data.toBitVec = input.readData.toBitVec := by
  have dataFields := decoded_metadata fields encoding destination
  have flags := UnifiedReduced.Proofs.decoder_selectors hp core
    (UnifiedReduced.Proofs.decoder_field_bounds fields).2.1 query
  have selected : w 28 = if input.store then 0 else 1 := by
    have bit := flags 17
    rw [dataFields] at bit
    cases mode : input.store <;> simpa [metadata, mode, importedConstraintsDecoderColumns, Nat.testBit,
      Nat.shiftRight_eq_div_pow] using bit
  have other : w 29 = if input.store then 1 else 0 := by
    have bit := flags 18
    rw [dataFields] at bit
    cases mode : input.store <;> simpa [metadata, mode, importedConstraintsDecoderColumns, Nat.testBit,
      Nat.shiftRight_eq_div_pow] using bit
  let port := importedConstraintsMemoryPorts[if input.store then 2 else 1]'
    (by change (if input.store then 2 else 1) < 3; split <;> decide)
  have present : port ∈ importedConstraintsMemoryPorts := by
    cases input.store <;> simp [port, importedConstraintsMemoryPorts]
  obtain ⟨cell, member, address⟩ := native_history_cell epoch (columns := importedConstraintsTraceColumns)
    (ports := importedConstraintsMemoryPorts) (port := port) rfl rfl rfl history present
  have ramSpace : ∃ code, port.address.code w = Nat.pair 1 code := by
    cases mode : input.store
    all_goals simp [mode] at selected other
    all_goals refine ⟨Nat.pair (w (if input.store then 44 else 38)).val
      (w (if input.store then 45 else 39)).val, ?_⟩
    all_goals simp [port, mode, importedConstraintsMemoryPorts, MemoryAddress.code, selected, other,
      pairCode, ZMod.val_one'' (by omega : p ≠ 1)]
  have addressHi : 64 ≤ output.address.hi := by
    cases cell with
    | register index =>
      obtain ⟨code, actual⟩ := ramSpace
      have impossible := actual.symm.trans address
      simp [Cell.addressCode, Nat.pair_eq_pair] at impossible
    | ram actual =>
      have lower := ram actual member
      have canonical := address_word address
      have outputAddress : output.address = Word.ofBitVec actual := by
        have word : output.address = port.address.word w := by
          cases mode : input.store
          all_goals apply congrArg₂ Word.mk
          all_goals first
            | simpa [port, mode, importedConstraintsMemoryPorts, MemoryAddress.word, WordColumns.evaluate] using words.addressLo
            | simpa [port, mode, importedConstraintsMemoryPorts, MemoryAddress.word, WordColumns.evaluate] using words.addressHi
        exact word.trans canonical
      rw [outputAddress]
      dsimp [Word.ofBitVec, limbBase]
      omega
  have nativeRam := UnifiedReduced.Proofs.word_memory_ram (by omega) input.store core selected other
    (by simpa [words.addressHi] using addressHi)
  have copied := UnifiedReduced.Proofs.word_memory_copy input.store core selected other nativeRam
  change w 50 = w 42 ∧ w 51 = w 43 at copied
  have outputWord : output.data = Word.mk (w 50).val (w 51).val := congrArg₂ Word.mk words.dataLo words.dataHi
  have inputWord : input.readData = Word.mk (w 42).val (w 43).val := congrArg₂ Word.mk words.readLo words.readHi
  rw [outputWord, inputWord, copied.1, copied.2]

theorem row_soundness_from_memory [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output} {w : Nat → ZMod p}
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    (accepted : Accepted trace)
    (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    (words : UnifiedReduced.WordMemory.WordMapping input output w)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    {entry : ProgramEntry} (source : entry.SourceWith initial decoderFields)
    (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = if input.store then .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
      else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4))
    (memory : MemoryExecution trace initial cells)
    (initialization : NativeInputs projection trace initial cells program)
    (configuration : Configured initial)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (destination : input.store = false → input.rd ≠ zeroRegister)
    (copiedWord : output.data.toBitVec = input.readData.toBitVec) :
    Airbender.WordMemory.spec input output := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  obtain ⟨events, after, past, history⟩ := UnifiedReduced.Proofs.row_position_from_memory hp inverse accepted
    initialization.clocks memory position
  have sourceRange := (UnifiedReduced.Proofs.value_bounds hp inverse accepted
    initialization.clocks initialization.image).1 _ member importedConstraintsMemoryPorts[0]
    (by simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  have pcWord : input.pc = Word.mk (w 0).val (w 1).val := congrArg₂ Word.mk words.pcLo words.pcHi
  have pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before := by
    obtain ⟨newer, older, middle, permutation, ordered, writes, state⟩ := position
    rw [state, pcWord]
    exact retired_state_pc middle _
  exact row_soundness_from_history (by dsimp [timestampBase] at hp; omega) core (accepted.active _ member)
    (by simpa [pcWord, Row.start, Row.columns, CircuitLayout.columns, PCState.State.word,
      rawPair, importedConstraintsTraceColumns] using past)
    history sourceRange words source.fields query encoding configuration (fun address present => initialization.aligned (.ram address) present)
    ordinary destination copiedWord pcRead

theorem row_soundness [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output} {w : Nat → ZMod p}
    (accepted : Accepted trace) (decoded : Decoded trace program)
    (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    (mapping : TraceMapping trace initial cells program input output w)
    (initialization : NativeInputs decoderFields trace initial cells program)
    (configuration : Configured initial)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (destination : input.store = false → input.rd ≠ zeroRegister)
    (copiedWord : output.data.toBitVec = input.readData.toBitVec) :
    Airbender.WordMemory.spec input output := by
  obtain ⟨addresses, image⟩ := initialization.programImage
  obtain ⟨entry, present, query, encoding⟩ := mapping.instruction
  exact row_soundness_from_memory hp inverse accepted member mapping.words mapping.state
    (run_program_sources image entry present) query encoding
    (UnifiedReduced.Proofs.memory_execution hp inverse accepted initialization decoded)
    initialization configuration ordinary destination copiedWord

theorem soundness [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : UnifiedTrace p) (initial : State) (cells : List Cell) (program : List ProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) Airbender.WordMemory.spec := by
  rintro input output w ⟨assumptions, ⟨accepted, decoded, member⟩, mapping⟩
  have limbSize : limbBase < p := by dsimp [limbBase, timestampBase] at *; omega
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  obtain ⟨addresses, image⟩ := assumptions.initialization.programImage
  obtain ⟨entry, present, query, encoding⟩ := mapping.instruction
  have source := run_program_sources image entry present
  have dataFields := decoded_metadata source.fields encoding assumptions.destination
  have flags := UnifiedReduced.Proofs.decoder_selectors (by dsimp [timestampBase] at hp; omega) core
    (UnifiedReduced.Proofs.decoder_field_bounds source.fields).2.1 query
  have selected : w 28 = if input.store then 0 else 1 := by
    have bit := flags 17
    rw [dataFields] at bit
    cases mode : input.store <;> simpa [metadata, mode, importedConstraintsDecoderColumns, Nat.testBit,
      Nat.shiftRight_eq_div_pow] using bit
  have other : w 29 = if input.store then 1 else 0 := by
    have bit := flags 18
    rw [dataFields] at bit
    cases mode : input.store <;> simpa [metadata, mode, importedConstraintsDecoderColumns, Nat.testBit,
      Nat.shiftRight_eq_div_pow] using bit
  have addressWord : output.address = Word.mk (w (if input.store then 44 else 38)).val
      (w (if input.store then 45 else 39)).val :=
    congrArg₂ Word.mk mapping.words.addressLo mapping.words.addressHi
  have readWord : input.readData = Word.mk (w 42).val (w 43).val :=
    congrArg₂ Word.mk mapping.words.readLo mapping.words.readHi
  let port := importedConstraintsMemoryPorts[if input.store then 2 else 1]'
    (by change (if input.store then 2 else 1) < 3; split <;> decide)
  have portMember : port ∈ (⟨.machine, w⟩ : Row p UnifiedFamily).ports := by
    cases input.store <;> simp [port, Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]
  have addressBound : output.address.Bounded := by
    have bound := address_bounds hp inverse accepted assumptions.initialization.clocks
      assumptions.initialization.image _ member port portMember
    cases mode : input.store
    all_goals simpa [port, MemoryAddress.word, importedConstraintsMemoryPorts, WordColumns.evaluate,
      addressWord, mode] using bound
  have ramSpace : ∃ code, port.address.code w = Nat.pair 1 code := by
    cases mode : input.store
    all_goals simp [mode] at selected other
    all_goals refine ⟨Nat.pair (w (if input.store then 44 else 38)).val
      (w (if input.store then 45 else 39)).val, ?_⟩
    all_goals simp [port, mode, importedConstraintsMemoryPorts, MemoryAddress.code, selected, other,
      pairCode, ZMod.val_one'' (by omega : p ≠ 1)]
  have ramCell := row_ram_cell hp inverse accepted assumptions.initialization.clocks
    assumptions.initialization.image member portMember ramSpace
  have physical : Cell.ram output.address.toBitVec ∈ cells ∧
      port.address.code w = (Cell.ram output.address.toBitVec).addressCode := by
    cases mode : input.store
    all_goals simpa [port, mode, addressWord, importedConstraintsMemoryPorts, MemoryAddress.word,
      WordColumns.evaluate] using ramCell
  have addressHi : 64 ≤ output.address.hi := by
    have lower := assumptions.ram output.address.toBitVec physical.1
    rw [Word.toBitVec_toNat addressBound] at lower
    have low := addressBound.1
    dsimp [Word.value, limbBase] at *
    omega
  have ram := UnifiedReduced.Proofs.word_memory_ram (by dsimp [timestampBase] at hp; omega) input.store core selected other
    (by simpa [mapping.words.addressHi] using addressHi)
  have copied := UnifiedReduced.Proofs.word_memory_copy input.store core selected other ram
  change w 50 = w 42 ∧ w 51 = w 43 at copied
  have copiedWord : output.data = input.readData := by
    have dataWord : output.data = Word.mk (w 50).val (w 51).val :=
      congrArg₂ Word.mk mapping.words.dataLo mapping.words.dataHi
    rw [dataWord, readWord, copied.1, copied.2]
  exact row_soundness hp inverse accepted decoded member mapping assumptions.initialization
    assumptions.configuration assumptions.ordinary assumptions.destination (congrArg Word.toBitVec copiedWord)

end Airbender.UnifiedReduced.WordMemory.Proofs
