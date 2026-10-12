import Tests.SubwordMemoryTimestamp
import Airbender.Proofs.SubwordMemory.PortReads
import Airbender.Proofs.SubwordMemory.Address
import Airbender.Proofs.Sail.WordMemoryState
import Airbender.Proofs.Sail.PhysicalMemory
import Airbender.Proofs.SubwordMemory.Claims

namespace Tests.SubwordMemoryHistory
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

private def entry : Airbender.SubwordMemory.ProgramEntry :=
  ⟨0, 0x0000c103, .LOAD (0, .Regidx 1, .Regidx 2, true, 1),
    ⟨(), 1, 0, 2, ⟨0, 0⟩, 2, 0⟩⟩
private def attributes : SailRV32.PMA :=
  { (default : SailRV32.PMA) with readable := true, writable := true, executable := true }
private def initial : State :=
  { (default : State) with
    regs := ((default : State).regs).insert .mstatus 0
    |>.insert .cur_privilege .Machine |>.insert .misa 0x40000100
    |>.insert .senvcfg 0 |>.insert .menvcfg 0x10
    |>.insert .pmpcfg_n (Vector.replicate 64 0)
    |>.insert .pmpaddr_n (Vector.replicate 64 0)
    |>.insert .pma_regions [rv32Region attributes]
    |>.insert .mhartid 7 |>.insert .htif_tohost_base none
    |>.insert .x1 0x00400001 |>.insert .x2 0 |>.insert .PC 0 }
private def dataState := wordWriteState initial 4194304 0x56781234
private def before := wordWriteState dataState 0 entry.bits
private def cells : List Cell := [.register 1, .ram 4194304, .register 2]
private def seed : List (MemoryToken babyBearModulus) :=
  [Cell.initialToken (.register 1) 0x00400001,
    Cell.initialToken (.ram 4194304) 0x56781234, Cell.initialToken (.register 2) 0]
private def row : Row babyBearModulus Airbender.SubwordMemory.TraceKind :=
  ⟨.subwordMemory, Tests.SubwordMemoryTimestamp.assignment false⟩
private def trace : Airbender.SubwordMemory.NativeTrace babyBearModulus where
  rows := [row]
  rom := Verification.subwordTable (fun _ => 0)
  initial := row.start
  terminal := row.finish
  initialMemory := seed
  terminalMemory := [⟨(Cell.register 1).addressCode, (4, 0), Nat.pair 1 64⟩,
    ⟨(Cell.ram 4194304).addressCode, (5, 0), Nat.pair 4660 22136⟩,
    ⟨(Cell.register 2).addressCode, (6, 0), Nat.pair 18 0⟩]

private theorem accepted : Accepted trace := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact Tests.SubwordMemoryTimestamp.constraints false
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · dsimp [trace, Row.reads, Row.writes, Row.ports, Row.columns, row,
      Airbender.SubwordMemory.importedConstraintsMemoryPorts,
      Airbender.SubwordMemory.importedConstraintsTraceColumns]
    decide

private theorem boundary : ClockBoundary trace := by
  constructor
  · change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro actual member
    simp only [trace, seed, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide

private theorem image : initialImage before cells = some seed := by
  have one : (Cell.register 1).read before = .ok 0x00400001 before := by
    apply read_register
    simp [before, dataState, initial, wordWriteState, Std.ExtDHashMap.get?_insert]
  have two : (Cell.register 2).read before = .ok 0 before := by
    apply read_register
    simp [before, dataState, initial, wordWriteState, Std.ExtDHashMap.get?_insert]
  have memory : (Cell.ram 4194304).read before = .ok 0x56781234 before :=
    written_word_disjoint 0 entry.bits (Or.inr (by decide)) (written_word_read initial 4194304 0x56781234)
  simp only [initialImage, cells, seed, List.mapM_cons, List.mapM_nil, one, two, memory]
  rfl

private theorem program_image : Airbender.SubwordMemory.programImage before [0] = some [entry] := by
  have bytes : (Cell.ram 0).read before = .ok entry.bits before := written_word_read _ 0 _
  have decoded : run (SailRV32.Functions.encdec_backwards entry.bits) before =
      .ok entry.instruction before := by with_unfolding_all rfl
  simp only [Airbender.SubwordMemory.programImage, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, decoded, bind, Option.bind]
  rfl

private theorem decoded : Airbender.SubwordMemory.Decoded trace [entry] := by
  intro actual member
  simp only [trace, List.mem_singleton] at member
  subst actual
  change ∃ i, _
  exact ⟨⟨0, by decide⟩, by decide⟩

set_option backward.isDefEq.respectTransparency false in
private theorem configuration : FlatMemoryConfiguration before := by
  constructor
  · simp [before, dataState, initial, wordWriteState, Std.ExtDHashMap.get?_insert]
  · simp [before, dataState, initial, wordWriteState, Std.ExtDHashMap.get?_insert]
  · exact ⟨0x40000100, by simp [before, dataState, initial, wordWriteState, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨0, by simp [before, dataState, initial, wordWriteState, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨0x10, by simp [before, dataState, initial, wordWriteState, Std.ExtDHashMap.get?_insert]⟩
  · simp [before, dataState, initial, wordWriteState, Std.ExtDHashMap.get?_insert]
  · exact ⟨Vector.replicate 64 0, by simp [before, dataState, initial, wordWriteState, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨attributes, by simp [before, dataState, initial, wordWriteState, Std.ExtDHashMap.get?_insert], rfl, rfl, rfl⟩
  · exact ⟨7, by simp [before, dataState, initial, wordWriteState, Std.ExtDHashMap.get?_insert]⟩
  · simp [before, dataState, initial, wordWriteState, Std.ExtDHashMap.get?_insert]

private theorem ram_inputs [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] : Airbender.SubwordMemory.RAMInputs trace before cells [entry] := by
  constructor
  · constructor
    · decide
    · intro cell member
      simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> simp [Cell.Aligned]
    · exact image
    · refine ⟨(4, 0), ?_⟩
      have pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok 0 before := by
        apply read_register
        simp [before, dataState, initial, wordWriteState]
      simp only [initialState, pc]
      rfl
    · exact ⟨[0], program_image⟩
    · exact boundary
  · exact configuration
  · intro address member
    simp [cells] at member
    subst address
    decide
  · intro address member
    simp [cells] at member
    subst address
    unfold OrdinaryWordAddress
    decide
  · intro actual member
    simp only [List.mem_singleton] at member
    subst actual
    constructor <;> decide
  · exact ⟨fun _ => 0, rfl⟩

/-- A real accepted LBU row reaches original Sail retirement and native
    terminal cells. Only public initialization and logical matching are supplied. -/
theorem actual_native_execution [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] :
    ∃ after, Airbender.SubwordMemory.SailTrace [entry] before after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok 4 after ∧
      run (SailRV32.Functions.rX_bits (.Regidx 2)) after = .ok 18 after := by
  obtain ⟨after, execution, pc, terminal⟩ :=
    Airbender.SubwordMemory.ram_trace_soundness (by decide) (by decide) ram_inputs accepted decoded
  obtain ⟨cell, _, address, read⟩ := terminal ⟨(Cell.register 2).addressCode, (6, 0), Nat.pair 18 0⟩
    (by simp [trace])
  have same : cell = .register 2 := Proofs.cell_address_injective address
  subst cell
  refine ⟨after, execution, ?_, ?_⟩
  · have value : trace.terminal.word.toBitVec = 4 := by decide
    rwa [value] at pc
  · simpa [Cell.read, MemoryToken.word, Nat.unpair_pair, Word.toBitVec,
      Word.value, limbBase] using read

/-- The effective address is proved from the imported row, public cell image
    and history. No operand or address range is passed to the theorem. -/
theorem actual_native_address :
    let w := row.assignment
    let cell : Word := ⟨(w 21).val, (w 22).val⟩
    let offset := (w 35).val + 2 * (w 36).val
    cell.Bounded ∧ cell.value % 4 = 0 ∧ offset < 4 ∧
      cell.toBitVec + BitVec.ofNat 32 offset =
        (Word.mk (w 19).val (w 20).val).toBitVec + (Word.mk (w 8).val (w 9).val).toBitVec ∧
      ((Word.mk (w 19).val (w 20).val).toBitVec +
        (Word.mk (w 8).val (w 9).val).toBitVec).toNat % 4 = offset ∧
      Cell.ram cell.toBitVec ∈ cells := by
  exact Airbender.SubwordMemory.Proofs.native_address (by decide) (by decide)
    accepted boundary image rfl (by simp [trace])
    (entry := entry) (by rfl) (by decide) false (by decide)

/-- Source/result bounds follow from the extracted public cells and the
    accepted native row, without a desired-read or output-bound premise. -/
theorem actual_native_bounds :
    (∀ actual ∈ trace.rows, ∀ port ∈ actual.ports,
      (readToken actual.assignment port).word.Bounded) ∧
    (∀ actual ∈ trace.rows, ∀ port ∈ actual.ports,
      (writeToken actual.columns actual.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) :=
  Airbender.SubwordMemory.Proofs.native_value_bounds (by decide) (by decide)
    accepted boundary (Proofs.image_bounds image) rfl

/-- A real public RAM/GPR image, actual LBU decoding and native matching
    produce complete grouped Sail cell histories. -/
theorem actual_native_history :
    ∃ (history : TimestampSortedMemoryAccessList)
      (rows : List (Row babyBearModulus Airbender.SubwordMemory.TraceKind)) (after : State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells
        (rows.flatMap fun row => (Trace.rowEvents trace.memoryEpoch row).reverse) before after ∧
      SailStateMatches cells history after := by
  apply Airbender.SubwordMemory.Proofs.decoded_native_history (by decide) (by decide)
    accepted boundary image (by decide) _ program_image decoded
  intro cell member
  simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [Cell.Aligned]

/-- The public image and accepted matching supply the actual source/RAM
    reads and destination write. No desired-read premise is passed. -/
theorem actual_native_transport :
    ∃ after,
      run (SailRV32.Functions.rX_bits (.Regidx 1)) before = .ok 0x00400001 before ∧
      (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 4194304).run before =
        .ok 0x56781234 before ∧
      run (SailRV32.Functions.wX_bits (.Regidx 2) 18) before = .ok () after := by
  obtain ⟨_, rows, after, _, permutation, _, native, _⟩ := actual_native_history
  have single : rows = [row] := List.perm_singleton.mp permutation
  rw [single] at native
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at native
  have query : Airbender.SubwordMemory.decoderQuery row.assignment = entry.query := by decide
  have core := Verification.holds_of_sublist (Tests.SubwordMemoryTimestamp.constraints false)
    (List.sublist_append_left (Airbender.SubwordMemory.importedConstraints trace.rom)
      Airbender.SubwordMemory.importedConstraintsTimestampLookups)
  have read := Airbender.SubwordMemory.Proofs.source_read (by decide) trace.memoryEpoch query native
  have ram := Airbender.SubwordMemory.Proofs.ram_read (by decide) (by decide)
    accepted boundary image (by simp [trace]) false (by decide) native
  have write := Airbender.SubwordMemory.Proofs.destination_write (by decide) trace.memoryEpoch
    core (by decide) query native
  simp [entry, row, Tests.SubwordMemoryTimestamp.assignment, Tests.SubwordMemory.row,
    Airbender.SubwordMemory.importedConstraintsMemoryPorts, MemoryAddress.word,
    MemoryPort.readCode, MemoryPort.writeCode, WordColumns.code, WordColumns.evaluate,
    Trace.memoryWord, Word.toBitVec, Word.value, Nat.unpair_pair, limbBase,
    show (64 : ZMod babyBearModulus).val = 64 by decide,
    show (1 : ZMod babyBearModulus).val = 1 by decide] at read ram write
  exact ⟨after, read, ram, write⟩

/-- The accepted native RAM word supplies the byte consumed by Sail's
    original physical RAM path. -/
theorem actual_native_byte_read :
    run (SailRV32.Functions.read_ram .Read_plain (.Load .Data)
      (.Physaddr 4194305) 1 false) before = .ok (18, ()) before := by
  obtain ⟨_, _, ram, _⟩ := actual_native_transport
  have byte := read_subword true (offset := 1) (by decide) (by simp) ram
  have read : (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 1 4194305).run before =
      .ok (18 : BitVec 8) before := by simpa using byte
  have physical := read_ram_sized (Or.inl rfl) (address := 4194305) read
  have address : ((4194305 : BitVec 32).setWidth 34) = (4194305 : BitVec 34) := by decide
  rwa [address] at physical

end Tests.SubwordMemoryHistory
