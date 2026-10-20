import Slop.Trace.Claims
import Slop.Trace.Code
import Slop.Trace.CodeHistory
import Slop.Trace.NativeSailHistory
import Slop.Trace.Terminal
import Slop.Trace.Retirement
import Slop.Trace.WordMemory
import Slop.Final.Circuits.WordMemory.Theorems

namespace Tests.TraceStore
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384

-- SW x2,4(x1), crossing a limb boundary. Native state starts at PC 65532,
-- clock four; the three imported ports refresh x1/x2 and write RAM at 4259840.
private def assignment : Nat → ZMod babyBearModulus
  | 0 | 17 => 65532
  | 2 | 8 => 4
  | 13 => 8
  | 4 | 5 | 10 | 12 | 33 | 36 | 44 | 46 | 47 | 48 => 1
  | 6 | 19 => 2
  | 18 => 64
  | 23 | 31 => 1234
  | 24 | 32 => 5678
  | 26 => 65
  | 38 => 4259840
  | _ => 0

private def row : Row babyBearModulus := ⟨.wordMemory, assignment⟩
private def regToken (index time lo hi : Nat) : MemoryToken babyBearModulus :=
  ⟨Nat.pair 0 (Nat.pair index 0), (time, 0), Nat.pair lo hi⟩
private def ramToken (loAddress hiAddress time lo hi : Nat) : MemoryToken babyBearModulus :=
  ⟨Nat.pair 1 (Nat.pair loAddress hiAddress), (time, 0), Nat.pair lo hi⟩
private def initial : List (MemoryToken babyBearModulus) :=
  [regToken 1 0 65532 64, regToken 2 0 1234 5678, ramToken 0 65 0 0 0]
private def rom : Table (ZMod babyBearModulus) (fields 9) :=
  ROM.table [.register 1, .register 2, .ram 4259840] initial
private def trace : Data babyBearModulus where
  rows := [row]
  rom := rom
  initial := row.start
  terminal := row.finish
  initialMemory := initial
  terminalMemory := [regToken 1 4 65532 64, regToken 2 5 1234 5678, ramToken 0 65 6 1234 5678]

private def attributes : SailRV32.PMA :=
  { (default : SailRV32.PMA) with readable := true, writable := true, executable := true }

private def before : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity :
      Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .mstatus 0 |>.insert .cur_privilege .Machine |>.insert .misa 0x40000100
      |>.insert .senvcfg 0 |>.insert .menvcfg 0x10
      |>.insert .pmpcfg_n (Vector.replicate 64 0)
      |>.insert .pmpaddr_n (Vector.replicate 64 0)
      |>.insert .pma_regions [Reference.RiscV.Sail.rv32Region attributes]
      |>.insert .mhartid 7 |>.insert .htif_tohost_base none |>.insert .PC (65532 : BitVec 32)
      |>.insert .x1 ((Word.mk 65532 64).toBitVec)
      |>.insert .x2 ((Word.mk 1234 5678).toBitVec)
    mem := (Std.ExtHashMap.emptyWithCapacity).insert 4259840 (0 : BitVec 8)
      |>.insert 4259841 0 |>.insert 4259842 0 |>.insert 4259843 0
      |>.insert 65532 0x23 |>.insert 65533 0xa2 |>.insert 65534 0x20 |>.insert 65535 0 }

set_option backward.isDefEq.respectTransparency false in
private theorem configuration : Reference.RiscV.Sail.FlatMemoryConfiguration before := by
  constructor
  · simp [before, Std.ExtDHashMap.get?_insert]
  · simp [before, Std.ExtDHashMap.get?_insert]
  · exact ⟨0x40000100, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨0, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨0x10, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · simp [before, Std.ExtDHashMap.get?_insert]
  · exact ⟨Vector.replicate 64 0, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨attributes, by simp [before, Std.ExtDHashMap.get?_insert], rfl, rfl, rfl⟩
  · exact ⟨7, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · simp [before, Std.ExtDHashMap.get?_insert]

theorem public_initial_image : initialImage before [.register 1, .register 2, .ram 4259840] =
    some trace.initialMemory := by
  have one : (Cell.register 1).read before = .ok ((Word.mk 65532 64).toBitVec) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have two : (Cell.register 2).read before = .ok ((Word.mk 1234 5678).toBitVec) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  have ram : (Cell.ram 4259840).read before = .ok 0 before := by
    simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
      get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
      before, Std.ExtHashMap.getElem_insert]
  simp only [initialImage, List.mapM_cons, List.mapM_nil, one, two, ram, bind, Option.bind]
  rfl

theorem local_satisfies : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) (WordMemory.clockConstraints rom) := by
  simp [WordMemory.clockConstraints, WordMemory.importedConstraints,
    WordMemory.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, assignment, Lookup.Contains, Table.toRaw]
  all_goals repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, assignment, limbBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (apply Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, assignment, timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (change ∃ i : Fin 1, _
       exact ⟨0, rfl⟩)

theorem accepted : Accepted trace := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact local_satisfies
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · dsimp only [trace, initial]
    decide

private theorem boundary : ClockBoundary trace := by
  constructor
  · change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro token member
    simp [trace, initial] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide

private theorem aligned_domain :
    ∀ cell : Cell, cell ∈ [.register 1, .register 2, .ram 4259840] → cell.Aligned := by
  intro cell member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl <;> trivial

private theorem ordinary_domain : ∀ address,
    Cell.ram address ∈ [.register 1, .register 2, .ram 4259840] →
      Reference.RiscV.Sail.OrdinaryWordAddress address := by
  intro address member
  simp at member
  subst address
  unfold Reference.RiscV.Sail.OrdinaryWordAddress
  decide

private def entry : ProgramEntry :=
  ⟨65532, 0x0020a223, .STORE (4, .Regidx 2, .Regidx 1, 4),
    ⟨.wordMemory, 1, 2, 0, ⟨4, 0⟩, 1, 0⟩⟩

set_option maxRecDepth 32768 in
theorem program_image : programImage before [65532] = some [entry] := by
  have bytes : (Cell.ram 65532).read before = .ok 0x0020a223 before := by
    simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
      get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
      before, Std.ExtHashMap.getElem_insert]
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes,
    bind, Option.bind]
  rfl

theorem decoder_bound : Decoded trace [entry] := by
  intro actual member
  simp only [trace, List.mem_singleton] at member
  subst actual
  change ∃ i : Fin 1, _
  exact ⟨0, by decide⟩

theorem grouped_native_store : ∃ after,
    SailHistory [.register 1, .register 2, .ram 4259840]
      (Trace.rowEvents trace.memoryEpoch row).reverse before after := by
  obtain ⟨_, rows, after, _, permutation, _, execution, _⟩ :=
    Proofs.decoded_row_history Proofs.standardDecoderRules (by decide) (by decide) accepted boundary
      public_initial_image (by decide) (by
        intro cell member
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
        rcases member with rfl | rfl | rfl <;> trivial) program_image decoder_bound
  have singleton : rows = [row] := List.perm_singleton.mp permutation
  rw [singleton] at execution
  exact ⟨after, by simpa only [List.flatMap_singleton] using execution⟩

-- Actual Sail operand and RAM accesses are derived from accepted native ports,
-- not supplied to the soundness theorem as desired-read assumptions.
set_option maxHeartbeats 2000000 in
theorem actual_store_accesses : ∃ after,
    Reference.Sail.run (SailRV32.Functions.rX_bits (.Regidx 2)) before =
      .ok (Word.mk 1234 5678).toBitVec before ∧
    (Cell.ram 4259840).read before = .ok 0 before ∧
    Reference.Sail.run (Reference.RiscV.Sail.writeMemory (size := 4) 4259840
      (Word.mk 1234 5678).toBitVec) before = .ok () after := by
  obtain ⟨after, history⟩ := grouped_native_store
  have register := Proofs.word_history_register_read (by decide) true
    (Verification.holds_of_sublist local_satisfies
      (List.sublist_append_left (WordMemory.importedConstraints rom)
        WordMemory.importedConstraintsTimestampLookups)) (by rfl)
    (entry := entry) (by decide) trace.memoryEpoch history
  have ramRead := Proofs.row_history_ram_read (by decide) (by decide) accepted boundary
    public_initial_image (row := row) (List.mem_singleton_self row)
    (port := WordMemory.importedConstraintsMemoryPorts[2])
    (by simp [Row.ports, WordMemory.importedConstraintsMemoryPorts, row])
    (by exact ⟨Nat.pair 0 65, rfl⟩) history
  have ramWrite := Proofs.row_history_ram_write (by decide) (by decide) accepted boundary
    public_initial_image (row := row) (List.mem_singleton_self row)
    (port := WordMemory.importedConstraintsMemoryPorts[2])
    (by simp [Row.ports, WordMemory.importedConstraintsMemoryPorts, row]) (by rfl)
    (by exact ⟨Nat.pair 0 65, rfl⟩) history
  refine ⟨after, ?_, ?_, ?_⟩
  · norm_num [entry, assignment, ZMod.val_ofNat, babyBearModulus] at register
    exact register
  · norm_num [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.word,
      MemoryPort.readCode, pairCode, memoryWord, Nat.unpair_pair, assignment,
      row, Word.toBitVec, Word.value, limbBase, ZMod.val_ofNat,
      babyBearModulus] at ramRead
    exact ramRead
  · norm_num [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.word,
      MemoryPort.writeCode, pairCode, memoryWord, Nat.unpair_pair, assignment,
      row, Word.toBitVec, Word.value, limbBase, ZMod.val_ofNat,
      babyBearModulus] at ramWrite
    exact ramWrite

set_option maxHeartbeats 2000000 in
theorem actual_virtual_store [Sail.ArchSem.MemoryPlatform SailRV32.exception] : ∃ after,
    SailHistory [.register 1, .register 2, .ram 4259840]
      (Trace.rowEvents trace.memoryEpoch row).reverse before after ∧
    Reference.Sail.run (SailRV32.Functions.vmem_write (.Regidx 1) 4 4
      (Word.mk 1234 5678).toBitVec (.Store .Data) false false false) before =
        .ok (.Ok true) after := by
  obtain ⟨after, history⟩ := grouped_native_store
  have transport := Proofs.word_row_transport (by decide) (by decide) accepted boundary
    public_initial_image rfl aligned_domain ordinary_domain
    (w := assignment) (List.mem_singleton_self row) true rfl
    (entry := entry) rfl (by decide) configuration history
  norm_num [entry, assignment, ZMod.val_ofNat, babyBearModulus] at transport
  exact ⟨after, history, transport.2⟩

theorem actual_sail_store [Sail.ArchSem.MemoryPlatform SailRV32.exception] : ∃ after,
    SailHistory [.register 1, .register 2, .ram 4259840]
      (Trace.rowEvents trace.memoryEpoch row).reverse before after ∧
    Reference.Sail.run (SailRV32.Functions.execute_STORE 4 (.Regidx 2) (.Regidx 1) 4)
      before = .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  obtain ⟨after, history⟩ := grouped_native_store
  exact ⟨after, history, Proofs.word_row_store_execution (by decide) (by decide)
    accepted boundary public_initial_image rfl aligned_domain ordinary_domain
    (w := assignment) (List.mem_singleton_self row)
    (entry := entry) rfl (by decide) rfl configuration history⟩

set_option maxHeartbeats 2000000 in
theorem actual_store_step [Sail.ArchSem.MemoryPlatform SailRV32.exception] : ∃ after,
    SailHistory [.register 1, .register 2, .ram 4259840]
      (Trace.rowEvents trace.memoryEpoch row).reverse before after ∧
    Reference.Sail.run (Reference.RiscV.Sail.normalStep
      (SailRV32.Functions.execute_STORE 4 (.Regidx 2) (.Regidx 1) 4)) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        { after with regs := after.regs.insert .nextPC (65536 : BitVec 32) |>.insert .PC 65536 } := by
  obtain ⟨after, history⟩ := grouped_native_store
  refine ⟨after, history, Proofs.word_row_store_step (by decide) (by decide)
    accepted boundary public_initial_image rfl aligned_domain ordinary_domain configuration
    (by change (Word.mk 65532 0).Bounded; constructor <;> decide)
    (w := assignment) (List.mem_singleton_self row) (entry := entry) rfl (by decide) rfl
    (SailHistory.nil before) history ?_⟩
  apply Reference.RiscV.Sail.read_register
  simp [assignment, Word.toBitVec, Word.value, limbBase, babyBearModulus,
    before, Std.ExtDHashMap.get?_insert]
  decide

theorem derived_ram_address :
    (Word.mk (assignment 25).val (assignment 26).val).Bounded ∧
      ROM.limit ≤ (Word.mk (assignment 25).val (assignment 26).val).toBitVec.toNat :=
  Proofs.native_store_address (by decide) (by decide) accepted boundary public_initial_image
    (List.mem_singleton_self row) rfl

theorem preserved_fetched_bytes : ∃ after,
    Reference.Sail.run (Reference.RiscV.Sail.writeMemory (size := 4)
      (Word.mk (assignment 25).val (assignment 26).val).toBitVec
      (Word.mk (assignment 31).val (assignment 32).val).toBitVec) before = .ok () after ∧
    (Cell.ram 65532).read after = .ok 0x0020a223 after := by
  apply Proofs.native_store_code_frame (by decide) (by decide) accepted boundary
    public_initial_image (List.mem_singleton_self row) rfl 65532 (by decide) (by decide)
  simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
    get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
    before, Std.ExtHashMap.getElem_insert]

theorem native_sail_execution : ∃ (history : TimestampSortedMemoryAccessList)
    (events : List MemoryAccess) (after : Reference.RiscV.Sail.State),
    MemoryHistory trace history ∧ events.Perm trace.nativeEvents ∧
    SailHistory [.register 1, .register 2, .ram 4259840] events before after ∧
    SailStateMatches [.register 1, .register 2, .ram 4259840] history after := by
  obtain ⟨history, events, _, after, consistent, _, permutation, execution, final⟩ :=
    Proofs.native_sail_history (by decide) (by decide) accepted boundary
      public_initial_image (by decide) (by
        intro cell member
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
        rcases member with rfl | rfl | rfl <;> trivial) (by
        intro event member zero
        obtain ⟨cell, present, address⟩ := Proofs.native_event_cells
          (by decide) (by decide) accepted boundary public_initial_image event member
        have same := Proofs.cell_address_injective (address.trans zero)
        subst cell
        simp at present)
  exact ⟨history, events, after, consistent, permutation, execution, final⟩

/-- The complete accepted history, including readonly clock refreshes, keeps
    the fetched code word even though it is outside the tracked cell domain. -/
theorem native_history_preserves_code : ∃ (history : TimestampSortedMemoryAccessList)
    (events : List MemoryAccess) (after : Reference.RiscV.Sail.State),
    MemoryHistory trace history ∧ events.Perm trace.nativeEvents ∧
    SailHistory [.register 1, .register 2, .ram 4259840] events before after ∧
    (Cell.ram 65532).read after = .ok 0x0020a223 after := by
  obtain ⟨history, events, after, consistent, permutation, execution, _⟩ := native_sail_execution
  refine ⟨history, events, after, consistent, permutation, execution, ?_⟩
  apply Proofs.native_history_code_frame (by decide) (by decide) accepted boundary
    public_initial_image permutation execution 65532 (by decide) (by decide)
  simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
    get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
    before, Std.ExtHashMap.getElem_insert]

theorem native_sail_terminal_ram : ∃ (events : List MemoryAccess)
    (after : Reference.RiscV.Sail.State),
    events.Perm trace.nativeEvents ∧
    SailHistory [.register 1, .register 2, .ram 4259840] events before after ∧
    (Cell.ram 4259840).read after = .ok (Word.mk 1234 5678).toBitVec after := by
  obtain ⟨history, events, after, consistent, permutation, execution, final⟩ := native_sail_execution
  have reads := Proofs.terminal_sail_reads (by decide) (by decide) accepted boundary
    public_initial_image (by decide) consistent final
  obtain ⟨cell, _, address, read⟩ := reads (ramToken 0 65 6 1234 5678)
    (by change _ ∈ [_, _, _]; simp)
  change cell.addressCode = (Cell.ram 4259840).addressCode at address
  have same := Proofs.cell_address_injective address
  subst cell
  exact ⟨events, after, permutation, execution, by
    simpa only [memoryWord, ramToken, Nat.unpair_pair] using read⟩

private def wrongTerminal : Data babyBearModulus :=
  { trace with terminalMemory :=
    [regToken 1 4 65532 64, regToken 2 5 1234 5678, ramToken 0 65 6 99 5678] }

theorem fabricated_terminal_value_rejected : ¬ Accepted wrongTerminal := by
  intro accepted
  have mismatch : ¬ (wrongTerminal.initialMemory ++ wrongTerminal.rows.flatMap Row.writes).Perm
      (wrongTerminal.terminalMemory ++ wrongTerminal.rows.flatMap Row.reads) := by decide
  exact mismatch accepted.memory

theorem native_sail_retirement : ∃ (events : List MemoryAccess)
    (middle after : Reference.RiscV.Sail.State),
    events.Perm trace.nativeEvents ∧
    SailHistory [.register 1, .register 2, .ram 4259840] events before middle ∧
    Reference.Sail.run (do
      SailRV32.writeReg .nextPC (65536 : BitVec 32)
      SailRV32.Functions.tick_pc ()) middle = .ok () after ∧
    Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) after = .ok 65536 after ∧
    (Cell.ram 4259840).read after = .ok (Word.mk 1234 5678).toBitVec after := by
  obtain ⟨events, middle, permutation, execution, read⟩ := native_sail_terminal_ram
  let prepared : Reference.RiscV.Sail.State :=
    { middle with regs := middle.regs.insert .nextPC (65536 : BitVec 32) }
  let after : Reference.RiscV.Sail.State :=
    { prepared with regs := prepared.regs.insert .PC (65536 : BitVec 32) }
  refine ⟨events, middle, after, permutation, execution, ?_, ?_, ?_⟩
  · rw [Reference.Sail.run_bind_of_ok _ _ _ _ _
      (Reference.RiscV.Sail.write_register .nextPC (65536 : BitVec 32) middle)]
    exact Reference.RiscV.Sail.tick_pc_run (by simp)
  · exact Reference.RiscV.Sail.read_register (by simp [after])
  · exact Proofs.cell_read_PC (.ram 4259840)
      (Proofs.cell_read_nextPC (.ram 4259840) read 65536) 65536

-- Per-circuit review claim with inhabited public inputs, using the same SW
-- fixture. The table and actual decoded instruction come from its public state.
private def pooledProgram : List PooledProgramEntry :=
  [entry.mapFamily pooledArithmeticFamily]

private def pooled : PooledTrace babyBearModulus where
  rows := [⟨.wordMemory, assignment⟩]
  rom := ⟨rom, Verification.subwordTable (ROM.words before)⟩
  initial := trace.initial
  terminal := trace.terminal
  initialMemory := trace.initialMemory
  terminalMemory := trace.terminalMemory

private theorem pooledAccepted : Accepted pooled := by
  constructor
  · intro actual member
    simp only [pooled, List.mem_singleton] at member
    subst actual
    exact local_satisfies
  · intro actual member
    simp only [pooled, List.mem_singleton] at member
    subst actual
    rfl
  · exact accepted.states
  · exact accepted.memory

private theorem pooledImage : pooledProgramImage before [65532] = some pooledProgram := by
  have bytes := (Proofs.program_sources program_image entry (by simp)).bytes
  change (Cell.ram 65532).read before = .ok 0x0020a223 before at bytes
  simp only [pooledProgramImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, bind, Option.bind]
  rfl

private theorem pooledDecoded : PooledDecoded pooled pooledProgram := by
  intro actual member
  simp only [pooled, List.mem_singleton] at member
  subst actual
  change ∃ i : Fin 1, _ = _
  exact ⟨0, by decide⟩

private theorem pooledInputs : NativeInputs pooledDecoderFields pooled before
    [.register 1, .register 2, .ram 4259840] pooledProgram := by
  refine ⟨by decide, aligned_domain, public_initial_image, ?_, ⟨[65532], pooledImage⟩, ?_⟩
  · refine ⟨(4, 0), ?_⟩
    have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) before =
        .ok 65532 before := by
      apply Reference.RiscV.Sail.read_register
      simp [before, Std.ExtDHashMap.get?_insert]
    simp only [initialState, pc]
    rfl
  · exact ⟨boundary.initial, boundary.aligned, boundary.memory⟩

/-- Real SW effects follow from the review model with no per-row range, read
    value or successful-access assumption. -/
theorem per_circuit_store_soundness [Sail.ArchSem.MemoryPlatform SailRV32.exception] :
    ∃ input : WordMemory.Input,
      (WordMemory.circuitModel pooled before [.register 1, .register 2, .ram 4259840] pooledProgram).relation
        input ⟨⟨0, 65⟩, ⟨1234, 5678⟩, ⟨0, 1⟩⟩ assignment ∧
      WordMemory.InterfaceAssumptions pooled before [.register 1, .register 2, .ram 4259840] pooledProgram ∧
      WordMemory.spec input ⟨⟨0, 65⟩, ⟨1234, 5678⟩, ⟨0, 1⟩⟩ := by
  have member : (⟨.wordMemory, assignment⟩ : Row babyBearModulus PooledFamily) ∈ pooled.rows := by
    simp [pooled]
  obtain ⟨current, position⟩ := Proofs.pooled_row_position_exists (by decide) (by decide)
    pooledAccepted pooledInputs.clocks pooledInputs.image pooledInputs.distinct pooledInputs.aligned
    pooledImage pooledDecoded member
  let input : WordMemory.Input :=
    ⟨true, ⟨65532, 64⟩, ⟨4, 0⟩, ⟨1234, 5678⟩, ⟨65532, 0⟩, .Regidx 1, .Regidx 2, .Regidx 0, 4, current⟩
  have mapping : WordMemory.TraceMapping pooled before [.register 1, .register 2, .ram 4259840]
      pooledProgram input ⟨⟨0, 65⟩, ⟨1234, 5678⟩, ⟨0, 1⟩⟩ assignment := by
    refine ⟨?_, position, ?_⟩
    · constructor <;> rfl
    · refine ⟨entry.mapFamily pooledArithmeticFamily, by simp [pooledProgram], rfl, ?_, rfl⟩
      decide
  have assumptions : WordMemory.InterfaceAssumptions pooled before
      [.register 1, .register 2, .ram 4259840] pooledProgram :=
    ⟨⟨pooledInputs, rfl, rfl⟩, ordinary_domain, configuration⟩
  have core := Verification.holds_of_sublist local_satisfies
    (List.sublist_append_left (WordMemory.importedConstraints rom) WordMemory.importedConstraintsTimestampLookups)
  have relation : (WordMemory.circuitModel pooled before [.register 1, .register 2, .ram 4259840]
      pooledProgram).relation input ⟨⟨0, 65⟩, ⟨1234, 5678⟩, ⟨0, 1⟩⟩ assignment :=
    ⟨⟨pooledAccepted, pooledDecoded, member⟩, mapping⟩
  exact ⟨input, relation, assumptions, WordMemory.babyBear_soundness pooled before
    [.register 1, .register 2, .ram 4259840] pooledProgram assumptions input _ _ relation⟩

/-- A field-congruent source limb is not an alternative interpretation of the row. -/
theorem per_circuit_field_alias_rejected (current : Reference.RiscV.Sail.State) :
    ¬ WordMemory.TraceMapping pooled before [.register 1, .register 2, .ram 4259840] pooledProgram
      (⟨true, ⟨babyBearModulus + 65532, 64⟩, ⟨4, 0⟩, ⟨1234, 5678⟩, ⟨65532, 0⟩,
        .Regidx 1, .Regidx 2, .Regidx 0, 4, current⟩ : WordMemory.Input)
      ⟨⟨0, 65⟩, ⟨1234, 5678⟩, ⟨0, 1⟩⟩ assignment := by
  intro mapping
  have impossible := mapping.words.sourceLo
  change babyBearModulus + 65532 = (assignment 17).val at impossible
  have small := ZMod.val_lt (assignment 17)
  omega

namespace Load

-- LW x1,4(x1): the native destination aliases rs1, and its prior timestamp
-- must refer to the first port's refresh. The public RAM word initially is zero.
private def loadAssignment : Nat → ZMod babyBearModulus
  | 0 | 17 | 29 => 65532
  | 2 | 8 | 27 => 4
  | 13 => 8
  | 4 | 5 | 7 | 12 | 25 | 33 | 36 | 44 | 46 | 47 | 48 => 1
  | 18 | 30 => 64
  | 20 => 65
  | 38 => 4259840
  | _ => 0

private def loadRow : Row babyBearModulus := ⟨.wordMemory, loadAssignment⟩
private def loadCells : List Cell := [.register 1, .ram 4259840]
private def loadInitial : List (MemoryToken babyBearModulus) :=
  [regToken 1 0 65532 64, ramToken 0 65 0 0 0]
private def loadTrace : Data babyBearModulus where
  rows := [loadRow]
  rom := ROM.table loadCells loadInitial
  initial := loadRow.start
  terminal := loadRow.finish
  initialMemory := loadInitial
  terminalMemory := [regToken 1 6 0 0, ramToken 0 65 5 0 0]

private def loadState : Reference.RiscV.Sail.State :=
  Reference.RiscV.Sail.wordWriteState before 65532 0x0040a083

private def loadEntry : ProgramEntry :=
  ⟨65532, 0x0040a083, .LOAD (4, .Regidx 1, .Regidx 1, false, 4),
    ⟨.wordMemory, 1, 0, 1, ⟨4, 0⟩, 0, 0⟩⟩

theorem public_image : initialImage loadState loadCells = some loadTrace.initialMemory := by
  have register : (Cell.register 1).read loadState =
      .ok (Word.mk 65532 64).toBitVec loadState := by
    apply Reference.RiscV.Sail.read_register
    simp [loadState, Reference.RiscV.Sail.wordWriteState, before, Std.ExtDHashMap.get?_insert]
  have ram : (Cell.ram 4259840).read loadState = .ok 0 loadState := by
    apply Reference.RiscV.Sail.written_word_disjoint 65532 0x0040a083 (by decide)
    simp [Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
      get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
      before, Std.ExtHashMap.getElem_insert]
  simp only [initialImage, loadCells, List.mapM_cons, List.mapM_nil, register, ram,
    bind, Option.bind]
  rfl

set_option maxRecDepth 32768 in
theorem program_image : programImage loadState [65532] = some [loadEntry] := by
  have bytes : (Cell.ram 65532).read loadState = .ok 0x0040a083 loadState :=
    Reference.RiscV.Sail.written_word_read before 65532 0x0040a083
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, bind, Option.bind]
  rfl

theorem decoder_bound : Decoded loadTrace [loadEntry] := by
  intro actual member
  simp only [loadTrace, List.mem_singleton] at member
  subst actual
  change ∃ i : Fin 1, _
  exact ⟨0, by decide⟩

theorem satisfies : FlatOperation.ConstraintsHoldFlat
    (Verification.environment loadAssignment) (WordMemory.clockConstraints loadTrace.rom) := by
  simp [WordMemory.clockConstraints, WordMemory.importedConstraints,
    WordMemory.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, loadAssignment, Lookup.Contains, Table.toRaw]
  all_goals repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, loadAssignment, limbBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (apply Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, loadAssignment, timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (change ∃ i : Fin 1, _
       exact ⟨0, rfl⟩)

theorem accepted : Accepted loadTrace := by
  constructor
  · intro actual member
    simp only [loadTrace, List.mem_singleton] at member
    subst actual
    exact satisfies
  · intro actual member
    simp only [loadTrace, List.mem_singleton] at member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · dsimp only [loadTrace, loadInitial]
    decide

private theorem loadBoundary : ClockBoundary loadTrace := by
  constructor
  · change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro token member
    simp [loadTrace, loadInitial] at member
    rcases member with rfl | rfl <;> constructor <;> decide

private theorem loadAligned : ∀ cell ∈ loadCells, cell.Aligned := by
  intro cell member
  simp [loadCells] at member
  rcases member with rfl | rfl <;> trivial

private theorem loadOrdinary : ∀ address, Cell.ram address ∈ loadCells →
    Reference.RiscV.Sail.OrdinaryWordAddress address := by
  intro address member
  simp [loadCells] at member
  subst address
  unfold Reference.RiscV.Sail.OrdinaryWordAddress
  decide

theorem grouped : ∃ after, SailHistory loadCells
    (Trace.rowEvents loadTrace.memoryEpoch loadRow).reverse loadState after := by
  obtain ⟨_, rows, after, _, permutation, _, execution, _⟩ :=
    Proofs.decoded_row_history Proofs.standardDecoderRules (by decide) (by decide) accepted loadBoundary public_image
      (by decide) loadAligned program_image decoder_bound
  have singleton : rows = [loadRow] := List.perm_singleton.mp permutation
  rw [singleton] at execution
  exact ⟨after, by simpa only [List.flatMap_singleton] using execution⟩

set_option maxHeartbeats 2000000 in
theorem actual_sail_load [Sail.ArchSem.MemoryPlatform SailRV32.exception] : ∃ after,
    SailHistory loadCells
      (Trace.rowEvents loadTrace.memoryEpoch loadRow).reverse loadState after ∧
    Reference.Sail.run (SailRV32.Functions.execute_LOAD 4 (.Regidx 1) (.Regidx 1) false 4)
      loadState = .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  obtain ⟨after, history⟩ := grouped
  exact ⟨after, history, Proofs.word_row_load_execution (by decide) (by decide)
    accepted loadBoundary public_image rfl loadAligned loadOrdinary
    (Reference.RiscV.Sail.configuration_word_write configuration 65532 0x0040a083)
    (w := loadAssignment) (List.mem_singleton_self loadRow)
    (entry := loadEntry) rfl rfl (by decide) rfl
    (events := []) (by simp) (.nil loadState) history⟩

theorem public_pc : initialState loadState (4, 0) = some loadTrace.initial := by
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) loadState =
      .ok (65532 : BitVec 32) loadState := by
    apply Reference.RiscV.Sail.read_register
    simp [loadState, Reference.RiscV.Sail.wordWriteState, before, Std.ExtDHashMap.get?_insert]
  simp only [initialState, pc]
  rfl

theorem native_pc_increment : loadRow.finish.word.toBitVec = loadRow.start.word.toBitVec + 4 :=
  Proofs.row_pc_successor (by decide) (by decide) accepted
    (Proofs.initial_pc_bound (by decide) public_pc) (List.mem_singleton_self loadRow)

set_option maxHeartbeats 2000000 in
theorem actual_load_step [Sail.ArchSem.MemoryPlatform SailRV32.exception] : ∃ after,
    SailHistory loadCells
      (Trace.rowEvents loadTrace.memoryEpoch loadRow).reverse loadState after ∧
    Reference.Sail.run (Reference.RiscV.Sail.normalStep
      (SailRV32.Functions.execute_LOAD 4 (.Regidx 1) (.Regidx 1) false 4)) loadState =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        { after with regs := after.regs.insert .nextPC (65536 : BitVec 32) |>.insert .PC 65536 } := by
  obtain ⟨after, history⟩ := grouped
  refine ⟨after, history, Proofs.word_row_load_step (by decide) (by decide)
    accepted loadBoundary public_image rfl loadAligned loadOrdinary
    (Reference.RiscV.Sail.configuration_word_write configuration 65532 0x0040a083)
    (Proofs.initial_pc_bound (by decide) public_pc)
    (w := loadAssignment) (List.mem_singleton_self loadRow)
    (entry := loadEntry) rfl rfl (by decide) rfl
    (events := []) (by simp) (.nil _) history ?_⟩
  apply Reference.RiscV.Sail.read_register
  simp [loadAssignment, Word.toBitVec, Word.value, limbBase, babyBearModulus,
    loadState, Reference.RiscV.Sail.wordWriteState, before, Std.ExtDHashMap.get?_insert]
  decide

end Load
end Tests.TraceStore
