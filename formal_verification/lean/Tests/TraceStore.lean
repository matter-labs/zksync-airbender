import Airbender.Review.Trace.Theorems
import Airbender.Proofs.Trace.Code
import Airbender.Proofs.Trace.CodeHistory
import Airbender.Proofs.Trace.NativeSailHistory
import Airbender.Proofs.Trace.Terminal
import Airbender.Proofs.Trace.Retirement
import Airbender.Proofs.Trace.PortReads

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

private def before : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity).insert .x1 ((Word.mk 65532 64).toBitVec)
      |>.insert .x2 ((Word.mk 1234 5678).toBitVec)
    mem := (Std.ExtHashMap.emptyWithCapacity).insert 4259840 (0 : BitVec 8)
      |>.insert 4259841 0 |>.insert 4259842 0 |>.insert 4259843 0
      |>.insert 65532 0x23 |>.insert 65533 0xa2 |>.insert 65534 0x20 |>.insert 65535 0 }

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

private def entry : ProgramEntry :=
  ⟨65532, 0x0020a223, .STORE (4, .Regidx 2, .Regidx 1, 4),
    ⟨.wordMemory, 1, 2, 0, ⟨4, 0⟩, 1⟩⟩

set_option maxRecDepth 32768 in
theorem program_image : programImage before [65532] = some [entry] := by
  have bytes : (Cell.ram 65532).read before = .ok 0x0020a223 before := by
    simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
      get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
      before, Std.ExtHashMap.getElem_insert]
  simp only [programImage, List.mapM_cons, List.mapM_nil, programEntry, bytes,
    bind, Option.bind]
  rfl

theorem decoder_bound : Decoded trace [entry] := by
  intro actual member
  simp only [trace, List.mem_singleton] at member
  subst actual
  change ∃ i : Fin 1, _
  exact ⟨0, by decide⟩

theorem grouped_native_store : ∃ after,
    Proofs.SailHistory [.register 1, .register 2, .ram 4259840]
      (Proofs.rowEvents trace.memoryEpoch row).reverse before after := by
  obtain ⟨_, rows, after, _, permutation, _, execution, _⟩ :=
    Proofs.decoded_row_history (by decide) (by decide) accepted boundary
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
      MemoryPort.readCode, pairCode, Proofs.memoryWord, Nat.unpair_pair, assignment,
      row, Word.toBitVec, Word.value, limbBase, ZMod.val_ofNat,
      babyBearModulus] at ramRead
    exact ramRead
  · norm_num [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.word,
      MemoryPort.writeCode, pairCode, Proofs.memoryWord, Nat.unpair_pair, assignment,
      row, Word.toBitVec, Word.value, limbBase, ZMod.val_ofNat,
      babyBearModulus] at ramWrite
    exact ramWrite

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
    Proofs.SailHistory [.register 1, .register 2, .ram 4259840] events before after ∧
    Proofs.SailStateMatches [.register 1, .register 2, .ram 4259840] history after := by
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
    Proofs.SailHistory [.register 1, .register 2, .ram 4259840] events before after ∧
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
    Proofs.SailHistory [.register 1, .register 2, .ram 4259840] events before after ∧
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
    simpa only [Proofs.memoryWord, ramToken, Nat.unpair_pair] using read⟩

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
    Proofs.SailHistory [.register 1, .register 2, .ram 4259840] events before middle ∧
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

end Tests.TraceStore
