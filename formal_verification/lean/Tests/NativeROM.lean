import Tests.TraceExecution

namespace Tests.NativeROM
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

-- LW x1,0(x0), reading its own public ROM instruction word. Every native
-- initialization slot and the ROM permutation read/write value are zero.
private def before : State :=
  { Tests.TraceExecution.before with
    regs := Tests.TraceExecution.before.regs.insert .x1 (0 : BitVec 32)
    mem := Tests.TraceExecution.before.mem.insert 0 (0x83 : BitVec 8)
      |>.insert 1 0x20 |>.insert 2 0 |>.insert 3 0 }

private def cells : List Cell := Tests.TraceExecution.cells ++ [.ram 0]
private def physical : List (MemoryToken babyBearModulus) :=
  ROMView.nativeBootImage Tests.TraceExecution.cells ++ [Cell.initialToken (.ram 0) 0x2083]

private def assignment : Nat → ZMod babyBearModulus
  | 4 | 7 | 25 | 35 | 37 | 44 | 46 | 47 | 48 => 1
  | 2 | 11 => 4
  | 13 => 8
  | 31 | 40 | 41 => 0x2083
  | 36 => 65472
  | 45 => 34
  | _ => 0

private def nativeRow : Row babyBearModulus := ⟨.wordMemory, assignment⟩
private def terminal : List (MemoryToken babyBearModulus) :=
  [⟨(Cell.register 0).addressCode, (4, 0), Nat.pair 0 0⟩,
   ⟨(Cell.register 1).addressCode, (6, 0), Nat.pair 0x2083 0⟩] ++
  (ROMView.nativeBootImage (p := babyBearModulus) Tests.TraceExecution.cells).drop 2 ++
  [⟨(Cell.ram 0).addressCode, (5, 0), Nat.pair 0 0⟩]

private def trace : Data babyBearModulus where
  rows := [nativeRow]
  rom := ROM.table cells physical
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 4 (8, 0)
  initialMemory := ROMView.nativeBootImage cells
  terminalMemory := terminal

private def entry : ProgramEntry :=
  ⟨0, 0x2083, .LOAD (0, .Regidx 0, .Regidx 1, false, 4),
    ⟨.wordMemory, 0, 0, 1, ⟨0, 0⟩, 0, 0⟩⟩

private theorem bytes : (Cell.ram 0).read before = .ok 0x2083 before := by
  simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
    bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before, Std.ExtHashMap.getElem_insert]

private theorem zero_registers : ∀ index, (Cell.register index).read before = .ok 0 before := by
  have numeric : ∀ index : Nat, index < 32 →
      (Cell.register (BitVec.ofNat 5 index)).read before = .ok 0 before := by
    intro index bound
    interval_cases index
    all_goals first
      | rfl
      | (apply read_register; simp [before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert])
  intro index
  simpa using numeric index.toNat index.isLt

private theorem image : initialImage before cells = some physical := by
  simp only [initialImage, cells, Tests.TraceExecution.cells, List.cons_append, List.nil_append,
    List.mapM_cons, List.mapM_nil, zero_registers, bytes, bind, Option.bind]
  rfl

private theorem profile : InitialProfile before cells := by
  refine ⟨?_, zero_registers, ?_⟩
  · apply read_register
    simp [before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert]
  · intro address member bound
    have zero : address = 0 := by simpa [cells, Tests.TraceExecution.cells] using member
    subst address
    change 4194304 ≤ 0 at bound
    omega

private theorem configuration : FlatMemoryConfiguration before := by
  have written : run (SailRV32.Functions.wX_bits (.Regidx 1) 0)
      Tests.TraceExecution.before = .ok ()
        { Tests.TraceExecution.before with regs := Tests.TraceExecution.before.regs.insert .x1 0 } := by
    simp only [SailRV32.Functions.wX_bits, SailRV32.Functions.wX,
      SailRV32.Functions.regval_into_reg, write_callback_pure, freeM_pure_bind]
    exact run_bind_of_ok _ _ _ _ _ (write_register .x1 0 Tests.TraceExecution.before)
  have preserved := configuration_gpr_write Tests.TraceExecution.configuration 1 0 written
  exact configuration_register_frame
    (before := { Tests.TraceExecution.before with
      regs := Tests.TraceExecution.before.regs.insert .x1 (0 : BitVec 32) })
    (after := before) rfl preserved

private theorem inputs : NativeBootBoundary trace before cells [entry] := by
  refine {
    registers := fun index => List.mem_append_left _ (Tests.TraceExecution.inputs.registers index)
    distinct := by decide
    aligned := ?_
    ordinary := ?_
    configuration := configuration
    programImage := ⟨[0], ?_⟩
    code := ?_
    profile := profile
    seed := rfl
    initial := rfl
    rom := ⟨physical, image, rfl⟩ }
  · intro cell member
    simp [cells, Tests.TraceExecution.cells] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · intro address member
    have zero : address = 0 := by simpa [cells, Tests.TraceExecution.cells] using member
    subst address
    unfold OrdinaryWordAddress
    decide
  · simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes,
      bind, Option.bind]
    rfl
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    constructor <;> decide

theorem native_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) (WordMemory.clockConstraints trace.rom) := by
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
    | (change ∃ i : Fin 2, _
       refine ⟨1, ?_⟩
       simp [ROM.rows, cells, physical, Tests.TraceExecution.cells, ROMView.nativeBootImage,
         ROM.row, Cell.initialToken, MemoryToken.word, Word.ofBitVec, ROM.limit, limbBase,
         List.filterMap_cons, List.filterMap_nil]
       rfl)

theorem native_accepted : Accepted trace := by
  constructor
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    exact native_constraints
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · decide

private theorem decoded : Decoded trace [entry] := by
  intro actual member
  have same := List.mem_singleton.mp member
  subst actual
  change ∃ i : Fin 1, _
  exact ⟨0, by decide⟩

/-- A real native ROM load has zero shadow values and nonzero public bytes. -/
theorem distinct_rom_views :
    Cell.initialToken (.ram 0) 0 ∈ trace.initialMemory ∧ assignment 23 = 0 ∧
      (ROMView.token before (Cell.initialToken (p := babyBearModulus) (.ram 0) 0)).word.toBitVec = 0x2083 ∧
      assignment 31 = 0x2083 := by
  have read := ROMView.public_word_read bytes
  simp [trace, ROMView.nativeBootImage, cells, Tests.TraceExecution.cells, Cell.initialToken,
    Cell.addressCode, ROMView.token, ROMView.shadow, Word.ofBitVec,
    MemoryToken.word, assignment] at read ⊢
  rw [read]
  rfl

/-- Substituting physical ROM bytes into the native seed is incorrect. -/
theorem physical_bytes_are_not_native_seed : physical ≠ trace.initialMemory := by decide

/-- The same native trace reaches the actual Sail state and terminal register
    value. The ROM permutation token never supplies the instruction bytes. -/
theorem complete_rom_load [MemoryPlatform SailRV32.exception] :
    ∃ after, AirbenderTrace [entry] before after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok 4 after ∧
      (Cell.register 1).read after = .ok 0x2083 after := by
  obtain ⟨after, execution, pc, terminal⟩ := native_boot_soundness inputs native_accepted decoded
  refine ⟨after, execution, pc, ?_⟩
  have read := terminal ⟨(Cell.register 1).addressCode, (6, 0), Nat.pair 0x2083 0⟩
    (by simp [trace, Tests.NativeROM.terminal])
  obtain ⟨cell, _, equal, actual⟩ := read
  have same : cell = .register 1 := Proofs.cell_address_injective equal
  subst cell
  simpa [ROMView.token, ROMView.shadow, Cell.addressCode, MemoryToken.word,
    Word.toBitVec, Word.value, limbBase] using actual

end Tests.NativeROM
