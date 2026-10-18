import Airbender.Review.Trace.Families.WordMemory.Platform
import Airbender.Proofs.Trace.Families.WordMemory.ProjectedPorts
import Airbender.Review.Trace.Families.WordMemory.SailHistory
import Airbender.Review.Trace.Families.WordMemory.CodeHistory
import Airbender.Proofs.Trace.Terminal

namespace Tests.WordMemorySailHistory
open Airbender Verification Arithmetic Trace

private def rom : WordROM := ⟨[0x0020a023, 0x0000a183], by decide⟩

/-- Full native row with PC zero, time four and prior port timestamps zero. -/
private def row (store inROM discard : Bool) (i : Nat) : ZMod mersenne31Modulus :=
  let addressHi := if inROM then 0 else 64
  let rd := if store || discard then 0 else 3
  let candidateLo := if store then 0 else if inROM then 4211 else 123
  let candidateHi := if !store && inROM then 49152 else 0
  let writeLo := if store then 123 else if discard then 0 else candidateLo
  let writeHi := if discard then 0 else candidateHi
  if i = 2 then 4
  else if i = 4 ∨ i = 5 ∨ i = 49 ∨ i = 52 ∨ i = 55 then 1
  else if i = 6 then if store then 2 else 0
  else if i = 7 then rd
  else if i = 8 then if rd = 0 then 1 else 0
  else if i = 11 then 2
  else if i = 12 then if store then 1 else 0
  else if i = 13 then 4
  else if i = 15 then 8
  else if i = 17 ∨ i = 19 then 16
  else if i = 18 ∨ i = 20 then addressHi
  else if i = 22 then if inROM then 0 else 1
  else if i = 24 then if !store && inROM then 1 else 0
  else if i = 25 then if !store && !inROM then 1 else 0
  else if i = 26 then 4211
  else if i = 27 then 49152
  else if i = 28 then if store then 2 else 16
  else if i = 29 then if store then 0 else addressHi
  else if i = 30 then 123
  else if i = 32 then if store then 0 else 1
  else if i = 33 then if store then 16 else rd
  else if i = 34 then if store then addressHi else 0
  else if i = 37 then writeLo
  else if i = 38 then writeHi
  else if i = 39 then candidateLo
  else if i = 40 then candidateHi
  else if i = 41 then if discard then 0 else candidateLo
  else if i = 42 then if discard then 0 else candidateHi
  else if i = 43 then 1227138194
  else if i = 45 then 2147450879
  else 0

private theorem satisfies (store inROM discard : Bool) (legal : (store && inROM) = false) :
    FlatOperation.ConstraintsHoldFlat (environment (row store inROM discard))
      (Airbender.WordMemory.importedConstraints rom) := by
  cases store <;> cases inROM <;> cases discard <;> simp_all only [Bool.false_and,
    Bool.true_and, Bool.true_eq_false]
  all_goals
    simp [Airbender.WordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Expression.eval, environment, row]
    repeat' apply And.intro
    all_goals first | (apply range16_contains; decide) |
      (apply timestamp19_contains; decide) | try decide
    all_goals
      simp only [Lookup.Contains, fixed3, Table.toRaw, romSeparatorTable,
        romWordTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
        Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, row]
      solve
      | refine ⟨⟨0, by decide⟩, ?_⟩
        norm_num [romSeparatorRow, WordROM.row, WordROM.word, rom]
      | refine ⟨⟨64, by decide⟩, ?_⟩
        norm_num [romSeparatorRow, WordROM.row, WordROM.word, rom]
      | refine ⟨⟨4, by decide⟩, ?_⟩
        norm_num [romSeparatorRow, WordROM.row, WordROM.word, rom]

private def storeRow : Row mersenne31Modulus WordMemoryFamily := ⟨.wordMemory, row true false false⟩

-- The later load reads the store at timestamp six. Rows are supplied backwards.
private def loadAssignment (i : Nat) : ZMod mersenne31Modulus :=
  if i = 0 then 4 else if i = 2 ∨ i = 13 then 8 else if i = 15 then 12
  else if i = 47 then 4 else if i = 50 then 6 else if i = 43 then 1801116374
  else row false false false i
private def loadRow : Row mersenne31Modulus WordMemoryFamily := ⟨.wordMemory, loadAssignment⟩

private def regToken (index time lo hi : Nat) : MemoryToken mersenne31Modulus :=
  ⟨Nat.pair 0 (Nat.pair index 0), (time, 0), Nat.pair lo hi⟩
private def ramToken (time value : Nat) : MemoryToken mersenne31Modulus :=
  ⟨Nat.pair 1 (Nat.pair 16 64), (time, 0), Nat.pair value 0⟩

private def trace : Data mersenne31Modulus WordMemoryFamily where
  rows := [loadRow, storeRow]
  rom := rom
  initial := storeRow.start
  terminal := loadRow.finish
  initialMemory := [regToken 1 0 16 64, regToken 2 0 123 0, ramToken 0 0, regToken 3 0 0 0]
  terminalMemory := [regToken 1 8 16 64, regToken 2 5 123 0, ramToken 9 123, regToken 3 10 123 0]

private theorem load_satisfies :
    FlatOperation.ConstraintsHoldFlat (environment loadAssignment)
      (Airbender.WordMemory.importedConstraints rom) := by
  simp [Airbender.WordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, environment, loadAssignment, row]
  repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) | try decide
  all_goals
    simp only [Lookup.Contains, fixed3, Table.toRaw, romSeparatorTable,
      romWordTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
      Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
      loadAssignment, row]
    solve
    | refine ⟨⟨64, by decide⟩, ?_⟩; norm_num [romSeparatorRow]
    | refine ⟨⟨4, by decide⟩, ?_⟩; norm_num [WordROM.row, WordROM.word, rom]

private theorem accepted : Accepted trace := by
  constructor
  · intro actual member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact load_satisfies
    · exact satisfies true false false rfl
  · intro actual member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · change [storeRow.start, loadRow.finish, storeRow.finish].Perm
      [loadRow.finish, loadRow.start, storeRow.start]
    have middle : storeRow.finish = loadRow.start := rfl
    rw [middle]
    exact @List.perm_append_comm (Airbender.PCState.State mersenne31Modulus)
      [storeRow.start] [loadRow.finish, loadRow.start]
  · decide

private def attributes : SailRV32.PMA :=
  { (default : SailRV32.PMA) with readable := true, writable := true, executable := true }

private def before : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    regs := ((Std.ExtDHashMap.emptyWithCapacity :
      Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (4194320 : BitVec 32) |>.insert .x2 (123 : BitVec 32)
      |>.insert .x3 (0 : BitVec 32) |>.insert .PC (0 : BitVec 32)
      |>.insert .mstatus 0 |>.insert .cur_privilege .Machine |>.insert .misa 0x40000100
      |>.insert .senvcfg 0 |>.insert .menvcfg 0x10
      |>.insert .pmpcfg_n (Vector.replicate 64 0)
      |>.insert .pmpaddr_n (Vector.replicate 64 0)
      |>.insert .pma_regions [Reference.RiscV.Sail.rv32Region attributes]
      |>.insert .mhartid 7 |>.insert .htif_tohost_base none)
    mem := (Std.ExtHashMap.emptyWithCapacity
      |>.insert 4194320 (0 : BitVec 8) |>.insert 4194321 0 |>.insert 4194322 0 |>.insert 4194323 0
      |>.insert 0 0x23 |>.insert 1 0xa0 |>.insert 2 0x20 |>.insert 3 0
      |>.insert 4 0x83 |>.insert 5 0xa1 |>.insert 6 0 |>.insert 7 0) }
private def cells : List Cell := [.register 1, .register 2, .ram 4194320, .register 3]

private theorem inputs : ImageBoundary trace before cells := by
  have source : (Cell.register 1).read before = .ok (4194320 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have operand : (Cell.register 2).read before = .ok (123 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have target : (Cell.register 3).read before = .ok (0 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have memory : (Cell.ram 4194320).read before = .ok (0 : BitVec 32) before := by
    simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
      EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
      EStateM.get, EStateM.pure, before, Std.ExtHashMap.getElem_insert]
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) before = .ok (0 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  constructor
  · decide
  · simp only [cells, initialImage, List.mapM_cons, List.mapM_nil, source, operand, memory, target]
    rfl
  · rw [initialState, pc]; rfl

private def storeEntry : ProgramEntry WordMemoryFamily :=
  ⟨0, 0x0020a023, .STORE (0, .Regidx 2, .Regidx 1, 4),
    ⟨.wordMemory, 1, 2, 0, ⟨0, 0⟩, 1, 2⟩⟩
private def loadEntry : ProgramEntry WordMemoryFamily :=
  ⟨4, 0x0000a183, .LOAD (0, .Regidx 1, .Regidx 3, false, 4),
    ⟨.wordMemory, 1, 0, 3, ⟨0, 0⟩, 0, 2⟩⟩
private def setup : Airbender.WordMemory.DecoderSetup := ⟨[storeEntry, loadEntry], 2⟩

private theorem decoded : Airbender.WordMemory.Decoded trace setup := by
  intro actual member
  simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨⟨1, by decide⟩, by decide⟩
  · exact ⟨⟨0, by decide⟩, by decide⟩

set_option maxRecDepth 32768 in
theorem public_setup_built : Airbender.WordMemory.decoderSetupImage before 2 2 = some setup := by
  have storeBytes : (Cell.ram 0).read before = .ok storeEntry.bits before := by
    simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
      EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
      EStateM.get, EStateM.pure, before, storeEntry, Std.ExtHashMap.getElem_insert]
  have loadBytes : (Cell.ram 4).read before = .ok loadEntry.bits before := by
    simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
      EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
      EStateM.get, EStateM.pure, before, loadEntry, Std.ExtHashMap.getElem_insert]
  have program : programImageWith Airbender.WordMemory.decoderFields before [0, 4] =
      some [storeEntry, loadEntry] := by
    simp only [programImageWith, List.mapM_cons, List.mapM_nil,
      programEntryWith, storeBytes, loadBytes, bind, Option.bind]
    rfl
  change (programImageWith Airbender.WordMemory.decoderFields before [0, 4]).bind
    (fun entries => some (Airbender.WordMemory.DecoderSetup.mk entries 2)) = some setup
  rw [program]; rfl

private theorem aligned : ∀ cell ∈ cells, cell.Aligned := by
  intro cell member
  simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> simp [Cell.Aligned]

private theorem architectural : ∀ cell ∈ cells,
    Airbender.WordMemory.architecturalAddress cell.addressCode = true := by
  intro cell present
  simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  · exact Airbender.WordMemory.Proofs.architectural_register _
  · exact Airbender.WordMemory.Proofs.architectural_register _
  · rw [Airbender.WordMemory.Proofs.architectural_ram]; decide
  · exact Airbender.WordMemory.Proofs.architectural_register _

private theorem projected_of_history {events : List MemoryAccess}
    {start finish : Reference.RiscV.Sail.State} (history : SailHistory cells events start finish) :
    SailHistory cells (events.filter fun event => Airbender.WordMemory.architecturalAddress event.2.1)
      start finish := by
  have selected : (events.filter fun event => Airbender.WordMemory.architecturalAddress event.2.1) = events := by
    apply List.filter_eq_self.mpr
    intro event present
    obtain ⟨cell, member, address⟩ := Trace.Proofs.history_address_member history present
    rw [← address]
    exact architectural cell member
  exact selected.symm ▸ history

/-- Reversed native rows derive the intermediate store state and the later load
    from that state. No intermediate state/read or final-value premise is given. -/
theorem dependent_store_load : ∃ middle after,
    Reference.Sail.run ((Cell.ram 4194320).write 123) before = .ok () middle ∧
    (Cell.ram 4194320).read middle = .ok (123 : BitVec 32) middle ∧
    Reference.Sail.run ((Cell.register 3).write 123) middle = .ok () after := by
  obtain ⟨_, rows, after, _, permutation, ordered, history, _⟩ :=
    Airbender.WordMemory.public_sail_cell_history inputs accepted decoded aligned
  have same : rows = [loadRow, storeRow] :=
    List.Perm.eq_of_pairwise' ordered (by decide) permutation
  subst rows
  change SailHistory cells ((rowEvents trace.memoryEpoch loadRow).reverse ++
    (rowEvents trace.memoryEpoch storeRow).reverse) before after at history
  obtain ⟨middle, storeHistory, loadHistory⟩ := Trace.Proofs.sail_history_append.mp history
  refine ⟨middle, after, ?_, ?_, ?_⟩
  · have written := Airbender.WordMemory.Proofs.projected_history_write (by decide) _
      (accepted.constraints storeRow (by simp [trace])) (projected_of_history storeHistory)
      (port := Airbender.WordMemory.importedConstraintsMemoryPorts[2]) rfl
      (cell := Cell.ram 4194320) (by decide)
    simpa [memoryWord, MemoryPort.writeCode, WordColumns.code, WordColumns.evaluate,
      Airbender.WordMemory.importedConstraintsMemoryPorts, storeRow, row, Nat.unpair_pair, Word.toBitVec, Word.value,
      show (123 : ZMod mersenne31Modulus).val = 123 from by decide] using written
  · have read := Airbender.WordMemory.Proofs.projected_history_read (by decide) _
      (accepted.constraints loadRow (by simp [trace])) (projected_of_history loadHistory)
      (port := Airbender.WordMemory.importedConstraintsMemoryPorts[1])
      (by change _ ∈ Airbender.WordMemory.importedConstraintsMemoryPorts
          simp [Airbender.WordMemory.importedConstraintsMemoryPorts])
      (by
        have address : Airbender.WordMemory.importedConstraintsMemoryPorts[1].address.code
            loadRow.assignment = (Cell.ram 4194320).addressCode := by decide
        rw [address, Airbender.WordMemory.Proofs.architectural_ram]
        decide)
      (cell := Cell.ram 4194320) (by decide)
    simpa [memoryWord, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate,
      Airbender.WordMemory.importedConstraintsMemoryPorts, loadRow, loadAssignment, row, Nat.unpair_pair, Word.toBitVec, Word.value,
      show (123 : ZMod mersenne31Modulus).val = 123 from by decide] using read
  · have written := Airbender.WordMemory.Proofs.projected_history_write (by decide) _
      (accepted.constraints loadRow (by simp [trace])) (projected_of_history loadHistory)
      (port := Airbender.WordMemory.importedConstraintsMemoryPorts[2]) rfl
      (cell := Cell.register 3) (by decide)
    simpa [memoryWord, MemoryPort.writeCode, WordColumns.code, WordColumns.evaluate,
      Airbender.WordMemory.importedConstraintsMemoryPorts, loadRow, loadAssignment, row, Nat.unpair_pair, Word.toBitVec, Word.value,
      show (123 : ZMod mersenne31Modulus).val = 123 from by decide] using written

private theorem projected_inputs :
    Airbender.WordMemory.ShadowImageBoundary trace before cells [] := by
  constructor
  · simpa using inputs.domain
  · exact architectural
  · simp
  · simp [Airbender.WordMemory.shadowInitialImage, Airbender.WordMemory.shadowTokens, inputs.image]
  · exact inputs.initial

private theorem code_image : wordROMImage before 2 = some trace.rom := by
  have storeRead := (Airbender.WordMemory.Proofs.setup_sources public_setup_built
    storeEntry (by simp [setup])).bytes
  have loadRead := (Airbender.WordMemory.Proofs.setup_sources public_setup_built
    loadEntry (by simp [setup])).bytes
  change (Cell.ram 0).read before = .ok storeEntry.bits before at storeRead
  change (Cell.ram 4).read before = .ok loadEntry.bits before at loadRead
  unfold wordROMImage
  rw [dif_pos (by decide)]
  simp only [readROMWords, show BitVec.ofNat 32 (4 * 0) = (0 : BitVec 32) from rfl,
    show BitVec.ofNat 32 (4 * 1) = (4 : BitVec 32) from rfl, storeRead, loadRead,
    bind, Option.bind, pure]
  rfl

/-- The public initialized theorem preserves actual code/ROM extraction while
    native matching derives a real RAM change from zero to 123. Neither the
    later bytes, decoded instruction nor terminal read is an input. -/
theorem initialized_rom_preservation : ∃ after : Reference.RiscV.Sail.State,
    (∀ key < 4194304, after.mem[key]? = before.mem[key]?) ∧
    wordROMImage after 2 = some trace.rom ∧
    (∀ entry ∈ setup.program, entry.SourceWith after Airbender.WordMemory.decoderFields) ∧
    (Cell.ram 4194320).read after = .ok (123 : BitVec 32) after ∧
    before.mem[4194320]? = some (0 : BitVec 8) ∧ after.mem[16]? = none := by
  obtain ⟨history, rows, after, complete, _, _, matched, bytes, images, sources⟩ :=
    Airbender.WordMemory.public_projected_rom_preservation projected_inputs accepted decoded aligned
  obtain ⟨cell, _, address, read⟩ := Trace.Proofs.terminal_sail_reads (by decide) accepted
    (Airbender.WordMemory.Proofs.shadow_clock_boundary (by decide) projected_inputs)
    inputs.image inputs.domain complete matched (ramToken 9 123) (by simp [trace])
  have same : cell = Cell.ram 4194320 := Trace.Proofs.cell_address_injective address
  subst cell
  refine ⟨after, bytes, images code_image, sources public_setup_built (by decide), ?_, ?_, ?_⟩
  · simpa [memoryWord, ramToken, Nat.unpair_pair, Word.toBitVec, Word.value] using read
  · simp [before, Std.ExtHashMap.getElem_insert]
  · rw [bytes 16 (by decide)]; simp [before]

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
  · simp [before]

/-- The same reversed native SW/LW rows now traverse original Sail virtual
    memory, permissions and platform helpers. Matching derives the intermediate
    state/read; native/public construction derives source and address inputs. -/
theorem dependent_virtual_store_load [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] :
    ∃ middle after : Reference.RiscV.Sail.State,
      Reference.Sail.run (SailRV32.Functions.vmem_write (.Regidx 1) 0 4 123
        (.Store .Data) false false false) before = .ok (.Ok true) middle ∧
      Reference.Sail.run (SailRV32.Functions.vmem_read (.Regidx 1) 0 4
        (.Load .Data) false false false) middle = .ok (.Ok (123 : BitVec 32)) middle ∧
      Reference.Sail.run ((Cell.register 3).write 123) middle = .ok () after ∧
      Reference.RiscV.Sail.FlatMemoryConfiguration middle ∧
      Reference.RiscV.Sail.FlatMemoryConfiguration after := by
  obtain ⟨_, rows, after, _, permutation, ordered, history, _, finalConfig⟩ :=
    Airbender.WordMemory.public_projected_platform_configuration projected_inputs
      accepted decoded aligned configuration
  have same : rows = [loadRow, storeRow] :=
    List.Perm.eq_of_pairwise' ordered (by decide) permutation
  subst rows
  change SailHistory cells
    (((rowEvents trace.memoryEpoch loadRow).reverse ++
      (rowEvents trace.memoryEpoch storeRow).reverse).filter
        fun event => Airbender.WordMemory.architecturalAddress event.2.1) before after at history
  rw [List.filter_append] at history
  obtain ⟨middle, storeHistory, loadHistory⟩ := Trace.Proofs.sail_history_append.mp history
  have middleConfig := Trace.Proofs.sail_history_configuration storeHistory configuration
  have effects := Airbender.WordMemory.Proofs.projected_native_effects projected_inputs
    public_setup_built accepted decoded
  have storeAddress := (effects storeRow (by simp [trace])).1
  have loadAddress := (effects loadRow (by simp [trace])).1
  have store := Airbender.WordMemory.Proofs.projected_virtual_ram_write (by decide) _
    (satisfies true false false rfl) (by rfl) storeAddress
    (entry := storeEntry) (by decide) configuration
    (by unfold Reference.RiscV.Sail.OrdinaryWordAddress; decide) storeHistory
  have load := Airbender.WordMemory.Proofs.projected_virtual_ram_read (by decide) _
    load_satisfies (by rfl) (by decide) loadAddress
    (entry := loadEntry) (by decide) middleConfig
    (by unfold Reference.RiscV.Sail.OrdinaryWordAddress; decide) loadHistory
  refine ⟨middle, after, ?_, ?_, ?_, middleConfig, finalConfig⟩
  · simpa [storeEntry, Airbender.WordMemory.immediateWord, row, Word.toBitVec, Word.value,
      show (123 : ZMod mersenne31Modulus).val = 123 from by decide] using store
  · simpa [loadEntry, Airbender.WordMemory.immediateWord, loadAssignment, row, Word.toBitVec, Word.value,
      show (123 : ZMod mersenne31Modulus).val = 123 from by decide] using load
  · have written := Airbender.WordMemory.Proofs.projected_history_write (by decide) _
      load_satisfies loadHistory (port := Airbender.WordMemory.importedConstraintsMemoryPorts[2])
      rfl (cell := Cell.register 3) (by decide)
    simpa [memoryWord, MemoryPort.writeCode, WordColumns.code, WordColumns.evaluate,
      Airbender.WordMemory.importedConstraintsMemoryPorts, loadRow, loadAssignment, row, Nat.unpair_pair,
      Word.toBitVec, Word.value, show (123 : ZMod mersenne31Modulus).val = 123 from by decide] using written

end Tests.WordMemorySailHistory
