import Airbender.Review.Trace.Families.WordMemory.Theorems
import Airbender.Review.Trace.Families.WordMemory.ROMImage
import Airbender.Review.Trace.Families.WordMemory.CodeHistory
import Airbender.Review.Trace.Families.WordMemory.Projection
import Airbender.Review.Trace.Families.WordMemory.Inputs
import Airbender.Proofs.Trace.Families.WordMemory.ProjectedPorts

namespace Tests.WordMemoryROMTransport
open Airbender Verification Arithmetic Trace

private def rom (discard : Bool) : WordROM :=
  ⟨[if discard then 0x0000a003 else 0x0000a183, 0, 0, 0, 0xc0001073], by simp⟩

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
      (Airbender.WordMemory.importedConstraints (rom discard)) := by
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
        decide

private def nativeRow (store inROM discard : Bool) : Row mersenne31Modulus WordMemoryFamily :=
  ⟨.wordMemory, row store inROM discard⟩


private def destination (discard : Bool) : Cell := .register (if discard then 0 else 3)
private def cells (discard : Bool) : List Cell := [.register 1, destination discard]
private def seeds : List Airbender.WordMemory.ShadowSeed := [(16, 123)]

private def trace (discard : Bool) : Data mersenne31Modulus WordMemoryFamily where
  rows := [nativeRow false true discard]
  rom := rom discard
  initial := (nativeRow false true discard).start
  terminal := (nativeRow false true discard).finish
  initialMemory := [(Cell.register 1).initialToken 16, (destination discard).initialToken 0,
    (Cell.ram 16).initialToken 123]
  terminalMemory := (nativeRow false true discard).writes

private theorem accepted (discard : Bool) : Accepted (trace discard) := by
  constructor
  · intro actual member
    have same : actual = nativeRow false true discard := by simpa [trace] using member
    subst actual
    exact satisfies false true discard rfl
  · intro actual member
    have same : actual = nativeRow false true discard := by simpa [trace] using member
    subst actual
    rfl
  · change [(nativeRow false true discard).start, (nativeRow false true discard).finish].Perm
      [(nativeRow false true discard).finish, (nativeRow false true discard).start]
    exact List.Perm.swap _ _ []
  · have initial : (trace discard).initialMemory.Perm (nativeRow false true discard).reads := by
      cases discard <;> decide
    change ((trace discard).initialMemory ++ (nativeRow false true discard).writes).Perm
      ((nativeRow false true discard).writes ++ (nativeRow false true discard).reads)
    exact (initial.append_right _).trans List.perm_append_comm

-- Architectural bytes are real public ROM data. Native shadow value 123 stays
-- independently initialized and matched; it is not the loaded ROM word.
private def attributes : SailRV32.PMA :=
  { (default : SailRV32.PMA) with readable := true, writable := true, executable := true }

private def before (discard : Bool) : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    regs := ((Std.ExtDHashMap.emptyWithCapacity :
      Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType) |>.insert .x1 (16 : BitVec 32)
      |>.insert .x3 (0 : BitVec 32) |>.insert .PC (0 : BitVec 32)
      |>.insert .mstatus 0 |>.insert .cur_privilege .Machine |>.insert .misa 0x40000100
      |>.insert .senvcfg 0 |>.insert .menvcfg 0x10
      |>.insert .pmpcfg_n (Vector.replicate 64 0)
      |>.insert .pmpaddr_n (Vector.replicate 64 0)
      |>.insert .pma_regions [Reference.RiscV.Sail.rv32Region attributes]
      |>.insert .mhartid 7 |>.insert .htif_tohost_base none)
    mem := (Std.ExtHashMap.emptyWithCapacity
      |>.insert 0 (if discard then (0x03 : BitVec 8) else 0x83)
      |>.insert 1 (if discard then 0xa0 else 0xa1)
      |>.insert 2 0 |>.insert 3 0
      |>.insert 4 0 |>.insert 5 0 |>.insert 6 0 |>.insert 7 0
      |>.insert 8 0 |>.insert 9 0 |>.insert 10 0 |>.insert 11 0
      |>.insert 12 0 |>.insert 13 0 |>.insert 14 0 |>.insert 15 0
      |>.insert 16 0x73 |>.insert 17 0x10 |>.insert 18 0 |>.insert 19 0xc0) }

private theorem inputs (discard : Bool) :
    Airbender.WordMemory.ShadowImageBoundary (trace discard) (before discard) (cells discard) seeds := by
  have source : (Cell.register 1).read (before discard) = .ok (16 : BitVec 32) (before discard) := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have target : (destination discard).read (before discard) = .ok (0 : BitVec 32) (before discard) := by
    cases discard
    · apply Reference.RiscV.Sail.read_register
      simp [before, Std.ExtDHashMap.get?_insert]
    · rfl
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) (before discard) =
      .ok (0 : BitVec 32) (before discard) := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  constructor
  · cases discard <;> decide
  · intro cell member
    rcases List.mem_cons.mp member with rfl | member
    · exact Airbender.WordMemory.Proofs.architectural_register _
    · have same : cell = destination discard := by simpa [cells] using member
      subst cell
      exact Airbender.WordMemory.Proofs.architectural_register _
  · intro seed member
    have same : seed = (16, 123) := by simpa [seeds] using member
    subst seed
    decide
  · simp only [Airbender.WordMemory.shadowInitialImage, cells, initialImage,
      List.mapM_cons, List.mapM_nil, source, target]
    rfl
  · rw [initialState, pc]
    rfl

private def entry (discard : Bool) : ProgramEntry WordMemoryFamily :=
  ⟨0, (if discard then 0x0000a003 else 0x0000a183),
    .LOAD (0, .Regidx 1, .Regidx (if discard then 0 else 3), false, 4),
    ⟨.wordMemory, 1, 0, (if discard then 0 else 3), ⟨0, 0⟩, 0, 2⟩⟩
private def setup (discard : Bool) : Airbender.WordMemory.DecoderSetup := ⟨[entry discard], 1⟩

private theorem decoded (discard : Bool) : Airbender.WordMemory.Decoded (trace discard) (setup discard) := by
  intro actual member
  have same : actual = nativeRow false true discard := by simpa [trace] using member
  subst actual
  change ∃ i : Fin 2, (nativeRow false true discard).decoderQuery = (setup discard).row i
  refine ⟨⟨0, by decide⟩, ?_⟩
  cases discard <;> decide

set_option maxRecDepth 32768 in
theorem public_decoder_built (discard : Bool) :
    Airbender.WordMemory.decoderSetupImage (before discard) 1 1 = some (setup discard) := by
  have bytes : (Cell.ram 0).read (before discard) = .ok (entry discard).bits (before discard) := by
    cases discard <;>
      simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
        EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
        EStateM.get, EStateM.pure, before, entry, Std.ExtHashMap.getElem_insert]
  have program : programImageWith Airbender.WordMemory.decoderFields
      (before discard) [0] = some [entry discard] := by
    simp only [programImageWith, List.mapM_cons, List.mapM_nil,
      programEntryWith, bytes, bind, Option.bind]
    cases discard <;> rfl
  change (programImageWith Airbender.WordMemory.decoderFields (before discard) [0]).bind
    (fun entries => some (Airbender.WordMemory.DecoderSetup.mk entries 1)) = _
  rw [program]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem configuration (discard : Bool) : Reference.RiscV.Sail.FlatMemoryConfiguration (before discard) := by
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


private theorem aligned (discard : Bool) : ∀ cell ∈ cells discard, cell.Aligned := by
  intro cell member
  simp [cells] at member
  rcases member with rfl | rfl <;> trivial

/-- Actual bytes construct the same native ROM table, including its retained
    UNIMP tail. Its shadow seed value remains a separate native input. -/
theorem public_rom_built (discard : Bool) :
    wordROMImage (before discard) 5 = some (rom discard) := by
  have bytes (i : Fin 5) :
      (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read (before discard) =
        .ok ((rom discard).word i.val) (before discard) := by
    fin_cases i <;> cases discard <;>
      simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
        EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
        EStateM.get, EStateM.pure, before, rom, WordROM.word, Std.ExtHashMap.getElem_insert]
  have b0 := bytes ⟨0, by decide⟩
  have b1 := bytes ⟨1, by decide⟩
  have b2 := bytes ⟨2, by decide⟩
  have b3 := bytes ⟨3, by decide⟩
  have b4 := bytes ⟨4, by decide⟩
  unfold wordROMImage
  rw [dif_pos (by decide)]
  simp only [readROMWords, b0, b1, b2, b3, b4, bind, Option.bind, pure]
  cases discard <;> rfl

/-- The accepted native shadow read is independent of the actual public ROM
    bytes at the same address; original LW must use the latter. -/
theorem shadow_value_differs (discard : Bool) :
    (Word.mk (row false true discard 30).val (row false true discard 31).val).toBitVec = 123 ∧
    (Cell.ram 16).read (before discard) = .ok (0xc0001073 : BitVec 32) (before discard) ∧
    (123 : BitVec 32) ≠ 0xc0001073 := by
  have read := Airbender.WordMemory.public_rom_prefix_read (public_rom_built discard)
    (satisfies false true discard rfl) (by cases discard <;> decide) (by cases discard <;> decide)
  refine ⟨?_, ?_, by decide⟩
  · cases discard <;> decide
  · simpa [Airbender.WordMemory.addressWord, row, Word.toBitVec, Word.value, limbBase,
      show (16 : ZMod mersenne31Modulus).val = 16 from by decide,
      show (4211 : ZMod mersenne31Modulus).val = 4211 from by decide,
      show (49152 : ZMod mersenne31Modulus).val = 49152 from by decide] using read

/-- Native acceptance and public constructors derive an actual ROM virtual
    load, original LW clause and actual masked write for ordinary and x0 loads.
    The same history retains its distinct shadow seed and every refresh. -/
theorem initialized_virtual_rom_load [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (discard : Bool) :
    ∃ (history : TimestampSortedMemoryAccessList) (after : Reference.RiscV.Sail.State),
      MemoryHistory (trace discard) history ∧
      SailStateMatches (cells discard) history after ∧
      Reference.Sail.run (SailRV32.Functions.vmem_read (.Regidx 1) 0 4
        (.Load .Data) false false false) (before discard) =
        .ok (.Ok (0xc0001073 : BitVec 32)) (before discard) ∧
      Reference.Sail.run ((destination discard).write (if discard then 0 else 0xc0001073))
        (before discard) = .ok () after ∧
      Reference.Sail.run (SailRV32.Functions.execute_LOAD 0 (.Regidx 1)
        (.Regidx (if discard then 0 else 3)) false 4) (before discard) =
        .ok SailRV32.Functions.RETIRE_SUCCESS after ∧
      Reference.Sail.run (Reference.RiscV.Sail.normalStep
        (SailRV32.Functions.execute_LOAD 0 (.Regidx 1) (.Regidx (if discard then 0 else 3)) false 4))
        (before discard) = .ok SailRV32.Functions.RETIRE_SUCCESS
          (Trace.retiredState after 4) := by
  obtain ⟨history, rows, after, complete, permutation, _, actual, matched⟩ :=
    Airbender.WordMemory.public_projected_sail_history (inputs discard) (accepted discard)
      (decoded discard) (aligned discard)
  have same : rows = [nativeRow false true discard] := List.perm_singleton.mp permutation
  subst rows
  have current : SailHistory (cells discard)
      ((rowEvents (trace discard).memoryEpoch (nativeRow false true discard)).reverse.filter
        fun event => Airbender.WordMemory.architecturalAddress event.2.1) (before discard) after := by
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using actual
  obtain ⟨selected, present, query, read⟩ := Airbender.WordMemory.Proofs.initialized_virtual_rom_read
    (inputs discard) (public_decoder_built discard) (public_rom_built discard)
    (configuration discard) (accepted discard) (decoded discard)
    (by change nativeRow false true discard ∈ (trace discard).rows; simp [trace])
    (SailHistory.nil (before discard)) current (by cases discard <;> decide) (by cases discard <;> decide)
  have equal : selected = entry discard := by simpa [setup] using present
  subst selected
  have written := Airbender.WordMemory.Proofs.projected_history_write (by decide) _
    (satisfies false true discard rfl) current
    (port := Airbender.WordMemory.importedConstraintsMemoryPorts[2]) rfl
    (cell := destination discard) (by cases discard <;> decide)
  have fields := (Airbender.WordMemory.Proofs.setup_sources (public_decoder_built discard)
    (entry discard) (by simp [setup])).fields
  have address := (Airbender.WordMemory.Proofs.projected_native_effects (inputs discard)
    (public_decoder_built discard) (accepted discard) (decoded discard)
    (nativeRow false true discard) (by simp [trace])).1
  have execution := Airbender.WordMemory.Proofs.projected_rom_load_execution (by decide) _
    (satisfies false true discard rfl) address fields query
    (imm := 0) (rs1 := 1) (rd := if discard then 0 else 3) rfl
    (configuration discard) (public_rom_built discard)
    (by cases discard <;> decide) (by cases discard <;> decide) current
  obtain ⟨clause, chosen, normal⟩ := Airbender.WordMemory.Proofs.initialized_instruction_retirement
    (inputs discard) (public_decoder_built discard) (accepted discard) (decoded discard)
    (w := row false true discard) (by change nativeRow false true discard ∈ (trace discard).rows; simp [trace])
    fields query (configuration discard) (public_rom_built discard)
    (by intro ram; exact ((by cases discard <;> decide : ¬ 64 ≤ (row false true discard 20).val) ram).elim)
    (by intro _; cases discard <;> decide) current
  change some (SailRV32.Functions.execute_LOAD 0 (.Regidx 1) (.Regidx (if discard then 0 else 3)) false 4) = some clause at chosen
  rw [← Option.some.inj chosen] at normal
  have initialPC : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) (before discard) =
      .ok (0 : BitVec 32) (before discard) := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have incoming : (Word.mk (row false true discard 0).val (row false true discard 1).val).toBitVec = 0 := by
    cases discard <;> decide
  have outgoing : (Word.mk (row false true discard 13).val (row false true discard 14).val).toBitVec = 4 := by
    cases discard <;> decide
  rw [incoming, outgoing] at normal
  rw [Trace.Proofs.normal_step_rebased initialPC] at normal
  refine ⟨history, after, complete, matched, ?_, ?_, execution, normal⟩
  · simpa [entry, Airbender.WordMemory.immediateWord, row, Word.toBitVec, Word.value, limbBase,
      show (4211 : ZMod mersenne31Modulus).val = 4211 from by decide,
      show (49152 : ZMod mersenne31Modulus).val = 49152 from by decide] using read
  · cases discard <;>
      simpa [memoryWord, MemoryPort.writeCode, WordColumns.code, WordColumns.evaluate,
        Airbender.WordMemory.importedConstraintsMemoryPorts, nativeRow, row, Nat.unpair_pair,
        Word.toBitVec, Word.value, limbBase, show (4211 : ZMod mersenne31Modulus).val = 4211 from by decide,
        show (49152 : ZMod mersenne31Modulus).val = 49152 from by decide] using written

/-- Ordinary and x0 ROM loads satisfy the complete fetched/decoded trace claim.
    Native shadow 123 stays independent of the actual ROM word 0xc0001073. -/
theorem initialized_fetched_execution [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (discard : Bool) :
    Airbender.WordMemory.Realizes (setup discard).program (trace discard) (before discard) (cells discard) := by
  apply Airbender.WordMemory.public_sail_execution (inputs discard) (public_decoder_built discard)
    (accepted discard) (decoded discard) (aligned discard) (configuration discard)
    (public_rom_built discard) (by decide)
  · intro address member
    simp [cells, destination] at member
  · intro seed member
    have same : seed = ((16, 123) : Airbender.WordMemory.ShadowSeed) := by simpa [seeds] using member
    subst seed
    decide

end Tests.WordMemoryROMTransport
